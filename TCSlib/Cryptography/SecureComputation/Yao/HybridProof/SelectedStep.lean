/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedTables

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A common reconstruction for both sides of a selected gate substep

The selected argument is an actual argument of the current gate. The two neighboring
stage samplers use the same reconstruction machine, slice offsets and lengths, and fixed
before-stage advice. Only their padded slice message families vary.

## Main definitions

None.

## Main results

* `SelectedStep.plaintext_ne`: all three local stages avoid the selected inactive label.
* `SelectedStep.advice_next`: both sides use identical fixed advice.
* `SelectedStep.reconstruct`: the exact pointwise two-sided sampler contract.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (one selected inactive-key substep).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep

open Complexity Turing BoolCircuit TCSlib.Cryptography

/-- Every plaintext label in local stage `2*i0+phase`, for `phase <= 2`, differs from
`(u,true)` when gate `i0` reads `u`. This combines the three published phase readers and
uses no comparison of actual key values. [PS10, Theorem 163.7] -/
theorem plaintext_ne {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ C.gates[i₀.val].args)
    (phase : ℕ) (hphase : phase ≤ 2)
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    (m + i.val, GateHybrids.stageBit C v (2 * i₀.val + phase) i a) ≠ (u, true) := by
  have hc : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · simpa only [Nat.add_zero] using SelectedFields.stageBit_plaintext_ne_even C v i₀ u hu i a
  · exact SelectedFields.stageBit_plaintext_ne_odd C v i₀ u hu i a
  · exact SelectedFields.stageBit_plaintext_ne_next C v i₀ u hu i a

/-- Rows without the selected inactive argument have identical plaintext bits at stages
`2*i0+p.val` and `2*i0+p.val+1`. The selected position is an actual argument of a gate with
at most two arguments. [PS10, Theorem 163.7]
`GateHybrids.stageBit C v (2 * i₀.val + p.val) i a = GateHybrids.stageBit C v (2 * i₀.val +
p.val + 1) i a`.

**Proof sketch.** The actual position is zero or one. Apply the published first-substep
support reader in the first case and the second-substep support reader in the second case.
The latter uses the supplied consistent wire values. No selected wire is fabricated for
an absent argument. -/
theorem unselected_eq {m : ℕ} (C : DAGCircuit m) (v : ℕ → Bool)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (m + i))
    (i₀ : Fin C.gates.length) (hargs : C.gates[i₀.val].args.Nodup)
    (p : Fin C.gates[i₀.val].args.length) (u : ℕ) (hu : C.gates[i₀.val].args[p.val] = u)
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (hNone : GateOccurrences.selectedPosition C.gates[i.val] a u = none) :
    GateHybrids.stageBit C v (2 * i₀.val + p.val) i a =
      GateHybrids.stageBit C v (2 * i₀.val + p.val + 1) i a := by
  have hp : p.val ≤ 1 := by
    have ha := hA i₀
    simp only [Fin.getElem_fin] at ha
    have hp := p.isLt
    omega
  by_cases hzero : p.val = 0
  · simpa only [hzero, Nat.add_zero] using
      SelectedFields.stage_first_unselected C v i₀ hargs p hzero u hu i a hNone
  · have hone : p.val = 1 := by omega
    have hstage : 2 * i₀.val + 1 + 1 = 2 * i₀.val + 2 := by omega
    rw [hone, hstage]
    exact SelectedFields.stage_second_unselected C v hA hEval i₀ hargs p hone u hu i a hNone

/-- Neighboring stages for an actual selected argument have exactly the same fixed
reconstruction advice, including the complete message tail. Only their challenge messages
may differ. [PS10, Theorem 163.7]
`SelectedPlan.advice C rows s u E₁ E₂ (fun i a => keyAt C s (m + i.val) (GateHybrids.stageBit C v
(2 * i₀.val + p.val) i a)) (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s inA
outLen output v (2 * i₀.val + p.val))) privateInput aliceOutput = SelectedPlan.advice C rows s u E₁
E₂ (fun i a => keyAt C s (m + i.val) (GateHybrids.stageBit C v (2 * i₀.val + p.val + 1) i a))
(pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s inA outLen output v (2 * i₀.val +
p.val + 1))) privateInput aliceOutput`.

**Proof sketch.** The published tail reader removes the stage dependence of the retained
message tail. The common-advice reader then reduces the claim to plaintext-key equality
on unselected rows. Those rows have equal neighboring stage bits by the first/second
substep support readers, so their output keys agree. -/
theorem advice_next {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (v : ℕ → Bool) (hfanin : C.IsFaninTwo)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (m + i))
    (i₀ : Fin C.gates.length) (p : Fin C.gates[i₀.val].args.length)
    (hu : C.gates[i₀.val].args[p.val] = u.val) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (privateInput aliceOutput : List Bool) :
    SelectedPlan.advice C rows s u E₁ E₂ (fun i a =>
      keyAt C s (m + i.val) (GateHybrids.stageBit C v (2 * i₀.val + p.val) i a))
      (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s inA outLen
        output v (2 * i₀.val + p.val))) privateInput aliceOutput =
    SelectedPlan.advice C rows s u E₁ E₂ (fun i a =>
      keyAt C s (m + i.val) (GateHybrids.stageBit C v (2 * i₀.val + p.val + 1) i a))
      (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s inA outLen
        output v (2 * i₀.val + p.val + 1))) privateInput aliceOutput := by
  have hfan := (DAGCircuit.isFaninTwo_iff C).mp hfanin
  have hA (i : Fin C.gates.length) : (C.gates[i]).args.length ≤ 2 := by
    simpa only [Fin.getElem_fin] using hfan.2 _ (List.getElem_mem i.isLt)
  rw [← SelectedFields.message_tail_stage_eq (nestedSpecial E₁ E₂ n) C s inA outLen
    output v (2 * i₀.val + p.val) (2 * i₀.val + p.val + 1)]
  apply SelectedPlan.advice_congr
  intro i a hNone
  exact congrArg (keyAt C s (m + i.val))
    (unselected_eq C v hA hEval i₀ (hfan.1 _ (List.getElem_mem i₀.isLt)).1 p u.val hu
      i a hNone)

section Joint

variable {L L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hG hGE₁ hGE₂ in
/-- Both neighboring actual hybrid samples reconstruct from the same before-stage advice,
with the same slice offsets and lengths and only the side-specific challenge messages.
The equality holds for every challenge key and all padded row nonces. [PS10, Theorem 163.7]
`let before := 2 * i₀.val + p.val; let stage := before + side.toNat; let plain : (i : Fin
C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool) := fun i a => keyAt C s
(m + i.val) (GateHybrids.stageBit C v stage i a); let beta := SelectedPlan.advice C rows s u E₁ E₂
(fun i a => keyAt C s (m + i.val) (GateHybrids.stageBit C v before i a)) (pairSndD
(GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s inA outLen output v before)) (pairEncode
bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB))) aliceOutput;
SliceReconstruction.rebuild E₂ (pairEncode N (pairEncode (sliceMultiEncDist G n q
(SelectedPlan.slotOffset C rows s u q) (SelectedPlan.slotLength C rows s u q)
(SelectedPlan.slotMessage C rows s u q E₁ plain) (k, rs)) beta)) = GateHybridMessage.sample
(nestedSpecial E₁ E₂ n) C (SelectedSeed.fill C rows s u q k rs) inA inB outLen output v N bobInput
[] aliceOutput stage`.

**Proof sketch.** Fan-in two supplies distinct arguments and an actual position zero or one.
Canonical rows are complete. Since the selected argument precedes the current gate, every
plaintext label in either neighboring stage avoids its inactive label. The sink hypothesis
also excludes the selected wire from both entries of every output decoding pair. Apply the
exact filled-seed sample reconstruction on the before side. On the after side first replace
the fixed advice by the equal after-stage advice, then apply the same reconstruction reader.
All key-value collisions and zero key width are allowed. -/
theorem reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ) (v : ℕ → Bool) (hfanin : C.IsFaninTwo)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (m + i))
    (i₀ : Fin C.gates.length) (p : Fin C.gates[i₀.val].args.length)
    (hu : C.gates[i₀.val].args[p.val] = u.val)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrows : ∀ i, rows i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
    (hsink : ∀ j g, g ∈ C.gates → output j ∉ g.args)
    (N bobInput aliceOutput : List Bool)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) (side : Bool) :
    let before := 2 * i₀.val + p.val
    let stage := before + side.toNat
    let plain : (i : Fin C.gates.length) →
        (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool) :=
      fun i a => keyAt C s (m + i.val) (GateHybrids.stageBit C v stage i a)
    let beta := SelectedPlan.advice C rows s u E₁ E₂ (fun i a =>
      keyAt C s (m + i.val) (GateHybrids.stageBit C v before i a))
      (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s
        inA outLen output v before))
      (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB))) aliceOutput
    SliceReconstruction.rebuild E₂ (pairEncode N (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q)
        (SelectedPlan.slotMessage C rows s u q E₁ plain) (k, rs)) beta)) =
      GateHybridMessage.sample (nestedSpecial E₁ E₂ n) C (SelectedSeed.fill C rows s u q k rs)
        inA inB outLen output v N bobInput [] aliceOutput stage := by
  -- Recover the structural hypotheses from the public circuit reader.
  have hfan := (DAGCircuit.isFaninTwo_iff C).mp hfanin
  have hargs (i : Fin C.gates.length) : C.gates[i.val].args.Nodup :=
    (hfan.1 _ (List.getElem_mem i.isLt)).1
  have hA (i : Fin C.gates.length) : C.gates[i.val].args.length ≤ 2 :=
    hfan.2 _ (List.getElem_mem i.isLt)
  have hcomplete (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
      a ∈ rows i := by
    rw [hrows i]
    exact Finset.mem_toList.mpr (Finset.mem_univ a)
  have huMem : u.val ∈ C.gates[i₀.val].args := by
    rw [← hu]
    exact List.getElem_mem p.isLt
  -- Sink outputs exclude both decoding labels at the selected wire.
  have hOut (j : Fin outLen) : output j ≠ u.val := by
    intro h
    exact GateOccurrences.decoding_label_ne C i₀ u.val huMem output hsink j true
      (congrArg (fun w : ℕ => (w, true)) h)
  have hp : p.val ≤ 1 := by have ha := hA i₀; have hlt := p.isLt; omega
  -- The after side changes only the challenge messages, using the same advice.
  dsimp only
  cases side with
  | false =>
    simp only [Bool.toNat_false, Nat.add_zero]
    apply SelectedTables.sample_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q
      inA inB outLen output v (2 * i₀.val + p.val) N bobInput aliceOutput
      hargs hA hcomplete hcap hrows _ hOut k rs
    intro i a
    exact plaintext_ne C v i₀ u.val huMem p.val (by omega) i a
  | true =>
    simp only [Bool.toNat_true]
    rw [advice_next E₁ E₂ C rows s u v hfanin hEval i₀ p hu inA outLen output
      (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB))) aliceOutput]
    apply SelectedTables.sample_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q
      inA inB outLen output v (2 * i₀.val + p.val + 1) N bobInput aliceOutput
      hargs hA hcomplete hcap hrows _ hOut k rs
    intro i a
    simpa only [Nat.add_assoc] using
      plaintext_ne C v i₀ u.val huMem (p.val + 1) (by omega) i a

end Joint

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStep
