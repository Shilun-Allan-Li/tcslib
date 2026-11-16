/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedSeed
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fields unaffected by selected inactive-key replacement

The selected fill changes the symbolic key label `(u,true)`. False active
keys, unrelated decoding pairs and the encoded message tail therefore remain
fixed. These are reader-based consequences, with no key-value inequality or
encryption hypothesis. Stage output labels are separated from the selected
argument label by circuit acyclicity and the completed-gate rule.

## Main definitions

None.

## Main results

* `keyAt_of_label_ne`, `keyAt_false`: total key lookup outside the selected label is unchanged.
* Active answers and unrelated output decoding pairs are unchanged by selected fill.
* The message tail is independent of selected fill and the hybrid stage.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the gate-by-gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Keys

variable {inputs : ℕ} {K ρ : Type} [Inhabited K]
  (C : DAGCircuit inputs)
  (rows : (i : Fin C.gates.length) → List (Fin (C.gates[i.val]).args.length → Bool))
  (s : GarbleSeed C K (ρ × ρ)) (u : Fin C.size) (q : ℕ) (k : K)
  (rs : Fin (q + 1) → ρ)

/-- Total key lookup is unchanged at every symbolic label other than `(u,true)`,
including the default region outside the circuit. [PS10, Theorem 163.7] -/
theorem keyAt_of_label_ne (w : ℕ) (b : Bool) (h : (w, b) ≠ (u.val, true)) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w b = keyAt C s w b := by
  rw [SelectedSeed.fill_keyAt, if_neg h]

/-- False active keys are unchanged at every vertex, including default vertices.
This is a symbolic-label fact and does not require distinct key values. -/
theorem keyAt_false (w : ℕ) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w false = keyAt C s w false := by
  simp only [SelectedSeed.fill_keyAt, Prod.mk.injEq, Bool.false_eq_true, and_false, ite_false]

/-- Both key choices are unchanged at a vertex different from the selected vertex. -/
theorem keyAt_of_ne (w : ℕ) (b : Bool) (hw : w ≠ u.val) :
    keyAt C (SelectedSeed.fill C rows s u q k rs) w b = keyAt C s w b :=
  keyAt_of_label_ne C rows s u q k rs w b (fun h => hw (congrArg Prod.fst h))

/-- An output decoding pair at an unrelated vertex is unchanged, for every
prescribed result bit. No encryption assumption is needed. -/
theorem decodePair_fill (w : ℕ) (b : Bool) (hw : w ≠ u.val) :
    FakeObjects.decodePair C (SelectedSeed.fill C rows s u q k rs) w b =
      FakeObjects.decodePair C s w b := by
  rw [FakeObjects.decodePair_eq, FakeObjects.decodePair_eq,
    keyAt_of_ne C rows s u q k rs w b hw, keyAt_of_ne C rows s u q k rs w (!b) hw]

end Keys

/-- The complete false-key answer vector is unchanged by selected fill for
all starting vertices and counts, including zero key width. -/
theorem activeAnswers_fill {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (rows : (i : Fin C.gates.length) → List (Fin (C.gates[i.val]).args.length → Bool))
    (s : GarbleSeed C (Fin width → Bool) (ρ × ρ)) (u : Fin C.size) (q : ℕ)
    (k : Fin width → Bool) (rs : Fin (q + 1) → ρ) (first count : ℕ) :
    FakeObjects.activeAnswers C (SelectedSeed.fill C rows s u q k rs) first count =
      FakeObjects.activeAnswers C s first count := by
  funext t
  rw [FakeObjects.activeAnswers_eq, FakeObjects.activeAnswers_eq, keyAt_false]

/-- The encoded message tail is independent of the hybrid stage: only the
encoded table head depends on the stage. -/
theorem message_tail_stage_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage stage' : ℕ) :
    pairSndD (GateHybridMessage.message M C s inA outLen output v stage) =
      pairSndD (GateHybridMessage.message M C s inA outLen output v stage') := by
  simp only [GateHybridMessage.message_eq, pairSndD_pairEncode]

/-- The encoded message tail is unchanged by selected fill when no output
vertex is the selected argument vertex. [PS10, Theorem 163.7]

**Proof sketch.** Read the message pair and discard its table head. Every
encoded Alice input key is false and is unchanged. Each output decoding pair
is at an unrelated vertex and is unchanged. Encoding these equal component
vectors preserves the entire tail. -/
theorem message_tail_fill {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) (ρ × ρ)) (C : DAGCircuit inputs)
    (rows : (i : Fin C.gates.length) → List (Fin (C.gates[i.val]).args.length → Bool))
    (s : GarbleSeed C (Fin width → Bool) (ρ × ρ)) (u : Fin C.size) (q : ℕ)
    (k : Fin width → Bool) (rs : Fin (q + 1) → ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ)
    (hOut : ∀ j, output j ≠ u.val) :
    pairSndD (GateHybridMessage.message M C (SelectedSeed.fill C rows s u q k rs)
      inA outLen output v stage) =
      pairSndD (GateHybridMessage.message M C s inA outLen output v stage) := by
  rw [GateHybridMessage.message_eq, GateHybridMessage.message_eq,
    pairSndD_pairEncode, pairSndD_pairEncode]
  congr 1
  · apply congrArg BinArith.encWords
    apply congrArg List.ofFn
    funext w
    rw [keyAt_false]
  · apply congrArg BinArith.encWords
    apply congrArg List.ofFn
    funext j
    simp only [decodePair_fill C rows s u q k rs (output j) (v (output j)) (hOut j)]

/-- Every hybrid output-key label differs from `(u,true)` when the selected
wire precedes the current cutoff vertex. This concerns symbolic labels, not
inequality of key values. [PS10, Theorem 163.7] -/
theorem outputBit_plaintext_ne_of_lt {inputs : ℕ} (C : DAGCircuit inputs)
    (v : ℕ → Bool) (cutoff phase u : ℕ) (hu : u < inputs + cutoff)
    (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool) :
    (inputs + i.val, GateHybrids.outputBit C v cutoff phase i a) ≠ (u, true) := by
  have h := GateOccurrences.hybrid_plaintext_ne inputs cutoff u i.val hu
    (GateHybrids.outputBit C v cutoff phase i a)
  by_cases hi : i.val < cutoff
  · rw [GateHybrids.outputBit_completed C v cutoff phase i a hi]
    simpa only [if_pos hi] using h
  · simpa only [if_neg hi] using h

/-- Selecting a current gate's argument gives a different symbolic key label
from every hybrid row plaintext, at every phase. [PS10, Theorem 163.7] -/
theorem outputBit_plaintext_ne {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (phase u : ℕ) (hu : u ∈ (C.gates[i₀.val]).args)
    (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool) :
    (inputs + i.val, GateHybrids.outputBit C v i₀.val phase i a) ≠ (u, true) :=
  outputBit_plaintext_ne_of_lt C v i₀.val phase u
    (GateOccurrences.selected_wire_lt C i₀ u hu) i a

/-- At the even stage of a gate, all row plaintext labels avoid its selected
argument's inactive key label. -/
theorem stageBit_plaintext_ne_even {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ (C.gates[i₀.val]).args)
    (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool) :
    (inputs + i.val, GateHybrids.stageBit C v (2 * i₀.val) i a) ≠ (u, true) := by
  rw [GateHybrids.stageBit_even]
  exact outputBit_plaintext_ne C v i₀ 0 u hu i a

/-- At the odd stage of a gate, all row plaintext labels avoid its selected
argument's inactive key label. -/
theorem stageBit_plaintext_ne_odd {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ (C.gates[i₀.val]).args)
    (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool) :
    (inputs + i.val, GateHybrids.stageBit C v (2 * i₀.val + 1) i a) ≠ (u, true) := by
  rw [GateHybrids.stageBit_odd]
  exact outputBit_plaintext_ne C v i₀ 1 u hu i a

/-- After completing the current gate, all row plaintext labels still avoid
its selected argument's inactive key label. -/
theorem stageBit_plaintext_ne_next {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (u : ℕ) (hu : u ∈ (C.gates[i₀.val]).args)
    (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool) :
    (inputs + i.val, GateHybrids.stageBit C v (2 * i₀.val + 2) i a) ≠ (u, true) := by
  have hlt := GateOccurrences.selected_wire_lt C i₀ u hu
  have hu' : u < inputs + (i₀.val + 1) := by omega
  have hstage : 2 * i₀.val + 2 = 2 * (i₀.val + 1) := by omega
  rw [hstage, GateHybrids.stageBit_even]
  exact outputBit_plaintext_ne_of_lt C v (i₀.val + 1) 0 u hu' i a

/-- The first substep at an arity-zero gate changes no stage label. The
statement requires no selected wire because the first argument is absent. -/
theorem stage_first_of_arity_zero {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i₀ : Fin C.gates.length) (hzero : (C.gates[i₀.val]).args.length = 0) :
    GateHybrids.stageBit C v (2 * i₀.val) =
      GateHybrids.stageBit C v (2 * i₀.val + 1) := by
  rw [GateHybrids.stageBit_even, GateHybrids.stageBit_odd]
  funext i a
  apply GateHybrids.outputBit_first_unchanged
  by_cases hi : i = i₀
  · subst i
    right
    exact List.getD_eq_default (List.ofFn a) false (n := 0) (by
      simpa only [List.length_ofFn, Fin.getElem_fin, hzero] using (Nat.le_refl 0))
  · exact Or.inl (fun h => hi (Fin.ext h))

/-- The second substep at a gate of arity at most one changes no stage label
for consistent wire values. No second argument or selected wire is required.

**Proof sketch.** Other gates are unchanged by cutoff advancement. At the
current gate the padded second bit is false because the assignment has length
at most one. The existing second-substep support theorem then applies; its
all-zero case is justified by the supplied circuit-consistency equation. -/
theorem stage_second_of_arity_le_one {inputs : ℕ} (C : DAGCircuit inputs)
    (v : ℕ → Bool)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (i₀ : Fin C.gates.length) (hsmall : (C.gates[i₀.val]).args.length ≤ 1) :
    GateHybrids.stageBit C v (2 * i₀.val + 1) =
      GateHybrids.stageBit C v (2 * i₀.val + 2) := by
  have hstage : 2 * i₀.val + 2 = 2 * (i₀.val + 1) := by omega
  rw [GateHybrids.stageBit_odd, hstage, GateHybrids.stageBit_even]
  funext i a
  apply GateHybrids.outputBit_second_unchanged C v hA hEval i₀.val i a
  by_cases hi : i = i₀
  · subst i
    right; right
    exact List.getD_eq_default (List.ofFn a) false (n := 1) (by
      simpa only [List.length_ofFn, Fin.getElem_fin] using hsmall)
  · exact Or.inl (fun h => hi (Fin.ext h))

/-- Equal stage-label families give equal complete encoded messages. -/
theorem message_eq_of_stageBit_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage stage' : ℕ)
    (h : GateHybrids.stageBit C v stage = GateHybrids.stageBit C v stage') :
    GateHybridMessage.message M C s inA outLen output v stage =
      GateHybridMessage.message M C s inA outLen output v stage' := by
  rw [GateHybridMessage.message_eq, GateHybridMessage.message_eq, h]

/-- Equal stage-label families give exactly equal Bob-view samples for every
seed and prescribed Alice output. -/
theorem sample_eq_of_stageBit_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA inB outLen : ℕ)
    (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (stage stage' : ℕ)
    (h : GateHybrids.stageBit C v stage = GateHybrids.stageBit C v stage') :
    GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput stage =
      GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput stage' := by
  rw [GateHybridMessage.sample_eq, GateHybridMessage.sample_eq,
    message_eq_of_stageBit_eq M C s inA outLen output v stage stage' h]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields
