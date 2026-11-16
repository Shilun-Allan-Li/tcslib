/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedStepChoices
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SliceReduction
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedLaw

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One uniform negligible bound for all selected neighboring hybrids

The advice family simultaneously ranges over all inputs, actual selected arguments and
baseline tapes, with an empty option for degenerate circuits. One reconstruction machine
and the proved polynomial advice bound turn joint slice security into a uniform bound.

## Main definitions

None.

## Main results

* `filled_negligible`: a uniform nonnegative negligible bound with fixed baseline tapes.
* `selected_negligible`: the bound for every actual uniform-tape selected substep.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (the inactive-key hybrid, fixing all other coins).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Data

variable {I : ℕ → Type} [∀ n, Fintype (I n)] {inputs : ℕ → ℕ}
  (C : ∀ n, DAGCircuit (inputs n)) (S A B O R : PolyExpr)
  (seed : ∀ n, List Bool →
    GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : ∀ n, I n → ℕ → Bool) (output : ∀ n, Fin (O.eval n) → ℕ)
  (bobWord aliceWord : ∀ n, I n → List Bool)
  (hSize : ∀ n, (C n).size ≤ S.eval n) (hfanin : ∀ n, (C n).IsFaninTwo)
  (hEval : ∀ n z (i : Fin (C n).gates.length),
    gateOut ((C n).gates[i]) (RelabelGarbling.argValues (C n) (v n z) i) =
      v n z (inputs n + i))
  (hsink : ∀ n j g, g ∈ (C n).gates → output n j ∉ g.args)
  (hBob : ∀ n z, (bobWord n z).length ≤ B.eval n)
  (hAlice : ∀ n z, (aliceWord n z).length ≤ R.eval n)
  {L : PolyExpr} {L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool) (hE₂ : PolyTimeComputable E₂)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))
  (hL : ∀ n, 7 * n + 2 ≤ L.eval n) (hSecure : SliceMultiMessageSecure G)

include hSize hfanin hEval hsink hBob hAlice hE₂ hG hGE₁ hGE₂ hL hSecure in
/-- Joint slice security gives one nonnegative negligible bound for every input, actual
selected argument and fixed baseline tape, between the two neighboring samples after
fresh selected-key/nonce fill. The bound is uniform over all these choices.
[PS10, Theorem 163.7]
`∃ μ : ℕ → ℝ, Negligible μ ∧ (∀ n, 0 ≤ μ n) ∧ ∀ n (z : I n) (b : SelectedStepChoices.Selection (C
n)) (t : SelectedStepChoices.Tape S n), distAdv (fun r : (Fin n → Bool) × (Fin
((SelectedAdviceBounds.slotBudget S).eval n + 1) → Fin n → Bool) => GateHybridMessage.sample
(nestedSpecial E₁ E₂ n) (C n) (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n)) (seed n
(List.ofFn t)) (SelectedStepChoices.wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) r.1
r.2) (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true) (bobWord n z) []
(aliceWord n z) (2 * b.1.val + b.2.val)) (fun r : (Fin n → Bool) × (Fin
((SelectedAdviceBounds.slotBudget S).eval n + 1) → Fin n → Bool) => GateHybridMessage.sample
(nestedSpecial E₁ E₂ n) (C n) (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n)) (seed n
(List.ofFn t)) (SelectedStepChoices.wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) r.1
r.2) (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true) (bobWord n z) []
(aliceWord n z) (2 * b.1.val + b.2.val + 1)) (D.distinguisherL n) ≤ μ n`.

**Proof sketch.** Apply the existing finite-advice reduction to the padded choice family,
using the complete advice polynomial and the total reconstruction machine. The empty
choice makes this family nonempty and its nonnegative advantage forces the resulting bound
to be nonnegative at every parameter. At each real choice, the two pointwise reconstruction
readers replace the reconstructed slice experiments by the actual filled-seed hybrid samples.
The advice is identical on both sides and independent of the sampled key and nonces. -/
theorem filled_negligible (D : NUPPT) :
    ∃ μ : ℕ → ℝ, Negligible μ ∧ (∀ n, 0 ≤ μ n) ∧
      ∀ n (z : I n) (b : SelectedStepChoices.Selection (C n))
        (t : SelectedStepChoices.Tape S n),
      distAdv
        (fun r : (Fin n → Bool) ×
            (Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1) → Fin n → Bool) =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n)
            (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
              (SelectedStepChoices.wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n)
              r.1 r.2)
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) (2 * b.1.val + b.2.val))
        (fun r : (Fin n → Bool) ×
            (Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1) → Fin n → Bool) =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n)
            (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
              (SelectedStepChoices.wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n)
              r.1 r.2)
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) (2 * b.1.val + b.2.val + 1))
        (D.distinguisherL n) ≤ μ n := by
  classical
  let Q := SelectedAdviceBounds.slotBudget S
  let budget := SelectedAdviceBounds.sampleBudget S A B O R
  letI : ∀ n, Fintype (SelectedStepChoices.Choice I C S n) := fun _ => Fintype.ofFinite _
  letI : ∀ n, Nonempty (SelectedStepChoices.Choice I C S n) :=
    fun _ => ⟨(none, fun _ => false)⟩
  -- One worst finite choice fixes the input, step and all baseline coins.
  obtain ⟨μ, hμ, hBound⟩ := SliceReduction.reconstruction_negligible hSecure D Q budget
    (SelectedStepChoices.advice C S A B O seed v output bobWord aliceWord E₁ E₂)
    (SelectedStepChoices.advice_budget C S A B O seed v output bobWord aliceWord E₁ E₂
      R hSize hfanin hBob hAlice)
    (SliceReconstruction.rebuild_poly hE₂)
    (SelectedStepChoices.offset C S seed) (SelectedStepChoices.len C S seed)
    (SelectedStepChoices.fits C S seed L hL)
    (SelectedStepChoices.message C S seed v E₁ false)
    (SelectedStepChoices.message C S seed v E₁ true)
  have hNonneg (n : ℕ) : 0 ≤ μ n := by
    have hb := hBound n ((none, fun _ => false) : SelectedStepChoices.Choice I C S n)
    rw [distAdv_def] at hb
    exact (abs_nonneg _).trans hb
  refine ⟨μ, hμ, hNonneg, ?_⟩
  intro n z b t
  -- Both real endpoints use the same advice, offsets and lengths.
  have hPoint (side : Bool) :
      (fun r : (Fin n → Bool) × (Fin (Q.eval n + 1) → Fin n → Bool) =>
        SliceReconstruction.rebuild E₂ (pairEncode (List.replicate n true) (pairEncode
          (sliceMultiEncDist G n (Q.eval n)
            (SelectedStepChoices.offset C S seed n (some (z, b), t))
            (SelectedStepChoices.len C S seed n (some (z, b), t))
            (SelectedStepChoices.message C S seed v E₁ side n (some (z, b), t)) r)
          (SelectedStepChoices.advice C S A B O seed v output bobWord aliceWord E₁ E₂
            n (some (z, b), t))))) =
      (fun r : (Fin n → Bool) × (Fin (Q.eval n + 1) → Fin n → Bool) =>
        GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n)
          (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n)) (seed n (List.ofFn t))
            (SelectedStepChoices.wire (C n) b) (Q.eval n) r.1 r.2)
          (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
          (bobWord n z) [] (aliceWord n z) (2 * b.1.val + b.2.val + side.toNat)) := by
    funext r
    exact SelectedStepChoices.rebuild_some C S A B O seed v output bobWord aliceWord E₁ E₂
      G G₁ G₂ hG hGE₁ hGE₂ hSize hfanin hEval hsink n z b t r.1 r.2 side
  have hb := hBound n (some (z, b), t)
  rw [hPoint false, hPoint true] at hb
  simpa only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] using hb

variable
  (hK : ∀ n q (w : Fin (C n).size) (b : Bool) (t : Fin n),
    (seed n q).1 w b t = q.getD ((b.toNat * S.eval n + w.val) * n + t.val) false)
  (hR₀ : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool) (t : Fin n),
    ((seed n q).2.1 i a).1 t = q.getD (2 * S.eval n * n + (4 * i.val +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t.val) false)
  (hR₁ : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool) (t : Fin n),
    ((seed n q).2.1 i a).2 t = q.getD (2 * S.eval n * n + (4 * i.val +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t.val) false)
  (hP : ∀ n q (i : Fin (C n).gates.length)
      (a : Fin (C n).gates[i.val].args.length → Bool)
      (t : Fin (C n).gates[i.val].args.length),
    (seed n q).2.2 i a t = xor (a t)
      (q.getD (10 * S.eval n * n + 2 * i.val + t.val) false))

include hSize hfanin hEval hsink hBob hAlice hE₂ hG hGE₁ hGE₂ hL hSecure
  hK hR₀ hR₁ hP in
/-- For the actual addressed uniform tape distribution, one nonnegative negligible function
bounds the advantage of every neighboring hybrid substep with an actual selected argument,
uniformly in the input, gate and argument. Empty circuits require no selected vertex.
[PS10, Theorem 163.7]
`∃ μ : ℕ → ℝ, Negligible μ ∧ (∀ n, 0 ≤ μ n) ∧ ∀ n (z : I n) (i : Fin (C n).gates.length) (p : Fin (C
n).gates[i.val].args.length), distAdv (fun t : SelectedStepChoices.Tape S n =>
GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t)) (A.eval n) (B.eval n)
(O.eval n) (output n) (v n z) (List.replicate n true) (bobWord n z) [] (aliceWord n z) (2 * i.val +
p.val)) (fun t : SelectedStepChoices.Tape S n => GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C
n) (seed n (List.ofFn t)) (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n
true) (bobWord n z) [] (aliceWord n z) (2 * i.val + p.val + 1)) (D.distinguisherL n) ≤ μ n`.

**Proof sketch.** Obtain the uniform bound with each baseline tape fixed. Average that tape
using the existing fiber advantage inequality, which applies because the bound is nonnegative.
The proved actual-tape fill law then identifies each averaged filled-seed acceptance
probability with its original uniform-tape acceptance probability. Apply this law separately
to the before and after stages. All shifts and unused padded coordinates retain their actual
law; no uniformity claim about the induced permutation or distinctness of key values is used. -/
theorem selected_negligible (D : NUPPT) :
    ∃ μ : ℕ → ℝ, Negligible μ ∧ (∀ n, 0 ≤ μ n) ∧
      ∀ n (z : I n) (i : Fin (C n).gates.length) (p : Fin (C n).gates[i.val].args.length),
      distAdv
        (fun t : SelectedStepChoices.Tape S n =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t))
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) (2 * i.val + p.val))
        (fun t : SelectedStepChoices.Tape S n =>
          GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t))
            (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
            (bobWord n z) [] (aliceWord n z) (2 * i.val + p.val + 1))
        (D.distinguisherL n) ≤ μ n := by
  obtain ⟨μ, hμ, hNonneg, hBound⟩ := filled_negligible C S A B O R seed v output
    bobWord aliceWord hSize hfanin hEval hsink hBob hAlice G G₁ G₂ E₁ E₂ hE₂
    hG hGE₁ hGE₂ hL hSecure D
  refine ⟨μ, hμ, hNonneg, ?_⟩
  intro n z i p
  let b : SelectedStepChoices.Selection (C n) := ⟨i, p⟩
  let u := SelectedStepChoices.wire (C n) b
  let q := (SelectedAdviceBounds.slotBudget S).eval n
  let X := fun (stage : ℕ)
      (s : GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool))) =>
    GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n) s
      (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
      (bobWord n z) [] (aliceWord n z) stage
  -- Average only the independent baseline tape; the challenge and test coins stay separate.
  have hAvg := SliceReduction.distAdv_fibers_le
    (fun (t : SelectedStepChoices.Tape S n)
        (r : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) =>
      X (2 * i.val + p.val) (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n))
        (seed n (List.ofFn t)) u q r.1 r.2))
    (fun (t : SelectedStepChoices.Tape S n)
        (r : (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) =>
      X (2 * i.val + p.val + 1) (SelectedSeed.fill (C n) (SelectedStepChoices.rows (C n))
        (seed n (List.ofFn t)) u q r.1 r.2))
    (D.distinguisherL n) (μ n) (hNonneg n) (hBound n z b)
  have hfan := (DAGCircuit.isFaninTwo_iff (C n)).mp (hfanin n)
  have hA (j : Fin (C n).gates.length) : (C n).gates[j.val].args.length ≤ 2 :=
    hfan.2 _ (List.getElem_mem j.isLt)
  have hargs (j : Fin (C n).gates.length) : (C n).gates[j.val].args.Nodup :=
    (hfan.1 _ (List.getElem_mem j.isLt)).1
  -- The same proved fill law applies to either complete sampler endpoint.
  have hLaw (stage : ℕ) := SelectedLaw.acceptProb_fill (C n) (S.eval n) n hA (hSize n)
    (seed n) (hK n) (hR₀ n) (hR₁ n) (hP n) (SelectedStepChoices.rows (C n)) u q
    hargs (SelectedStepChoices.rows_complete (C n)) (SelectedStepChoices.rows_nodup (C n))
    (X stage) (D.distinguisherL n)
  rw [distAdv_def] at hAvg ⊢
  rw [hLaw _, hLaw _] at hAvg
  exact hAvg

end Data

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepSecurity
