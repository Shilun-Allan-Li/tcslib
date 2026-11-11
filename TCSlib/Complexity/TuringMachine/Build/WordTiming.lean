/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time bounds for concatenating computed words

The outputs of two computations on the same input can be concatenated with a bound proportional to their separate running times and the input length. The construction uses paired storage and the timed payload-map contract.

## Main definitions

None.

## Main results

* `Turing.FinTM.exists_append_computesFunInTime` gives the additive running-time bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

namespace Turing.FinTM

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime
attribute [local irreducible] pairEncode pairDecode bufferedCompTM

/-- Two computations on the same input can have their outputs concatenated with
linear overhead in their separate time bounds and the input length.

**Proof sketch.** Duplicate the input and map the first computation over the payload.
Duplicate the resulting pair, then compute the second result from its original-input
projection. Concatenate and remove the retained input. Each call is charged at its
actual input, and the two computed words have length at most their run times. -/
theorem exists_append_computesFunInTime {F G : FinTM Bool}
    {f g : List Bool → List Bool} {A B : ℕ → ℕ}
    (hf : F.ComputesFunInTime f A) (hg : G.ComputesFunInTime g B) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => f x ++ g x)
        (fun n => c * (A n + B n + n + 1)) := by
  obtain ⟨D, a, hD⟩ := computesFunInTime_pairDup
  obtain ⟨P, hP⟩ := exists_pairMapSnd_computesInTime F
  let G' := bufferedCompTM (pairExtractTM true false) G
  obtain ⟨Q, hQ⟩ := exists_pairMapSnd_computesInTime G'
  let C := pairExtractTM true true
  let S := pairExtractTM false true
  let M := bufferedCompTM
    (bufferedCompTM (bufferedCompTM (bufferedCompTM (bufferedCompTM D P) D) Q) C) S
  refine ⟨M, 4 * a + 1500, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  let n := x.length
  let budget := A n + B n + n + 1
  let p := pairEncode x x
  let s := pairEncode x (f x)
  let q := pairEncode s s
  let r := pairEncode s (g x)
  have hf' := (computesFunInTime_iff _ _ _).1 hf x
  have hg' := (computesFunInTime_iff _ _ _).1 hg x
  have hlf : (f x).length ≤ A n := by
    rw [← ((computesInTime_iff _ _ _ _).1 hf').2]
    exact F.tm.output_length_le x _
  have hlg : (g x).length ≤ B n := by
    rw [← ((computesInTime_iff _ _ _ _).1 hg').2]
    exact G.tm.output_length_le x _
  have h₁ := (computesFunInTime_iff _ _ _).1 hD x
  have h₂ := hP x x (f x) (A n) hf'
  have h₃ := (computesFunInTime_iff _ _ _).1 hD s
  have hproj : (pairExtractTM true false).ComputesInTime s x (5 * (s.length + 1)) := by
    simpa only [s, pairDecode_pairEncode, Bool.false_eq_true, ↓reduceIte, List.append_nil] using
      pairExtractTM_computes true false s
  have hrun : G'.ComputesInTime s (g x) (5 * (s.length + 1) + n + 2 + B n) :=
    bufferedCompTM_computesInTime (pairExtractTM true false) G hproj hg'
  have h₄ := hQ s s (g x) _ hrun
  have h₅ : C.ComputesInTime r (s ++ g x) (5 * (r.length + 1)) := by
    simpa only [C, r, pairDecode_pairEncode, ↓reduceIte] using
      pairExtractTM_computes true true r
  have hword : s ++ g x = pairEncode x (f x ++ g x) := by
    simp only [s, pairEncode_eq, List.append_assoc]
  have h₆ : S.ComputesInTime (s ++ g x) (f x ++ g x) (5 * ((s ++ g x).length + 1)) := by
    rw [hword]
    simpa only [S, pairDecode_pairEncode, ↓reduceIte, List.nil_append] using
      pairExtractTM_computes false true (pairEncode x (f x ++ g x))
  have h := bufferedCompTM_computesInTime D P h₁ h₂
  have h := bufferedCompTM_computesInTime _ D h h₃
  have h := bufferedCompTM_computesInTime _ Q h h₄
  have h := bufferedCompTM_computesInTime _ C h h₅
  have h := bufferedCompTM_computesInTime _ S h h₆
  have hn : n + 1 ≤ budget := by dsimp only [budget]; omega
  have hs : s.length ≤ 2 * budget := by
    rw [show s = pairEncode x (f x) from rfl, length_pairEncode]
    dsimp only [budget, n] at hlf ⊢
    omega
  have hsmall : 1 ≤ budget := by omega
  have hp : p.length ≤ 3 * budget := by
    rw [show p = pairEncode x x from rfl, length_pairEncode]
    dsimp only [n] at hn
    omega
  have hq : q.length ≤ 8 * budget := by
    rw [show q = pairEncode s s from rfl, length_pairEncode]
    omega
  have hr : r.length ≤ 7 * budget := by
    rw [show r = pairEncode s (g x) from rfl, length_pairEncode]
    have : B n ≤ budget := by dsimp only [budget]; omega
    omega
  have hd₁ : a * (n + 1) ≤ a * budget := Nat.mul_le_mul_left _ hn
  have hd₂ : a * (s.length + 1) ≤ a * (3 * budget) :=
    Nat.mul_le_mul_left _ (by omega)
  have hA : A n ≤ budget := by dsimp only [budget]; omega
  have hB : B n ≤ budget := by dsimp only [budget]; omega
  refine h.mono ?_
  have hbound : (4 * a + 1500) * budget = a * budget + a * (3 * budget) + 1500 * budget := by
    ring
  change _ ≤ (4 * a + 1500) * budget
  rw [hbound]
  rw [List.length_append]
  change a * (n + 1) + p.length + 2 + 40 * (A n + p.length + 1) +
    s.length + 2 + a * (s.length + 1) +
    q.length + 2 + 40 * (5 * (s.length + 1) + n + 2 + B n + q.length + 1) +
    r.length + 2 + 5 * (r.length + 1) +
    (s.length + (g x).length) + 2 + 5 * (s.length + (g x).length + 1) ≤ _
  omega


end Turing.FinTM
