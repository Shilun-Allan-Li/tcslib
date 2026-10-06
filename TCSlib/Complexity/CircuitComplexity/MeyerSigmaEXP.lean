/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.ClassNP.ExpPoly
import TCSlib.Complexity.PolyHierarchy.Collapse
import TCSlib.Complexity.ClassNP.CoNP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `Σ₂ᵖ ⊆ EXP`

The second level of the polynomial hierarchy is decidable in exponential time: the
inclusion behind the equality `EXP = Σ₂ᵖ` in Meyer's theorem [AB09, Thm 6.20] (the book
uses it tacitly; cf. [AB09, Claim 2.4] for `NP ⊆ EXP`).

## The proof

Write `x ∈ L ⟺ ∃ u (|u| = C(|x|+1)^c), ⟨x, u⟩ ∈ L'` with `L' ∈ coNP`
(`Complexity.mem_SigmaP_two_iff`). Since `L'ᶜ ∈ NP ⊆ EXP` (`Complexity.NP_subset_EXP`),
`L'` is decided in exponential time (output flipped by a linear postprocessor); composed
with the catalog's split search, the language `V = {x ++ u | ⟨x, u⟩ ∈ L'}` is decided in
time `2^{poly}`. The brute-force enumerator with an arbitrary-time verifier
(`Complexity.exists_proj_decider`) then decides `L` in time
`2^{C(n+1)^c} · 2^{poly(n)}`, which is `EXP`.

The exponential-polynomial bounds `Complexity.ExpPoly` are in
`TCSlib.Complexity.ClassNP.ExpPoly`.

## Main results

* `Complexity.SigmaP_two_subset_EXP` — `Σ₂ᵖ ⊆ EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §5.2; §6.4, Theorem 6.20.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.PolyHierarchy

/-! ### The verifier on concatenations -/

/-- The split search finds the length of the input part (the strict monotonicity of
`n ↦ n + C(n+1)^c`). -/
theorem solveSplit_self' (C c n : ℕ) : solveSplit C c (n + C * (n + 1) ^ c) = some n := by
  have hmono : StrictMono (fun j : ℕ => j + C * (j + 1) ^ c) := by
    intro a b h
    have := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h.le 1) c)
    dsimp only
    omega
  unfold solveSplit
  cases h : (List.range (n + C * (n + 1) ^ c + 1)).find?
      (fun i => i + C * (i + 1) ^ c == n + C * (n + 1) ^ c) with
  | none =>
    have := List.find?_eq_none.mp h n (by simp only [List.mem_range]; omega)
    simp at this
  | some j =>
    have hj := List.find?_some h
    simp only [beq_iff_eq] at hj
    rw [hmono.injective hj]

/-- The splitter recovering `⟨x, u⟩` from `x ++ u` when `|u| = C(|x|+1)^c`. -/
def splitXU (C c : ℕ) (w : List Bool) : List Bool :=
  match solveSplit C c w.length with
  | some i => pairEncode (w.take i) (w.drop i)
  | none => []

/-- On an exact-length concatenation the splitter returns the pair. -/
theorem splitXU_append (C c : ℕ) (x u : List Bool) (hu : u.length = C * (x.length + 1) ^ c) :
    splitXU C c (x ++ u) = pairEncode x u := by
  simp [splitXU, hu, solveSplit_self']

/-- **A complement decider** with a linear postprocessor: if `M` decides `L` within `T`,
some machine decides `Lᶜ` within `c (T n + a (T n + 1) + 1)` (the argument of
`Complexity.compl_mem_P`, for an arbitrary bound).

**Proof sketch.** Compose the decider (its one-bit output) with the catalog's equality test
against `[true]` (`Turing.FinTM.computesFunInTime_ifEq`), which flips the bit
(`Turing.FinTM.computesFunInTime_comp`). -/
theorem exists_compl_decider {L : Language Bool} {M : FinTM Bool} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) :
    ∃ (M' : FinTM Bool) (c a : ℕ), M'.DecidesInTime Lᶜ (fun n => c * (T n + a * (T n + 1) + 1)) := by
  classical
  obtain ⟨N, a, hN⟩ := computesFunInTime_ifEq [true] [false] [true]
  have hfun : M.ComputesFunInTime (fun x => [MultiTapeTM.indicator L x]) T := fun x => hM x
  obtain ⟨M', b, hcomp⟩ := computesFunInTime_comp hfun hN
    (fun _ _ hle => Nat.mul_le_mul_left a (Nat.add_le_add_right hle 1))
  refine ⟨M', b, a, fun x => ?_⟩
  by_cases hx : x ∈ L
  · have hxc : x ∉ (Lᶜ : Language Bool) := fun hnot => hnot hx
    simpa [Function.comp_apply, MultiTapeTM.indicator, hx, hxc] using hcomp x
  · have hxc : x ∈ (Lᶜ : Language Bool) := hx
    simpa [Function.comp_apply, MultiTapeTM.indicator, hx, hxc] using hcomp x

end Complexity.Meyer

namespace Complexity

open Turing Turing.FinTM Complexity.PolyHierarchy Meyer

/-- **`Σ₂ᵖ ⊆ EXP`** [AB09, Claim 2.4 and §5.2; the inclusion behind the equality in
Thm 6.20]: every language of the second level of the polynomial hierarchy is decidable
in exponential time.

**Proof sketch.** `L = {x | ∃ u, ⟨x, u⟩ ∈ L'}` with `L' ∈ coNP`. Since `L'ᶜ ∈ NP ⊆ EXP`,
a linear postprocessor gives an exponential-time decider of `L'`; composed with the split
search it decides `V = {x ++ u | ⟨x, u⟩ ∈ L'}` within `2^{poly}`. The brute-force
enumerator (`exists_proj_decider`) decides `L` within
`b 2^{C(n+1)^c} (Tv(n + C(n+1)^c) + poly)`, an exponential-polynomial bound
(`ExpPoly.mem_EXP`). -/
theorem SigmaP_two_subset_EXP : SigmaP 2 ⊆ EXP := by
  intro L hL
  obtain ⟨C, c, L', hL', hLx⟩ := mem_SigmaP_two_iff.mp hL
  obtain ⟨e, c₁, M₁, hM₁⟩ := Set.mem_iUnion.mp (NP_subset_EXP hL')
  obtain ⟨M₂, c₂, a₂, hM₂⟩ := exists_compl_decider hM₁
  rw [compl_compl] at hM₂
  set T₂ : ℕ → ℕ := fun n => c₂ * (c₁ * 2 ^ n ^ e + a₂ * (c₁ * 2 ^ n ^ e + 1) + 1) with hT₂
  have hT₂m : Monotone T₂ := by
    intro m n hmn
    have : 2 ^ m ^ e ≤ 2 ^ n ^ e := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hmn e)
    simp only [hT₂]
    gcongr
  obtain ⟨S, s₀, hS⟩ := computesFunInTime_splitSolve C c
  have hfun₂ : M₂.ComputesFunInTime (fun x => [MultiTapeTM.indicator L' x]) T₂ := fun x => hM₂ x
  obtain ⟨M₃, c₃, hM₃⟩ := computesFunInTime_comp hS hfun₂ hT₂m
  set V : Language Bool := splitXU C c ⁻¹' L' with hV
  set Tv : ℕ → ℕ := fun n => c₃ * (s₀ * (n + 1) ^ (c + 2) + T₂ (s₀ * (n + 1) ^ (c + 2)) + 1)
    with hTv
  have hdec : M₃.DecidesInTime V Tv := by
    intro x
    have := hM₃ x
    simp only [Function.comp_apply] at this
    convert this using 2
  obtain ⟨b, E, hE⟩ := exists_proj_decider C c V Tv M₃ hdec
  have hlang : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L := by
    ext x
    rw [hLx x]
    simp only [Set.mem_setOf_eq, hV]
    constructor
    · rintro ⟨u, hu, hmem⟩
      refine ⟨u, hu, ?_⟩
      have h' : splitXU C c (x ++ u) ∈ L' := hmem
      rwa [splitXU_append C c x u hu] at h'
    · rintro ⟨u, hu, hmem⟩
      refine ⟨u, hu, ?_⟩
      show splitXU C c (x ++ u) ∈ L'
      rwa [splitXU_append C c x u hu]
  rw [hlang] at hE
  refine ExpPoly.mem_EXP (T := fun n => b * 2 ^ (C * (n + 1) ^ c) *
    (Tv (n + C * (n + 1) ^ c) + (n + C * (n + 1) ^ c + 1) ^ (c + 1))) ?_
    ⟨1, E, fun x => by simpa only [one_mul] using hE x⟩
  -- the bound is exponential-polynomial
  have hTvm : Monotone Tv := by
    intro m n hmn
    have h1 : s₀ * (m + 1) ^ (c + 2) ≤ s₀ * (n + 1) ^ (c + 2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    simp only [hTv]
    gcongr
    exact hT₂m h1
  have hT₂e : ExpPoly T₂ := by
    have := ((expPoly_exp c₁ e).add ((expPoly_poly a₂ 0).mul
      ((expPoly_exp c₁ e).add (expPoly_poly 1 0)))).add (expPoly_poly 1 0)
    exact (((expPoly_poly c₂ 0).mul this).of_le (fun n => by simp [hT₂]))
  have hTve : ExpPoly Tv := by
    have := ((expPoly_poly s₀ (c + 2)).add (hT₂e.comp_poly s₀ (c + 2))).add
      (expPoly_poly 1 0)
    exact ((expPoly_poly c₃ 0).mul this).of_le (fun n => by simp [hTv])
  have hshift : ∀ n, n + C * (n + 1) ^ c ≤ (C + 1) * (n + 1) ^ (c + 1) := by
    intro n
    have h1 : C * (n + 1) ^ c ≤ C * (n + 1) ^ (c + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : n ≤ (n + 1) ^ (c + 1) := by
      calc n ≤ n + 1 := by omega
        _ = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hA : ExpPoly (fun n => Tv (n + C * (n + 1) ^ c)) :=
    (hTve.comp_poly (C + 1) (c + 1)).of_le (fun n => hTvm (hshift n))
  have hB : ExpPoly (fun n => (n + C * (n + 1) ^ c + 1) ^ (c + 1)) := by
    refine (expPoly_poly ((C + 2) ^ (c + 1)) ((c + 1) * (c + 1))).of_le (fun n => ?_)
    have : n + C * (n + 1) ^ c + 1 ≤ (C + 2) * (n + 1) ^ (c + 1) := by
      have := hshift n
      have h3 : 1 ≤ (n + 1) ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      nlinarith
    calc (n + C * (n + 1) ^ c + 1) ^ (c + 1) ≤ ((C + 2) * (n + 1) ^ (c + 1)) ^ (c + 1) :=
          Nat.pow_le_pow_left this _
      _ = (C + 2) ^ (c + 1) * (n + 1) ^ ((c + 1) * (c + 1)) := by rw [mul_pow, ← pow_mul]
  have hW : ExpPoly (fun n => 2 ^ (C * (n + 1) ^ c)) := ⟨C, c, fun n => le_rfl⟩
  exact ((expPoly_poly b 0).mul hW).mul (hA.add hB) |>.of_le
    (fun n => by simp only [pow_zero, mul_one]; exact le_rfl)

end Complexity
