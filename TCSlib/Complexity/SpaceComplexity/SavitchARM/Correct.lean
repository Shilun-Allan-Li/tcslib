/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Search
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's theorem at the polynomial level: `NPSPACE ⊆ PSPACE`

The Savitch register machine `Complexity.LogProg.SavitchARM.A`, run with the deciders of the
code languages of a nondeterministic polynomial-space decider `N`
(`TCSlib.Complexity.SpaceComplexity.Codec`), decides `N`'s language with registers of
polynomially many binary digits; `Complexity.LogProg.arm_decides_pspace_val` then places the
language in `PSPACE` [AB09, §4.2.1, Theorem 4.14 and its corollary `PSPACE = NPSPACE`].

## Main definitions

* `Complexity.LogProg.SavitchARM.decs`, `Complexity.LogProg.SavitchARM.orcN` — the four
  deciders of the Savitch machine for `N` and their answers.

## Main results

* `Complexity.NSPACE_poly_subset_PSPACE` — `NSPACE (n ^ k + 1) ⊆ PSPACE`.
* `Complexity.NPSPACE_subset_PSPACE` — `NPSPACE ⊆ PSPACE`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

namespace SavitchARM

open Turing

/-- The deciders of the Savitch machine for `N`: `0` the input length, `1` the initial codes,
`2` the accepting codes, `3` the step pairs. -/
def decs (N : FinNDTM Bool) : Fin 4 → Language Bool :=
  ![inputLenLang, Codec.initLang N, Codec.acceptLang N, Codec.stepLang N]

/-- The answers of the deciders of the Savitch machine for `N`. -/
noncomputable def orcN (N : FinNDTM Bool) : Fin 4 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs N j : Set (List Bool)) V

/-- The step relation answered by decider `3` is the code-level step relation of `N`. -/
lemma rel_orcN (N : FinNDTM Bool) (x : List Bool) (s : ℕ) :
    Rel (orcN N) x s = Codec.StepRel N x s := by
  funext u v
  apply propext
  simp [Rel, Codec.StepRel, orcN, decs, indicator_eq_decide]

/-- Decider `1` answers membership in the initial-code language. -/
lemma initO_orcN (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) :
    InitO (orcN N) x s u ↔
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.initLang N := by
  simp [InitO, orcN, decs, indicator_eq_decide]

/-- Decider `2` answers membership in the accepting-code language. -/
lemma accO_orcN (N : FinNDTM Bool) (x : List Bool) (s v : ℕ) :
    AccO (orcN N) x s v ↔
      pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.acceptLang N := by
  simp [AccO, orcN, decs, indicator_eq_decide]

/-- The constant of the Savitch machine for `N` deciding in space `c (n ^ k + 1)`: large
enough for the radius (`radius_le`), the code width (`codeWidth_le`) and the configuration
count (`configBound_le`). -/
def bigE (N : FinNDTM Bool) (k c : ℕ) : ℕ :=
  k + c + 1 + 2 * Codec.codeK N + (Fintype.card N.State + 2 + 9 * N.k)

end SavitchARM

end Complexity.LogProg

namespace Complexity

open Turing LogProg LogProg.SavitchARM

/-- **Nondeterministic polynomial space is in `PSPACE`** [AB09, §4.2.1, Theorem 4.14 at
`S(n) = n ^ k + 1`]: `NSPACE (n ^ k + 1) ⊆ PSPACE`.

**Proof sketch.** Let `N` decide `L` in space `c (n ^ k + 1)`, and let `E = bigE N k c`. On
input `x`, with `s = (|x| + 2) ^ E ≥ c (|x| ^ k + 1)` and `w = (|x| + 2) ^ (2E)`, the codes at
radius `s` have width at most `w` and the configuration count is at most `2 ^ w`, so
`x ∈ L` iff some initial code reaches some accepting code by midpoint reachability at level
`w` (`mem_iff_reach`). The Savitch machine `A E` answers exactly this (`savitch_halts`),
with the deciders of `inputLenLang` and the code languages (all in `L ⊆ PSPACE`) and every
register value at most `2 ^ (w · w) ≤ 2 ^ (2 ^ (4E) (|x| + 1) ^ (4E))`; conclude with
`Complexity.LogProg.arm_decides_pspace_val`. -/
theorem NSPACE_poly_subset_PSPACE (k : ℕ) : NSPACE (fun n => n ^ k + 1) ⊆ PSPACE := by
  classical
  rintro L ⟨c, N, hN⟩
  set E := bigE N k c with hE
  have hE1 : 1 ≤ E := by simp only [hE, bigE]; omega
  refine arm_decides_pspace_val (A E) .scan (decs N) (fun j => ?_) (2 ^ (4 * E)) (4 * E)
    (fun x => ?_)
  · fin_cases j
    · exact LOGSPACE_subset_PSPACE inputLenLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.initLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.acceptLang_mem
    · exact LOGSPACE_subset_PSPACE Codec.stepLang_mem
  set n := x.length with hn
  have hq : ∀ m ≤ x.length, orcN N 0 (pairEncode x (Nat.bits m)) = decide (m < x.length) := by
    intro m _
    simp only [orcN, decs, Matrix.cons_val_zero, inputLenLang, indicator_indexLang_pairEncode]
    exact decide_eq_decide.mpr Iff.rfl
  have h := savitch_halts (E := E) (orc := orcN N) (x := x) hE1 hq
  have hmem := mem_iff_reach hN x ((n + 2) ^ E) ((n + 2) ^ (2 * E))
    (radius_le n k c E (by simp only [hE, bigE]; omega))
    (codeWidth_le N n E (by simp only [hE, bigE]; omega))
    (configBound_le N n E (by simp only [hE, bigE]; omega))
  rw [rel_orcN] at h
  simp only [initO_orcN, accO_orcN] at h
  rw [decide_eq_decide.mpr hmem.symm] at h
  rw [indicator_eq_decide]
  refine h.mono fun a ha => ⟨ha.1, fun r => (ha.2 r).trans ?_⟩
  -- `2 ^ (w · w) ≤ 2 ^ (2 ^ (4E) (n + 1) ^ (4E))`
  apply Nat.pow_le_pow_right (by norm_num)
  calc (n + 2) ^ (2 * E) * (n + 2) ^ (2 * E) = (n + 2) ^ (4 * E) := by rw [← pow_add]; ring_nf
    _ ≤ (2 * (n + 1)) ^ (4 * E) := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (4 * E) * (x.length + 1) ^ (4 * E) := by rw [mul_pow]

/-- **`NPSPACE ⊆ PSPACE`** [AB09, §4.2.1, the corollary of Theorem 4.14].

**Proof sketch.** A member of `NPSPACE` lies in some `NSPACE (n ^ k + 1)`
(`Complexity.NSPACE_poly_subset_PSPACE`). -/
theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
  exact NSPACE_poly_subset_PSPACE k hk

end Complexity
