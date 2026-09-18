/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class coNP

[AB09, §2.6.1]: `coNP` is the class of complements of `NP` languages
(Definition 2.19), equivalently the class of languages whose membership is
certified by *every* polynomial-length certificate (Definition 2.20); the
equivalence is [AB09, Exercise 2.24]. This module also records the closure of
`P` under complement that the equivalence rides on, and the two standard
containment facts `P ⊆ NP ∩ coNP` and `P = NP → NP = coNP`.

## Design

* The complement-form Definition 2.19 is primary (it is one line); the
  ∀-certificate form is the characterization theorem, matching [AB09]'s own
  pedagogical ordering in reverse.
* `Complexity.compl_mem_P` is a statement *about the Chapter-1 class `P`* that
  Chapter 1 never needed; it is a new addition beyond the audited Chapter-1
  surface, placed here (its first consumer) and flagged for the phase-1 audit.

## Main definitions

* `Complexity.coNP` — the class coNP. [AB09, Definition 2.19]

## Main results

* `Complexity.compl_mem_P` — `P` is closed under complement.
* `Complexity.mem_coNP_iff_forall` — the ∀-certificate characterization
  [AB09, Definition 2.20 and Exercise 2.24].
* `Complexity.P_subset_NP_inter_coNP` — [AB09, Exercise 2.23].
* `Complexity.NP_eq_coNP_of_P_eq_NP` — [AB09, Exercise 2.25].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20, pp. 55-56;
  Exercises 2.23-2.25.)
-/

namespace Complexity

/-- **The class coNP** [AB09, Definition 2.19]: the complements of `NP` languages. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- **`P` is closed under complement**: if `L` is decidable in polynomial time then
so is its complement.

**Proof sketch.** Obtain a decider of `L` from `Complexity.mem_P_iff` and
postcompose it with the Boolean-negation postprocessor
`Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]`
(`w ↦ if w = [true] then [false] else [true]`) via
`Turing.FinTM.exists_comp_partial`; the composite decides `Lᶜ` because the
indicator of the complement is the negated indicator, and the budget stays
polynomial by the composition ledger. This is a new statement about the
Chapter-1 class, flagged for audit (plan §6). -/
theorem compl_mem_P {L : Language Bool} (h : L ∈ P) : Lᶜ ∈ P := by
  sorry

/-- **The ∀-certificate characterization of coNP** [AB09, Definition 2.20,
equivalence per Exercise 2.24]: `L ∈ coNP` iff there are a polynomially bounded
`p` and a verifier `V ∈ P` with `x ∈ L ↔ ∀ u, |u| = p |x| → x ++ u ∈ V`.

**Proof sketch.** Negate the exact-length existential in `NP`'s membership
equivalence for `Lᶜ`: `x ∈ L ↔ ¬(∃ u, |u| = p |x| ∧ x ++ u ∈ V₀)
↔ ∀ u, |u| = p |x| → x ++ u ∈ V₀ᶜ`, and `V₀ᶜ ∈ P` by
`Complexity.compl_mem_P`; both directions instantiate the same `p`, complementing
the verifier. -/
theorem mem_coNP_iff_forall {L : Language Bool} :
    L ∈ coNP ↔ ∃ (p : ℕ → ℕ) (V : Language Bool), PolyBound p ∧ V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔ ∀ u : List Bool, u.length = p x.length → x ++ u ∈ V := by
  sorry

/-- **`P ⊆ NP ∩ coNP`** [AB09, Exercise 2.23].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; for the `coNP` half,
`L ∈ P` gives `Lᶜ ∈ P ⊆ NP` by `Complexity.compl_mem_P`, i.e. `L ∈ coNP`. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP ∩ coNP := by
  sorry

/-- **If `P = NP` then `NP = coNP`** [AB09, Exercise 2.25].

**Proof sketch.** Under `P = NP`: `L ∈ NP → L ∈ P → Lᶜ ∈ P → Lᶜ ∈ NP → L ∈ coNP`
by `Complexity.compl_mem_P`, and symmetrically `L ∈ coNP → Lᶜ ∈ NP = P → L ∈ P =
NP` by closing under complement once more. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P = NP) : NP = coNP := by
  sorry

end Complexity
