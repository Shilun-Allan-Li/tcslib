/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.PolyHierarchy.Levels

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collapse of the polynomial hierarchy

[AB09, Theorem 5.4]: (1) for every `i ≥ 1`, if `Σᵢᵖ = Πᵢᵖ` then `PH = Σᵢᵖ` (the hierarchy
collapses to the `i`-th level); (2) if `P = NP` then `PH = P`. This file also records the
second-level characterizations used by the Karp–Lipton and Meyer theorems [AB09, §6.4]:
`Σ₂ᵖ = ∃·coNP` and `Π₂ᵖ = ∀·NP`, and the explicit `∃∀` / `∀∃` forms.

## Main results

* `Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP` — [AB09, Theorem 5.4 (1)].
* `Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP` — the one-inclusion form used by
  Karp–Lipton (`Π₂ᵖ ⊆ Σ₂ᵖ ⇒ PH = Σ₂ᵖ`).
* `Complexity.PH_eq_P_of_P_eq_NP` — [AB09, Theorem 5.4 (2)].
* `Complexity.mem_SigmaP_two_iff`, `Complexity.mem_PiP_two_iff` — `Σ₂ᵖ` via `coNP`,
  `Π₂ᵖ` via `NP`.
* `Complexity.mem_SigmaP_two_iff_exists_forall`, `Complexity.mem_PiP_two_iff_forall_exists`
  — the explicit two-quantifier forms.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2, Definition 5.3, p. 97; Theorem 5.4, pp. 97–98;
  Exercise 5.12; §6.4.)
-/

namespace Complexity

open Turing

/-- If `Πᵢᵖ ⊆ Σᵢᵖ` then `Σᵢᵖ = Πᵢᵖ` (complement both sides). -/
theorem SigmaP_eq_PiP_of_PiP_subset_SigmaP {i : ℕ} (h : PiP i ⊆ SigmaP i) :
    SigmaP i = PiP i := by
  refine Set.Subset.antisymm (fun L hL => ?_) h
  exact h (compl_mem_PiP_iff.mpr hL)

/-- If `Σᵢᵖ ⊆ Πᵢᵖ` then `Σᵢᵖ = Πᵢᵖ` (complement both sides). -/
theorem SigmaP_eq_PiP_of_SigmaP_subset_PiP {i : ℕ} (h : SigmaP i ⊆ PiP i) :
    SigmaP i = PiP i := by
  refine Set.Subset.antisymm h (fun L hL => ?_)
  exact compl_mem_PiP_iff.mp (h hL)

/-- **The polynomial hierarchy collapses to the `i`-th level** [AB09, Theorem 5.4 (1)]:
for every `i ≥ 1`, if `Σᵢᵖ = Πᵢᵖ` then `PH = Σᵢᵖ`.

**Proof sketch.** It suffices that `Σⱼᵖ ⊆ Σᵢᵖ` for all `j`. For `j ≤ i` this is
monotonicity. For `j ≥ i`, induct on `j`: a language in `Σⱼ₊₁ᵖ` is `∃·L'` with
`L' ∈ Πⱼᵖ` (`Complexity.mem_SigmaP_succ_iff`); by the induction hypothesis (complemented)
`L' ∈ Πᵢᵖ = Σᵢᵖ`, and merging the outer `∃` into the leading `∃` block of `L'`
(`Complexity.mem_SigmaP_of_exists`, using `i ≥ 1`) puts the language in `Σᵢᵖ`. This is
the book's argument: replace the inner `Πᵢᵖ` block by an equivalent `Σᵢᵖ` block and merge
the adjacent existential quantifiers. ([AB09] states Theorem 5.4 and leaves its proof as
Exercise 5.12; the sketch above is the standard argument indicated there.) -/
theorem PH_eq_SigmaP_of_SigmaP_eq_PiP {i : ℕ} (hi : 1 ≤ i) (h : SigmaP i = PiP i) :
    PH = SigmaP i := by
  have hi0 : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi
  -- Every higher level falls into `Σᵢᵖ`.
  have hup : ∀ j, i ≤ j → SigmaP j ⊆ SigmaP i := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih =>
      intro L hL
      obtain ⟨C, c, L', hL', hx⟩ := mem_SigmaP_succ_iff.mp hL
      -- `L' ∈ Πⱼᵖ ⊆ Πᵢᵖ = Σᵢᵖ`.
      have hL'i : L' ∈ SigmaP i := h ▸ (show L' ∈ PiP i from ih hL')
      exact mem_SigmaP_of_exists hi0 hL'i C c hx
  refine Set.Subset.antisymm (fun L hL => ?_) (SigmaP_subset_PH i)
  obtain ⟨j, hj⟩ := mem_PH_iff.mp hL
  rcases le_total j i with hji | hij
  · exact SigmaP_mono hji hj
  · exact hup j hij hj

/-- **Collapse from one inclusion**: for `i ≥ 1`, if `Πᵢᵖ ⊆ Σᵢᵖ` then `PH = Σᵢᵖ`. (The
form in which Karp–Lipton [AB09, Theorem 6.19] concludes: it proves `Π₂ᵖ ⊆ Σ₂ᵖ`.) -/
theorem PH_eq_SigmaP_of_PiP_subset_SigmaP {i : ℕ} (hi : 1 ≤ i) (h : PiP i ⊆ SigmaP i) :
    PH = SigmaP i :=
  PH_eq_SigmaP_of_SigmaP_eq_PiP hi (SigmaP_eq_PiP_of_PiP_subset_SigmaP h)

/-- **If `P = NP` then `PH = P`** [AB09, Theorem 5.4 (2)].

**Proof sketch.** `P = NP` gives `NP = coNP` (`P` is closed under complement,
`Complexity.NP_eq_coNP_of_P_eq_NP`), i.e. `Σ₁ᵖ = Π₁ᵖ`; by part (1),
`PH = Σ₁ᵖ = NP = P`. -/
theorem PH_eq_P_of_P_eq_NP (h : P = NP) : PH = P := by
  have h1 : SigmaP 1 = PiP 1 := by
    rw [SigmaP_one, PiP_one]
    exact NP_eq_coNP_of_P_eq_NP h
  rw [PH_eq_SigmaP_of_SigmaP_eq_PiP le_rfl h1, SigmaP_one, h]

/-! ### The second level -/

/-- **`Σ₂ᵖ = ∃·coNP`** [AB09, §5.2 and its use in §6.4]: `L ∈ Σ₂ᵖ` iff there are an
explicit polynomial length `C (|x|+1)^c` and `L' ∈ coNP` with
`x ∈ L ⟺ ∃ u, |u| = C (|x|+1)^c ∧ ⟨x, u⟩ ∈ L'`. -/
theorem mem_SigmaP_two_iff {L : Language Bool} :
    L ∈ SigmaP 2 ↔ ∃ (C c : ℕ) (L' : Language Bool), L' ∈ coNP ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ pairEncode x u ∈ L' := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, mem_SigmaP_succ_iff, PiP_one]

/-- **`Π₂ᵖ = ∀·NP`** [AB09, §5.2 and its use in §6.4]: `L ∈ Π₂ᵖ` iff there are an
explicit polynomial length `C (|x|+1)^c` and `L' ∈ NP` with
`x ∈ L ⟺ ∀ u, |u| = C (|x|+1)^c → ⟨x, u⟩ ∈ L'`. -/
theorem mem_PiP_two_iff {L : Language Bool} :
    L ∈ PiP 2 ↔ ∃ (C c : ℕ) (L' : Language Bool), L' ∈ NP ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → pairEncode x u ∈ L' := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, mem_PiP_succ_iff, SigmaP_one]

/-- **`Σ₂ᵖ` explicitly** [AB09, Definition 5.1; Definition 5.3 at `i = 2`]: `L ∈ Σ₂ᵖ` iff there are an
explicit polynomial `q(n) = C (n+1)^c` and `V ∈ P` with
`x ∈ L ⟺ ∃ u (|u| = q(|x|)) ∀ v (|v| = q(|x|)), ⟨⟨x, u⟩, v⟩ ∈ V`. -/
theorem mem_SigmaP_two_iff_exists_forall {L : Language Bool} :
    L ∈ SigmaP 2 ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧
          ∀ v : List Bool, v.length = C * (x.length + 1) ^ c →
            pairEncode (pairEncode x u) v ∈ V := Iff.rfl

/-- **`Π₂ᵖ` explicitly** [AB09, §5.2]: `L ∈ Π₂ᵖ` iff there are an explicit polynomial
`q(n) = C (n+1)^c` and `V ∈ P` with
`x ∈ L ⟺ ∀ u (|u| = q(|x|)) ∃ v (|v| = q(|x|)), ⟨⟨x, u⟩, v⟩ ∈ V`. -/
theorem mem_PiP_two_iff_forall_exists {L : Language Bool} :
    L ∈ PiP 2 ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c →
          ∃ v : List Bool, v.length = C * (x.length + 1) ^ c ∧
            pairEncode (pairEncode x u) v ∈ V :=
  mem_PiP_iff

end Complexity
