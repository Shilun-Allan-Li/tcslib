/-
  ReproNestedHaves.lean — minimal repro cases probing whether `#extract_haves`
  (ExtractHaves.lean) reaches `have` bindings nested inside bullets (`·`),
  `rcases`/`obtain` case splits, and `by_cases` branches.

  Each theorem below has exactly one named `have` buried inside some kind of
  nesting construct. `#extract_haves` is run on each; if the printed output is
  missing a lemma for a given theorem, that nesting shape is a shortcoming of
  the extractor.
-/

import Mathlib.Data.Nat.Notation
import TCSlib.Tactics.ExtractHaves

open ExtractHaves

namespace ReproNestedHaves

-- Case 1: `have` inside a `·` bullet closing one conjunct of `constructor`.
theorem repro_bullet (n : Nat) : (n + 0 = n) ∧ (0 + n = n) := by
  constructor
  · have h_bullet_left : n + 0 = n := Nat.add_zero n
    exact h_bullet_left
  · have h_bullet_right : 0 + n = n := Nat.zero_add n
    exact h_bullet_right

-- Case 2: `have` inside each branch of an `Or` case split via `rcases`.
theorem repro_rcases (n : Nat) (h : n = 0 ∨ n = 1) : n < 2 := by
  rcases h with h0 | h1
  · have h_case_zero : n < 2 := by omega
    exact h_case_zero
  · have h_case_one : n < 2 := by omega
    exact h_case_one

-- Case 3: `have` after destructuring an existential via `obtain`.
theorem repro_obtain (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := by
  obtain ⟨n, hn⟩ := h
  have h_after_obtain : P n := hn
  exact ⟨n, h_after_obtain⟩

-- Case 4: `have` inside a `by_cases` branch.
theorem repro_by_cases (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases hz : n = 0
  · have h_pos_branch : n = 0 ∨ n ≠ 0 := Or.inl hz
    exact h_pos_branch
  · have h_neg_branch : n = 0 ∨ n ≠ 0 := Or.inr hz
    exact h_neg_branch

-- Case 5: `have` nested two levels deep (bullet inside a bullet).
theorem repro_nested_bullet (n : Nat) : (n = 0 ∨ n = 1 ∨ True) := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · by_cases h1 : n = 1
    · have h_deep : n = 0 ∨ n = 1 ∨ True := Or.inr (Or.inl h1)
      exact h_deep
    · have h_deep2 : n = 0 ∨ n = 1 ∨ True := Or.inr (Or.inr trivial)
      exact h_deep2

-- Case 6: tactic-mode `have` with a MULTI-LINE proof, nested two bullets deep
-- (stress test for extractHaveBody's block-boundary logic on bullet-attached haves).
theorem repro_nested_bullet_tactic (n : Nat) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · by_cases h1 : n = 1
    · have h_deep_tac : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
        right
        left
        exact h1
      exact h_deep_tac
    · have h_deep_tac2 : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
        right; right; omega
      exact h_deep_tac2

#extract_haves repro_bullet
#extract_haves repro_rcases
#extract_haves repro_obtain
#extract_haves repro_by_cases
#extract_haves repro_nested_bullet
#extract_haves repro_nested_bullet_tactic

end ReproNestedHaves
