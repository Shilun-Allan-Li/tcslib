/-
  ReproNestedHaves.lean — minimal repro cases probing whether `#extract_haves`
  (ExtractHaves.lean) reaches `have` bindings nested inside bullets (`·`),
  `rcases`/`obtain` case splits, and `by_cases` branches.

  Each theorem below has exactly one named `have` buried inside some kind of
  nesting construct. `#extract_haves` is run on each; if the printed output is
  missing a lemma for a given theorem, that nesting shape is a shortcoming of
  the extractor.
-/

import Mathlib
import TCSlib.Tactics.ExtractHaves

open ExtractHaves

namespace ReproNestedHaves

-- Case 1: `have` inside a `·` bullet closing one conjunct of `constructor`.
private lemma repro_bullet_aux_h_bullet_left (n : Nat) : n + 0 = n :=
  Nat.add_zero n

private lemma repro_bullet_aux_h_bullet_right (n : Nat) : 0 + n = n :=
  Nat.zero_add n

theorem repro_bullet (n : Nat) : (n + 0 = n) ∧ (0 + n = n) := by
  constructor
  ·
    exact (repro_bullet_aux_h_bullet_left n)
  ·
    exact (repro_bullet_aux_h_bullet_right n)

-- Case 2: `have` inside each branch of an `Or` case split via `rcases`.
private lemma repro_rcases_aux_h_case_zero (n : Nat) (h0 : n = 0) : n < 2 := by
  omega

private lemma repro_rcases_aux_h_case_one (n : Nat) (h1 : n = 1) : n < 2 := by
  omega

theorem repro_rcases (n : Nat) (h : n = 0 ∨ n = 1) : n < 2 := by
  rcases h with h0 | h1
  ·
    exact (repro_rcases_aux_h_case_zero n h0)
  ·
    exact (repro_rcases_aux_h_case_one n h1)

-- Case 3: `have` after destructuring an existential via `obtain`.
private lemma repro_obtain_aux_h_after_obtain (P : Nat → Prop) (n : Nat) (hn : P n) : P n :=
  hn

theorem repro_obtain (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (repro_obtain_aux_h_after_obtain P n hn)⟩

-- Case 4: `have` inside a `by_cases` branch.
private lemma repro_by_cases_aux_h_pos_branch (n : Nat) (hz : n = 0) : n = 0 ∨ n ≠ 0 :=
  Or.inl hz

private lemma repro_by_cases_aux_h_neg_branch (n : Nat) (hz : ¬n = 0) : n = 0 ∨ n ≠ 0 :=
  Or.inr hz

theorem repro_by_cases (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases hz : n = 0
  ·
    exact (repro_by_cases_aux_h_pos_branch n hz)
  ·
    exact (repro_by_cases_aux_h_neg_branch n hz)

-- Case 5: `have` nested two levels deep (bullet inside a bullet).
private lemma repro_nested_bullet_aux_h_deep (n : Nat) (h1 : n = 1) : n = 0 ∨ n = 1 ∨ True :=
  Or.inr (Or.inl h1)

private lemma repro_nested_bullet_aux_h_deep2 (n : Nat) : n = 0 ∨ n = 1 ∨ True :=
  Or.inr (Or.inr trivial)

theorem repro_nested_bullet (n : Nat) : (n = 0 ∨ n = 1 ∨ True) := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · by_cases h1 : n = 1
    ·
      exact (repro_nested_bullet_aux_h_deep n h1)
    ·
      exact (repro_nested_bullet_aux_h_deep2 n)

-- Case 6: tactic-mode `have` with a MULTI-LINE proof, nested two bullets deep
-- (stress test for extractHaveBody's block-boundary logic on bullet-attached haves).
private lemma repro_nested_bullet_tactic_aux_h_deep_tac (n : Nat) (h1 : n = 1) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  right
  left
  exact h1

private lemma repro_nested_bullet_tactic_aux_h_deep_tac2 (n : Nat) (h0 : ¬n = 0) (h1 : ¬n = 1) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  right; right; omega

theorem repro_nested_bullet_tactic (n : Nat) : n = 0 ∨ n = 1 ∨ n ≥ 2 := by
  by_cases h0 : n = 0
  · exact Or.inl h0
  · by_cases h1 : n = 1
    ·
      exact (repro_nested_bullet_tactic_aux_h_deep_tac n h1)
    ·
      exact (repro_nested_bullet_tactic_aux_h_deep_tac2 n h0 h1)

#extract_haves repro_bullet
#extract_haves repro_rcases
#extract_haves repro_obtain
#extract_haves repro_by_cases
#extract_haves repro_nested_bullet
#extract_haves repro_nested_bullet_tactic

end ReproNestedHaves
