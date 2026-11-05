/-!
# Fixtures for `Haves.lean`

Mathlib-free, so `scripts/haves.py test` runs in seconds.  Every shape of tactic `have`
that the tool distinguishes appears here once, with the expected outcome in the comment
above it; the test script checks `scan`, `clean` and `extract` against those expectations
(see `EXPECT` in `scripts/haves.py`).  Semantic trouble that needs Mathlib (coercions
in pretty-printed binder types, `classical`, instance arguments) is covered by running
the tool on library files, not here.
-/

namespace HavesFixtures

-- used have; `clean` leaves it; `extract` gives `(a b : Nat) (hab : a = b)`
theorem used_simp (a b : Nat) (hab : a = b) : a + 0 = b := by
  have key : a = b := by simp_all
  simp only [key, Nat.add_zero]

-- have-then-exact with a nested have: inlined, and the inner have survives
theorem exact_nested (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
  have h2 : a ≤ b + 1 := by
    have h3 : b ≤ b + 1 := Nat.le_succ b
    exact Nat.le_trans h h3
  exact h2

-- unused have deleted; anonymous have-then-exact inlined
theorem unused_and_anonymous (n : Nat) : n + 0 = n := by
  have junk : 2 + 2 = 4 := by decide
  have : n + 0 = n := by simp
  exact this

-- rfl-have then rw, closing the goal: `change (n + 1 = n + 1)` then `rfl`
theorem rfl_rw_closes (n : Nat) : (fun x => x + 1) n = n + 1 := by
  have h : ((fun x => x + 1) n = n + 1) = (n + 1 = n + 1) := rfl
  rw [h]

-- rfl-have then rw with the proof continuing: `change`, then the rest
theorem rfl_rw_continues (n : Nat) (hn : n = 0) : (fun x => x + 0) n = 0 := by
  have h : ((fun x => x + 0) n = 0) = (n + 0 = 0) := rfl
  rw [h]
  omega

-- have-then-exact whose type is not syntactically the goal: `show` is kept
theorem exact_with_show (n : Nat) : n + 0 = n := by
  have h : n = n + 0 := by simp
  exact h.symm

-- have-then-exact whose type is only definitionally the goal: `show n = n` is kept
theorem exact_show_needed (n : Nat) : (fun x => x) n = n := by
  have h : n = n := rfl
  exact h

-- have inside a bullet, exact-after: inlined inside the bullet
theorem bullet (n : Nat) : (n + 0 = n) ∧ (0 + n = n) := by
  constructor
  · have h1 : n + 0 = n := Nat.add_zero n
    exact h1
  · exact Nat.zero_add n

-- have-then-exact blocks closing the goals of `constructor` one after the other:
-- each inlined block gets a bullet, the last one too
theorem multi_goal (n : Nat) : (n + 0 = n) ∧ (0 + n = n) := by
  constructor
  have h1 : n + 0 = n := Nat.add_zero n
  exact h1
  have h2 : 0 + n = n := Nat.zero_add n
  exact h2

-- have-then-exact with binders: `intro k hk`, then the proof
theorem binders_exact (n : Nat) : ∀ k : Nat, k ≤ n → k ≤ n + 1 := by
  have h (k : Nat) (hk : k ≤ n) : k ≤ n + 1 := by omega
  exact h

-- braced tactic block, consumed by `assumption`
theorem braced_assumption (n : Nat) : n ≤ n + 1 := by
  have h : n ≤ n + 1 := by { apply Nat.le_succ }
  assumption

-- rfl-have with a parenthesized type, then rw
theorem rfl_rw_paren (n : Nat) : (fun x => x + 1) n = n + 1 := by
  have h : (((fun x => x + 1) n = n + 1) = (n + 1 = n + 1)) := rfl
  rw [h]

-- semicolon-separated: `have h := …; exact h` becomes `exact …`
theorem semicolon (n : Nat) : n ≤ n + 1 := by
  have h := Nat.le_succ n; exact h

-- a comment between an unused have and the next tactic survives the deletion
theorem unused_with_comment (n : Nat) : n = n := by
  have junk : n + 0 = n := by simp
  -- this comment stays
  rfl

-- have with binders: extract keeps them; its only use is dead so the second
-- round of `clean` deletes both
theorem binders_dead (n : Nat) : n ≤ n + 3 := by
  have h_expl (k : Nat) (hk : k ≤ n) : k ≤ n + 1 := by omega
  have u := h_expl n (Nat.le_refl n)
  omega

-- have with binders that is used: extract takes `(k : Nat) (hk : k ≤ n)` and the
-- call site passes `n k hk`
theorem binders_used (n : Nat) : n ≤ n + 3 := by
  have h_expl (k : Nat) (hk : k ≤ n) : k ≤ n + 1 := by omega
  exact Nat.le_trans (h_expl n (Nat.le_refl n)) (by omega)

-- tactic-introduced variables are pretty-printed binders of the lemma
theorem intro_vars : ∀ n : Nat, ∀ m : Nat, m ≤ n → m ≤ n + 1 := by
  intro n m hmn
  have h : m ≤ n + 1 := Nat.le_succ_of_le hmn
  exact h

-- destructured variables likewise
theorem obtain_vars (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := by
  obtain ⟨n, hn⟩ := h
  have h2 : P n := hn
  exact ⟨n, h2⟩

-- an inaccessible dependency: `clean` inlines; `extract` names it with `rename_i a` first
theorem inaccessible (p : Nat → Prop) (h : ∀ n, p n → p (n+1)) : p 0 → p 1 := by
  intro
  have h1 : p 1 := h 0 ‹p 0›
  exact h1

-- a let-bound dependency: `extract` refuses; the have is unused, so `clean` deletes it
theorem let_dep (n : Nat) : n + 1 = 1 + n := by
  let m := n + 1
  have h : m = n + 1 := rfl
  omega

-- implicit theorem binders stay implicit when inferable from the statement
theorem implicit_binders {n : Nat} (hn : 0 < n) : 1 ≤ n := by
  have h : 1 ≤ n := hn
  exact h

-- the have's proof uses a hypothesis not named in its text (omega): still a parameter
theorem silent_use (a b : Nat) (hab : a < b) : a + 1 ≤ b + 1 := by
  have h : a + 1 ≤ b := by omega
  exact Nat.le_succ_of_le h

-- named only as a hint the final proof did not need: reported `hintOnly`, never deleted
theorem hint_only (n : Nat) : n + 0 = n := by
  have h2 : n = n := rfl
  simp [h2]

-- a destructuring have is reported and left alone
theorem destructuring (n : Nat) : n ≤ n + 1 := by
  have ⟨a, ha⟩ : ∃ a : Nat, a = n := ⟨n, rfl⟩
  omega

-- `open … in` before the declaration: the lemma is placed under the same prefix
open Nat in
theorem open_in (n : Nat) : n ≤ succ n := by
  have h : n ≤ succ n := le_succ n
  exact h

-- a multi-line type, colon at end of line: the text moves intact
theorem multiline_type (a b : Nat) (h : a ≤ b) : a ≤ b + 2 := by
  have step :
      a ≤ b + 1 := by
    omega
  exact Nat.le_succ_of_le step

end HavesFixtures
