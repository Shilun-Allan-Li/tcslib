import Mathlib.Data.Nat.Notation

/-!
# Test: AXLE `have2lemma` when a `have` feeds a later `simp only`

Companion to `Have2LemmaSimpAllTest.lean`. There the risk was the have's
*proof* silently consuming context; here it is the have being *consumed by
name* in a later `simp only [...]` argument list. Two failure surfaces:

1. Callsite reconstruction must keep the have's name bound so a downstream
   `simp only [key]` in the main proof still resolves.
2. When the consumer is itself a `have` that gets extracted, the extracted
   lemma must expose the earlier have as a parameter whose *name* matches the
   `simp only [key]` tactic text verbatim, or the extracted body won't
   elaborate.
-/

-- Case 1: have consumed by simp only in the main goal (after the callsite is
-- rewritten to a lemma call, `key1` must still name a local hypothesis).
theorem so_case1_main_goal (a b : ℕ) (hab : a = b) : a + 0 = b := by
  have key1 : a = b := by simp_all
  simp only [key1, Nat.add_zero]

-- Case 2: have consumed by simp only inside a *later have* that is also
-- extracted — the second lemma needs `key2a` as a like-named parameter.
theorem so_case2_have_in_have (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c := by
  have key2a : a = b := hab
  have key2b : a = c := by simp only [key2a, hbc]
  exact key2b

-- Case 3: ∀-quantified have used as a rewrite rule in a later have.
theorem so_case3_forall_rewrite (f g : ℕ → ℕ) (hfg : ∀ x, f x = g x) (n : ℕ) :
    f n + f n = 2 * g n := by
  have key3a : ∀ x, f x = g x := hfg
  have key3b : f n + f n = 2 * g n := by simp only [key3a, Nat.two_mul]
  exact key3b

-- Case 4: the have shadows the hypothesis its own proof consumes via simp only.
theorem so_case4_shadowing (a b : ℕ) (h : a = b) : b = a := by
  have h : b = a := by simp only [h]
  exact h

-- Case 5: earlier have consumed via `simp only [...] at h` (rewriting a
-- hypothesis, not the goal) inside a later have.
theorem so_case5_simp_at (a b : ℕ) (h : a + 0 = b) : a = b := by
  have key5a : a + 0 = a := Nat.add_zero a
  have key5b : a = b := by simp only [key5a] at h; exact h
  exact key5b

-- Case 6 (known bad): a ∀-headed have breaks extraction regardless of body
-- style — AXLE folds the context into the ∀-statement and the body loses
-- every hypothesis name. When such a have consumes an earlier one via
-- `simp only [key6a]`, the argument silently re-resolves to the extracted
-- *global* `<thm>.key6a` instead of the intended local hypothesis.
theorem so_case6_forall_consumer (f g : ℕ → ℕ) (hfg : ∀ x, f x = g x) :
    ∀ x, g x = f x := by
  have key6a : ∀ x, f x = g x := hfg
  have key6b : ∀ x, g x = f x := by intro x; simp only [key6a]
  exact key6b
