import Mathlib

/-!
# AXLE `have2lemma` output for `Have2LemmaSimpOnlyTest.lean`

Environment lean-4.25.1, include_have_body=true, reconstruct_callsite=true.

Verbatim AXLE output EXCEPT for the three ∀-headed lemmas (key3a, key6a,
key6b): for those the broken AXLE line is preserved in a `-- AXLE emitted
(broken):` comment and a minimally-fixed version is live, so this file
compiles. Bug shape: when a have's type is headed by an explicit `∀`, AXLE
folds the whole context into the ∀-statement (no parenthesized parameters)
but splices the original body unchanged, so every hypothesis name is out of
scope. Implication-typed haves (`p → q`) are NOT affected. All simp-only
*consumption* paths (cases 1, 2, 3b, 4, 5) extracted correctly.
-/

-- Case 1: have consumed by simp only in the main goal (after the callsite is
-- rewritten to a lemma call, `key1` must still name a local hypothesis).

lemma so_case1_main_goal.key1 (a b : ℕ) (hab : a = b) : a = b := by simp_all

theorem so_case1_main_goal (a b : ℕ) (hab : a = b) : a + 0 = b := by
  have key1 : a = b := so_case1_main_goal.key1 a b hab
  simp only [key1, Nat.add_zero]

-- Case 2: have consumed by simp only inside a *later have* that is also
-- extracted — the second lemma needs `key2a` as a like-named parameter.

lemma so_case2_have_in_have.key2a (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = b := hab

lemma so_case2_have_in_have.key2b (a b c : ℕ) (hab : a = b) (hbc : b = c) (key2a : a = b) : a = c := by simp only [key2a, hbc]

theorem so_case2_have_in_have (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c := by
  have key2a : a = b := so_case2_have_in_have.key2a a b c hab hbc
  have key2b : a = c := so_case2_have_in_have.key2b a b c hab hbc key2a
  exact key2b

-- Case 3: ∀-quantified have used as a rewrite rule in a later have.

-- AXLE emitted (broken — `Unknown identifier hfg`):
-- lemma so_case3_forall_rewrite.key3a : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → ∀ (n x : ℕ), f x = g x := hfg
lemma so_case3_forall_rewrite.key3a : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → ∀ (n x : ℕ), f x = g x :=
  fun _f _g hfg _n => hfg

lemma so_case3_forall_rewrite.key3b (f g : ℕ → ℕ) (hfg : ∀ (x : ℕ), f x = g x) (n : ℕ) (key3a : ∀ (x : ℕ), f x = g x) :
  f n + f n = 2 * g n := by simp only [key3a, Nat.two_mul]

theorem so_case3_forall_rewrite (f g : ℕ → ℕ) (hfg : ∀ x, f x = g x) (n : ℕ) :
    f n + f n = 2 * g n := by
  have key3a : ∀ x, f x = g x := so_case3_forall_rewrite.key3a f g hfg n
  have key3b : f n + f n = 2 * g n := so_case3_forall_rewrite.key3b f g hfg n key3a
  exact key3b

-- Case 4: the have shadows the hypothesis its own proof consumes via simp only.

lemma so_case4_shadowing.h (a b : ℕ) (h : a = b) : b = a := by simp only [h]

theorem so_case4_shadowing (a b : ℕ) (h : a = b) : b = a := by
  have h : b = a := so_case4_shadowing.h a b h
  exact h

-- Case 5: earlier have consumed via `simp only [...] at h` (rewriting a
-- hypothesis, not the goal) inside a later have.

lemma so_case5_simp_at.key5a (a b : ℕ) (h : a + 0 = b) : a + 0 = a := Nat.add_zero a

lemma so_case5_simp_at.key5b (a b : ℕ) (h : a + 0 = b) (key5a : a + 0 = a) : a = b := by simp only [key5a] at h; exact h

theorem so_case5_simp_at (a b : ℕ) (h : a + 0 = b) : a = b := by
  have key5a : a + 0 = a := so_case5_simp_at.key5a a b h
  have key5b : a = b := so_case5_simp_at.key5b a b h key5a
  exact key5b

-- Case 6 (known bad): a ∀-headed have breaks extraction regardless of body
-- style. Note the second failure mode in key6b: inside the broken lemma the
-- tactic text `simp only [key6a]` re-resolves to the *global*
-- `so_case6_forall_consumer.key6a` (namespace resolution), not the intended
-- local hypothesis — error becomes `simp made no progress`, not an unknown
-- identifier, which could silently change proof behavior.

-- AXLE emitted (broken — `Unknown identifier hfg`):
-- lemma so_case6_forall_consumer.key6a : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → ∀ (x : ℕ), f x = g x := hfg
lemma so_case6_forall_consumer.key6a : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → ∀ (x : ℕ), f x = g x :=
  fun _f _g hfg => hfg

-- AXLE emitted (broken — `simp made no progress`):
-- lemma so_case6_forall_consumer.key6b : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → (∀ (x : ℕ), f x = g x) → ∀ (x : ℕ), g x = f x := by intro x; simp only [key6a]
lemma so_case6_forall_consumer.key6b : ∀ (f g : ℕ → ℕ), (∀ (x : ℕ), f x = g x) → (∀ (x : ℕ), f x = g x) → ∀ (x : ℕ), g x = f x := by
  intro f g hfg key6a x; simp only [key6a]

theorem so_case6_forall_consumer (f g : ℕ → ℕ) (hfg : ∀ x, f x = g x) :
    ∀ x, g x = f x := by
  have key6a : ∀ x, f x = g x := so_case6_forall_consumer.key6a f g hfg
  have key6b : ∀ x, g x = f x := so_case6_forall_consumer.key6b f g hfg key6a
  exact key6b
