/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Certificate and choice words: split uniqueness and branch truncation

Two facts about the words that witness nondeterminism, shared by the plain and the
relativized developments ([AB09, Definition 2.1 and Theorem 2.6]).

* **Split uniqueness.** When the certificate length is a function `f` of the input
  length and `n ↦ n + f n` is strictly increasing, a concatenation `x ++ u` with
  `|u| = f |x|` determines `x` and `u`. The exact NP certificate length
  `C·(n + 1)^c` is such an `f`, including at `C = 0` and `c = 0`.
* **Branch truncation.** For any run along a choice word whose halted runs absorb
  further choices, if every run along a word of length `t` has halted, then the run
  along a longer word is the run along its length-`t` prefix. With the budget
  inequality `a·(n^c + 1) ≤ 2a·(n + 1)^c`, this identifies decision within a
  polynomial time with acceptance along exact-length choice words.

The statements are model-agnostic: the run is any function of the choice word. The
plain nondeterministic machines (`ClassNP/Nondeterminism.lean`) and the oracle ones
(`Build/OracleSim.lean`) instantiate them with their own `runWith`, `runWith_append`
and `runWith_of_halt`, and the plain certificate shell (`Build/CertShell.lean`) uses the
split. Factored here at the wave-1 statement gate (round 1, finding 2), replacing three
private copies.

## Main results

* `Turing.append_split_unique` — a concatenation with a length-determined suffix splits
  uniquely.
* `Turing.certificateLength_strictMono` — `n ↦ n + C·(n + 1)^c` is strictly increasing.
* `Turing.choiceBudget_le` — `a·(n^c + 1) ≤ 2a·(n + 1)^c`.
* `Turing.run_take_of_halted` — truncate a choice word to a length at which every run
  has halted.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.1: certificates of length `p(|x|)`; Theorem 2.6:
  choice words of a nondeterministic machine as certificates.)
-/

namespace Turing

/-- **Split uniqueness** ([AB09, Definition 2.1], the certificate split). If
`n ↦ n + f n` is strictly increasing, two concatenations `x ++ u = y ++ v` with
`|u| = f |x|` and `|v| = f |y|` have `x = y` and `u = v`.

**Proof sketch.** Equal concatenations have equal lengths, so `|x| + f |x| = |y| + f |y|`
and injectivity gives `|x| = |y|`; then cancel the equal-length prefixes. -/
theorem append_split_unique {α : Type*} {f : ℕ → ℕ} (hf : StrictMono fun n => n + f n)
    {x u y v : List α} (hu : u.length = f x.length) (hv : v.length = f y.length)
    (h : x ++ u = y ++ v) : x = y ∧ u = v := by
  have hlen := congrArg List.length h
  simp only [List.length_append, hu, hv] at hlen
  have hx : x.length = y.length := hf.injective hlen
  exact ⟨List.append_inj_left h hx, List.append_inj_right h hx⟩

/-- The total length of an input and its exact NP certificate, `n + C·(n + 1)^c`, is
strictly increasing in the input length, including `C = 0` and `c = 0`. -/
theorem certificateLength_strictMono (C c : ℕ) :
    StrictMono fun n : ℕ => n + C * (n + 1) ^ c := by
  intro n m hnm
  exact Nat.add_lt_add_of_lt_of_le hnm
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) c))

/-- **The choice budget.** The exact choice-word length `2a·(n + 1)^c` covers the time
bound `a·(n^c + 1)`, uniformly at `n = 0` and `c = 0`.

**Proof sketch.** `n^c ≤ (n + 1)^c` and `1 ≤ (n + 1)^c`. -/
theorem choiceBudget_le (a c n : ℕ) : a * (n ^ c + 1) ≤ 2 * a * (n + 1) ^ c := by
  have hp := Nat.pow_le_pow_left (Nat.le_succ n) c
  have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c _ (Nat.succ_pos n)
  calc a * (n ^ c + 1) ≤ a * ((n + 1) ^ c + (n + 1) ^ c) :=
        Nat.mul_le_mul_left a (Nat.add_le_add hp h1)
    _ = 2 * a * (n + 1) ^ c := by ring

/-- **Branch truncation** ([AB09, Theorem 2.6]). Let `run` send a choice word to a
configuration, and let halted runs absorb further choices:
`halted (run w) → run (w ++ w') = run w`. If every run along a word of length `t` has
halted, then a word `w` with `t ≤ |w|` runs exactly as its length-`t` prefix, which has
length `t` and has halted.

**Proof sketch.** The prefix has length `t`, so its run has halted; absorption along the
remaining suffix, `w.take t ++ w.drop t = w`, gives the equality. -/
theorem run_take_of_halted {β : Type*} (run : List Bool → β) (halted : β → Prop)
    (habs : ∀ w w' : List Bool, halted (run w) → run (w ++ w') = run w) {t : ℕ}
    (hall : ∀ w : List Bool, w.length = t → halted (run w)) {w : List Bool}
    (hw : t ≤ w.length) :
    (w.take t).length = t ∧ halted (run (w.take t)) ∧ run w = run (w.take t) := by
  have hlen : (w.take t).length = t := List.length_take_of_le hw
  have hp := hall _ hlen
  have h := habs (w.take t) (w.drop t) hp
  rw [List.take_append_drop] at h
  exact ⟨hlen, hp, h⟩

end Turing
