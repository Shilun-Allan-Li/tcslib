/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Iterating a polynomial-time step polynomially often

Infrastructure for [AB09 §7.2]; not itself a result of the book. The arithmetic algorithms of
§7.2 (repeated squaring, Euclid, the Jacobi-symbol recursion, long division) all have the
shape "run a polynomial-time step a polynomial number of times on a state of polynomially
bounded length". This file proves that this shape is polynomial-time, and gives the
measure argument used to show that such a loop has reached its fixed point.

## Main definitions

* `Complexity.BinArith.guardNxt`, `Complexity.BinArith.guardLoop` — the guarded round and the
  guarded countdown loop.
* `Complexity.BinArith.SlotsLe` — the slot-length bound keeping its orbits linear.

## Main results

* `Complexity.BinArith.polyTimeComputable_iterate` — if `g` and `init` are polynomial-time
  and the orbit `g^[i] (init z)`, `i ≤ a(|z|+1)^k`, stays inside `B(|z|+1)^b`, then
  `z ↦ g^[a(|z|+1)^k] (init z)` is polynomial-time.
* `Complexity.BinArith.iterate_measure_eq_zero` — a measure that strictly drops on every
  non-fixed state of an invariant reaches `0` within its initial value many steps.

## Implementation notes

The loop is `Complexity.BlockLoop.step` (the shared countdown loop of
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`) on the state
`⟨[1], ⟨1^T, ⟨1^U, s⟩⟩⟩`: the countdown `1^T` counts the rounds, and the unary marker `1^U`
guards each round, which replaces `s` by `g s` only if `|g s| ≤ U`. The guard keeps every
orbit of the loop, from every word, inside a linear envelope (the hypothesis
`Complexity.polyTimeComputable_emitIter` needs), while on the genuine orbit the length
hypothesis makes it inert.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing

/-! ### Measure arguments for loops -/

/-- An invariant of `g` holds along the whole orbit (the special case of Mathlib's
`Function.Iterate.rec` used throughout this development). -/
theorem iterate_invariant {α : Type} {g : α → α} (I : α → Prop) (hI : ∀ s, I s → I (g s))
    (n : ℕ) {s : α} (hs : I s) : I (g^[n] s) := by
  induction n with
  | zero => exact hs
  | succ n ih => rw [Function.iterate_succ_apply']; exact hI _ ih

/-- **Loops reach their fixed point.** Let `I` be an invariant of `g` and `μ` a measure
that strictly drops on every state of `I` with `μ > 0`, while states with `μ = 0` are fixed.
Then `n ≥ μ s` iterations from a state `s` of `I` end in a state of measure `0`. -/
theorem iterate_measure_eq_zero {α : Type} {g : α → α} (I : α → Prop) (μ : α → ℕ)
    (hI : ∀ s, I s → I (g s)) (hdec : ∀ s, I s → 0 < μ s → μ (g s) < μ s)
    (hfix : ∀ s, I s → μ s = 0 → g s = s) :
    ∀ (n : ℕ) (s : α), I s → μ s ≤ n → μ (g^[n] s) = 0 := by
  intro n
  induction n with
  | zero => intro s _ h; simpa using h
  | succ n ih =>
    intro s hs h
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos (μ s) with h0 | h0
    · rw [hfix s hs h0]; exact ih s hs (by omega)
    · exact ih (g s) (hI s hs) (by have := hdec s hs h0; omega)

/-! ### The guarded countdown loop -/

/-- One guarded round on the remainder `⟨u, s⟩`: replace `s` by `g s` when `|g s| ≤ |u|`. -/
def guardNxt (g : List Bool → List Bool) (_h r : List Bool) : List Bool :=
  pairEncode (pairFstD r)
    (if (g (pairSndD r)).length ≤ (pairFstD r).length then g (pairSndD r) else pairSndD r)

/-- The guarded loop: the countdown loop with constant head and the round `guardNxt g`. -/
def guardLoop (g : List Bool → List Bool) : List Bool → List Bool :=
  BlockLoop.step (fun h _ => h) (guardNxt g)

/-- The four slots of a loop state (head, countdown, marker, payload) are no longer than `L`. -/
def SlotsLe (L : ℕ) (W : List Bool) : Prop :=
  (pairFstD W).length ≤ L ∧ (pairFstD (pairSndD W)).length ≤ L ∧
    (pairFstD (pairSndD (pairSndD W))).length ≤ L ∧
    (pairSndD (pairSndD (pairSndD W))).length ≤ L

/-- Every slot of a word is no longer than the word. -/
theorem slotsLe_self (W : List Bool) : SlotsLe W.length W := by
  have h1 := length_pairSndD_le W
  have h2 := length_pairSndD_le (pairSndD W)
  refine ⟨length_pairFstD_le W, ?_, ?_, ?_⟩
  · exact (length_pairFstD_le _).trans h1
  · exact (length_pairFstD_le _).trans (h2.trans h1)
  · exact (length_pairSndD_le _).trans (h2.trans h1)

/-- A round of the guarded loop either stops or keeps head and marker, shortens the
countdown and applies the guard to the payload. -/
theorem guardLoop_cases (g : List Bool → List Bool) (W : List Bool) :
    guardLoop g W = blockDone ∨
      guardLoop g W = pairEncode (pairFstD W) (pairEncode ((pairFstD (pairSndD W)).drop 1)
        (guardNxt g (pairFstD W) (pairSndD (pairSndD W)))) := by
  unfold guardLoop BlockLoop.step
  split_ifs
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The guarded round preserves the slot bound. -/
theorem slotsLe_guardLoop (g : List Bool → List Bool) {L : ℕ} {W : List Bool}
    (h : SlotsLe L W) : SlotsLe L (guardLoop g W) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases guardLoop_cases g W with hW | hW <;> rw [hW]
  · simp [SlotsLe, blockDone, pairFstD_nil, show pairSndD [] = [] from rfl]
  · simp only [SlotsLe, guardNxt, pairFstD_pairEncode, pairSndD_pairEncode, List.length_drop]
    refine ⟨h1, by omega, h3, ?_⟩
    split_ifs with hg
    · exact hg.trans h3
    · exact h4

/-- The output of a guarded round has length at most `7L + 6` when its input's slots are
bounded by `L`. -/
theorem length_guardLoop_le (g : List Bool → List Bool) {L : ℕ} {W : List Bool}
    (h : SlotsLe L W) : (guardLoop g W).length ≤ 7 * L + 6 := by
  have h' := slotsLe_guardLoop g h
  rcases guardLoop_cases g W with hW | hW
  · rw [hW]; simp [blockDone, length_pairEncode]
  · obtain ⟨h1, h2, h3, h4⟩ := h'
    rw [hW] at h1 h2 h3 h4 ⊢
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, guardNxt] at h1 h2 h3 h4
    simp only [guardNxt, length_pairEncode]
    omega

/-- Every orbit of the guarded loop stays inside the linear envelope `7(|w| + 1)`. -/
theorem length_iterate_guardLoop_le (g : List Bool → List Bool) (w : List Bool) (i : ℕ) :
    ((guardLoop g)^[i] w).length ≤ 7 * (w.length + 1) ^ 1 := by
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply']
    have := length_guardLoop_le g
      (iterate_invariant (g := guardLoop g) (SlotsLe w.length) (fun _ h => slotsLe_guardLoop g h) i
        (slotsLe_self w))
    rw [pow_one]; omega

/-- The guarded round is polynomial-time when `g` is. -/
theorem polyTimeComputable_guardLoop {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (guardLoop g) := by
  have hr : PolyTimeComputable (fun W => pairSndD (pairSndD W)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hu : PolyTimeComputable (fun W => pairFstD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairFstD.comp hr
  have hs : PolyTimeComputable (fun W => pairSndD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairSndD.comp hr
  have hgs : PolyTimeComputable (fun W => g (pairSndD (pairSndD (pairSndD W)))) := hg.comp hs
  have htest : PolyTimeComputable (fun W => [decide
      ((g (pairSndD (pairSndD (pairSndD W)))).length ≤
        (pairFstD (pairSndD (pairSndD W))).length)]) := by
    have := polyTimeComputable_lenLe.comp (hu.pairEncode hgs)
    simpa [Function.comp_def] using this
  refine BlockLoop.polyTimeComputable_step rfl polyTimeComputable_pairFstD ?_
  have := hu.pairEncode (polyTimeComputable_ite htest hgs hs)
  simpa [guardNxt] using this

/-- **Iterating a polynomial-time step polynomially often is polynomial-time**
(infrastructure for [AB09 §7.2]; not itself a result of the book). If `g` and `init` are
polynomial-time and every state `g^[i] (init z)` with `i ≤ a(|z|+1)^k` has length at most
`B(|z|+1)^b`, then `z ↦ g^[a(|z|+1)^k] (init z)` is polynomial-time.

**Proof sketch.** Run the countdown loop `Complexity.BlockLoop.step` from
`⟨[1], ⟨1^T, ⟨1^U, init z⟩⟩⟩` with `T = a(|z|+1)^k`, `U = B(|z|+1)^b`, and the guarded
round `guardNxt g`, which applies `g` only when the result fits in `U`. The guard bounds
every orbit from every word by `7(|w|+1)` (`length_iterate_guardLoop_le`), as
`Complexity.BlockLoop.polyTimeComputable_of_loop` requires; on the genuine orbit the length
hypothesis makes the guard pass, so after `T` rounds the payload is `g^[T] (init z)`, which
the loop's single emission (`Complexity.BlockLoop.loop_output`) outputs. -/
theorem polyTimeComputable_iterate {g init : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hinit : PolyTimeComputable init) (a k B b : ℕ)
    (hbound : ∀ z i, i ≤ a * (z.length + 1) ^ k →
      (g^[i] (init z)).length ≤ B * (z.length + 1) ^ b) :
    PolyTimeComputable (fun z => g^[a * (z.length + 1) ^ k] (init z)) := by
  -- the remainder `⟨1^U, init z⟩` and the loop's initial state
  have hr : PolyTimeComputable
      (fun z => pairEncode (List.replicate (B * (z.length + 1) ^ b) true) (init z)) :=
    (polyTimeComputable_polyUnary B b).pairEncode hinit
  have hstart := BlockLoop.polyTimeComputable_countdownInit [true] polyTimeComputable_id hr a k
  have hout : PolyTimeComputable (fun W => pairSndD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  refine BlockLoop.polyTimeComputable_of_loop (polyTimeComputable_guardLoop hg)
    (BlockLoop.polyTimeComputable_emit hout) hstart 1 1 7
    (length_iterate_guardLoop_le g) (fun z => ?_)
  -- the loop's output is the payload after `T` guarded rounds
  set T := a * (z.length + 1) ^ k
  set U := List.replicate (B * (z.length + 1) ^ b) true
  have hK : T < 1 * ((pairEncode [true] (pairEncode (List.replicate (a * ((id z).length + 1) ^ k)
      true) (pairEncode U (init z)))).length + 1) ^ 1 + 1 := by
    simp only [id, length_pairEncode, List.length_replicate, pow_one, one_mul]
    omega
  have hstep : guardLoop g = BlockLoop.step (fun h _ => h) (guardNxt g) := rfl
  rw [BlockLoop.loop_output hstep (fun _ => [true]) (fun i => pairEncode U (g^[i] (init z)))
    (by simp [T]) (fun _ _ => List.cons_ne_nil _ _) (fun _ _ => rfl) (fun i hi => ?_) hK]
  · simp
  · have hb := hbound z (i + 1) (by omega)
    rw [Function.iterate_succ_apply'] at hb
    simp only [guardNxt, pairFstD_pairEncode, pairSndD_pairEncode, U, List.length_replicate,
      Function.iterate_succ_apply', if_pos hb]

end BinArith

end Complexity
