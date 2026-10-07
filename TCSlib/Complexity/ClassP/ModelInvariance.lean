/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# "And why it doesn't matter": model invariance of DTIME and P

The payoff of the robustness theorems ([AB09, §1.3.1], formalized in
`TCSlib.Complexity.TuringMachine.Robustness`), stated at the strength the theorems
actually deliver (phase-2 audit, finding 4): **alphabet size** never matters —
`DTIME` is alphabet-invariant, the alphabet-dependent constant being absorbed by
`DTIME`'s own existential — while **the number of work tapes** does not matter *for
`P`*, where the quadratic overhead of tape reduction is harmless. No invariance of a
fixed class `DTIME T` under tape reduction is claimed, and [AB09, §1.6.1] likewise
draws only the polynomial-time conclusion. This is the formal content of the
chapter's title at class level.

## Main definitions

* `Turing.FinTM.DecidesInTimeVia` — a machine over a larger alphabet decides a binary
  language via a symbol embedding.

## Main results

* `Complexity.mem_DTIME_of_decidesInTimeVia` — deciding over any finite alphabet lands
  in binary `DTIME` (constant absorbed). [AB09, Claim 1.5 for languages]
* `Complexity.mem_P_of_decidesInTimeVia_poly` — `P` is alphabet-invariant.
* `Complexity.mem_P_iff_one_work_tape` — `P` is exactly what one-work-tape binary
  machines decide in polynomial time. [AB09, Claims 1.5-1.6 for `P`]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3.1; §1.6.1 "Why the model may not matter".)
-/

namespace Turing.FinTM

/-- The machine `M`, over alphabet `Γ`, decides the binary language `L` via the symbol
embedding `e : Bool ↪ Γ` within time `T`: on every input `x.map e` it halts within
`T |x|` steps with output `[e b]` where `b` is the membership bit of `x` in `L`. -/
def DecidesInTimeVia {Γ : Type} (M : FinTM Γ) (e : Bool ↪ Γ) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (x.map e)
      [e (MultiTapeTM.indicator (L : Set (List Bool)) x)] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- Deciding a language over *any* finite alphabet puts it in the binary-machine class
`DTIME` (with the alphabet-dependent constant absorbed by `DTIME`'s existential).

**Proof sketch.** `DecidesInTimeVia` is `ComputesFunInTimeVia` for the function
`x ↦ [indicator L x]` (note `[b].map e = [e b]`); apply
`Turing.FinTM.alphabet_reduction` and absorb its constant `c` into `DTIME`'s. -/
theorem mem_DTIME_of_decidesInTimeVia {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} {T : ℕ → ℕ}
    (h : M.DecidesInTimeVia e L T) :
    L ∈ DTIME fun n => T n + 1 := by
  obtain ⟨c, M', -, hM'⟩ := FinTM.alphabet_reduction e M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T
    (fun x => by simpa using h x)
  exact ⟨c, M', fun x => hM' x⟩

/-- **`P` is alphabet-invariant**: a language decided in polynomial time by a machine
over any finite alphabet is in `P`.

**Proof sketch.** `Complexity.mem_DTIME_of_decidesInTimeVia` gives
`L ∈ DTIME (C · (n + 1) ^ d + 1)`; conclude with `Complexity.mem_P_of_dtime_le`
(pointwise bound `C · (n + 1) ^ d + 1 ≤ (C + 1) · 2 ^ d · (n ^ d + 1)`, using
`(n + 1) ^ d ≤ 2 ^ d (n ^ d + 1)` from the `mem_P_iff` arithmetic). -/
theorem mem_P_of_decidesInTimeVia_poly {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} (C d : ℕ)
    (h : M.DecidesInTimeVia e L fun n => C * (n + 1) ^ d) :
    L ∈ P := by
  have h1 := mem_DTIME_of_decidesInTimeVia e h
  refine mem_P_of_dtime_le h1 ((C + 1) * 2 ^ d) d fun n => ?_
  have h2 : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
  calc C * (n + 1) ^ d + 1
      ≤ C * (n + 1) ^ d + (n + 1) ^ d := Nat.add_le_add_left h2 _
    _ = (C + 1) * (n + 1) ^ d := by ring
    _ ≤ (C + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul (le_refl _) (succ_pow_le n d)
    _ = (C + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **`P` is tape-count-invariant**: `P` is exactly the class of languages decided by
binary machines with a *single* work tape in polynomial time. [AB09, Claim 1.6 at the
level of `P`; quadratic slowdown preserves polynomiality]

**Proof sketch.** Backward: a one-work-tape polynomial decider is in particular a
polynomial decider (`Complexity.mem_P_iff`). Forward: from `mem_P_iff` take a decider
within `C · (n + 1) ^ d`; `DecidesInTime` is `ComputesFunInTime` for
`x ↦ [indicator L x]`, so `Turing.FinTM.one_work_tape_binary` yields a one-work-tape
binary machine within `c · (C · (n + 1) ^ d + 1)² ≤ C' · (n + 1) ^ (2d)`, again of the
`mem_P_iff` shape. -/
theorem mem_P_iff_one_work_tape {L : Language Bool} :
    L ∈ P ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.k = 1 ∧ M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
    obtain ⟨M', c, hk, hM'⟩ := FinTM.one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
      (fun n => C * (n + 1) ^ d) hM
    refine ⟨M', c * (C + 1) ^ 2, d * 2, hk, fun x => (hM' x).mono ?_⟩
    have h2 : 0 < (x.length + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
    calc c * (C * (x.length + 1) ^ d + 1) ^ 2
        ≤ c * ((C + 1) * (x.length + 1) ^ d) ^ 2 := by
          refine Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left ?_ 2)
          calc C * (x.length + 1) ^ d + 1
              ≤ C * (x.length + 1) ^ d + (x.length + 1) ^ d :=
                Nat.add_le_add_left h2 _
            _ = (C + 1) * (x.length + 1) ^ d := by ring
      _ = c * (C + 1) ^ 2 * ((x.length + 1) ^ d) ^ 2 := by ring
      _ = c * (C + 1) ^ 2 * (x.length + 1) ^ (d * 2) := by rw [pow_mul]
  · rintro ⟨M, C, d, -, hM⟩
    exact mem_P_iff.mpr ⟨C, d, M, hM⟩

end Complexity
