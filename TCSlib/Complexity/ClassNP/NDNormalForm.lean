/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear-overhead coded normal form of an NDTM

[AB09, §3.2] ([BGW70]-style guess-then-verify): every bundled binary nondeterministic machine has a
coded two-work-tape equivalent (`Turing.CodeNDTM`) whose acceptance tracks the original's at linear
time overhead, forward with an explicit constant and backward in unbounded form. The
nondeterministic time hierarchy (`TCSlib.Complexity.Diagonalization.NTimeHierarchy`) diagonalizes
over these codes. The statement was gated with phase P3.3's statements and lived in that module. It
moved here unchanged (user, 2026-10-17; C1's fill plan, `audits/evidence/c1/C1-fill-plan.md`), so
that its fill can run beside the universal machine's in `NTimeHierarchy`.

## Main definitions

No new definitions: the normal form is an existential contract.

## Main results

* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded normal form (sorried;
  phase P3.3).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; no external text is required.)
-/

namespace Turing

namespace FinNDTM

/-- **The linear-overhead coded normal form** ([BGW70]-style guess-then-verify,
cited through [AB09, §3.2]; spec, fill pending — phase P3.3): every
nondeterministic machine has a coded (two-work-tape) equivalent whose
acceptance tracks the original's at linear time overhead — forward with the
explicit constant, backward in unbounded form (the consumer recovers the
budgeted form from the original's all-branch halting by the truncation
argument, `Turing.NDTM.runWith_of_halt`).

**Proof sketch.** Guess-then-verify, the reason codes carry **two** work
tapes: on tape A the simulator guesses, left to right and one choice bit per
guessed bit, the full display sequence of a `k`-tape run of `N` — per step
the choice bit, the state, the `k + 1` scanned symbols, and the action record
(`O_N(1)` cells per step) — checking the **control-local** part on the fly
(each record must follow from its predecessor by `N`'s table, hardwired in
the simulator's finite control). Then the non-local reads are verified in
`k + 1` sweeps: the input claims by replaying the claimed input-head moves
against the real input tape, and each work tape `j` by replaying tape `j` on
tape B — B's head tracks tape `j`'s claimed head, so each step checks the
claimed read against B's cell and applies the claimed write at unit cost —
rewinding A and clearing B between sweeps. Total `O_N((k+1)·(t+1)) =
C·(t+1)` — the `k+1` covers the zero-work-tape case, where the display
guess and the input sweep remain (round-1 finding 6).
Forward transfer: a genuine accepting run of length `t` yields the accepting
display, guessed and verified within `C·(t+1)`. Backward: a verified display
**is** a genuine run (the sweeps force consistency), so an accepting branch
of the simulator exhibits an accepting branch of `N` at some length —
unbounded on purpose: runaway guessing branches never accept, and no
all-branch-halting claim is made for the simulator. State-space finiteness
packages as `Fin` by the relabeling `Turing.NDTM.relabelState` (the
nondeterministic mirror of `Turing.MultiTapeTM.relabelState`, as in the
`exists_codeTM` precedent). Fill obligations, named: the display format and
its on-the-fly control check; the `k + 1` verification sweeps; the two
transfer directions; the relabeling packaging. -/
theorem exists_codeNDTM_accepts_linear (N : FinNDTM Bool) :
    ∃ (M : CodeNDTM) (C : ℕ),
      (∀ (x : List Bool) (t : ℕ),
        N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))) ∧
      (∀ (x : List Bool) (t : ℕ),
        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  sorry

end FinNDTM

end Turing
