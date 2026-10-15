/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalK

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The self-application universal machine `U₀`

[AB09, Exercise 4.1] at self-application: one fixed machine `U₀` that, on an input
`pairEncode α w`, simulates the machine coded by `α` on that same input and reproduces its
output, with a space overhead that is a constant factor depending on `α` only. It is the
universal machine of `Complexity.space_hierarchy`'s window route (`machine-library-design.md`
§16b item 3): a public row built from H2's step block and H5's native device, not a private host
of that proof (`policy.md` §1, *Hosts come first*).

**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). Both statements are the `k = 1` cases of the
`k`-generic `Turing.exists_selfStartupTMK` and `Turing.exists_selfUniversalK`
(`TuringMachine/UniversalK.lean`, U2 statement gate pending; user decision (a), 2026-10-14), and
are proved from them here, with their statements unchanged; the construction, its sketch and its
fill are the generic ones.

## Design

* **Self-application.** The simulated input is all of `U₀`'s input, so the native device serves
  (`Turing.NativeAt`: its left boundary is a real blank) and no input position is stored or
  copied.
* **Forward only.** Halting runs within `s` cells are reproduced within `C_α · (s + 1)` cells;
  nothing is claimed of other runs, which is all the window route uses.
* **Library notions only.** The startup's endpoint is the step block's seam relation written
  out: the table on tape `1`, the unary initial state on tape `2` from cell `2`, the input head
  at `1`, the output empty. Neither statement names a declaration of the H2 promotion (H2-S);
  the prose cites its public names after the move to `Build/StepBlock.lean` (H2-M,
  `Turing.StepBlock.*`). The fill depends on H2-S round 2: the public step block contract, and
  the repaired iteration with its cofinality bound.
* **Generic in the effective scheme**; `Complexity.space_hierarchy` instantiates
  `Complexity.TimeHierarchy.code`.

## Main definitions

None: the module uses existing definitions.

## Main results

* `Turing.exists_selfStartupTM` — the startup, ending at the step block's seam (the `k = 1`
  case of `Turing.exists_selfStartupTMK`).
* `Turing.exists_selfUniversal` — `U₀`, with its forward space ledger (the `k = 1` case of
  `Turing.exists_selfUniversalK`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9: the universal machine and its step;
  Exercise 4.1: the space-bounded universal machine; §4.1.3, Theorem 4.8, whose proof the book
  assigns to Exercise 4.1. The startup and the wrapped rounds are the repository's refinement.)
-/

namespace Turing

/-- **`U₀`'s startup** (the RD-3 gate's check 2). For an effective scheme `c` there is a binary
machine with `K + 3` work tapes and an exit state such that for every code `α` there are a
time `T` and a space bound `B`, **depending on `α` only**, with the following property on every
input `pairEncode α w`. At time `T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before (administrative output suppressed);
* tape `0`, the simulated work tape, blank, and tape `1` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `2` holding the decoded machine's initial state in unary from cell `2` (cells `0` and
  `1` blank), which is the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam for
the decoded machine's initial configuration on the same input (H2's seam relation
`Turing.StepBlock.Rep`, `TuringMachine/Build/StepBlock.lean`, at one coded work tape). [AB09,
§1.4.1, Theorem 1.9]

**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfStartupTMK`, whose
sketch is this construction at `k` mirrored tapes (extract and canonize, install the table and
the unary state, rewind the input head). The generic tape indices `k` and `k + 1` are `1` and
`2`, and `c.toK` decodes to the same machines (`Turing.EffectiveMachineCode.toK_toFinTM`). -/
theorem exists_selfStartupTM (c : EffectiveMachineCode) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 3) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
              else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  obtain ⟨K, P, hP, dP, R, exit, h⟩ := exists_selfStartupTMK 1 c.toK
  refine ⟨K, P, hP, dP, R, exit, fun α => ?_⟩
  obtain ⟨T, B, hT⟩ := h α
  refine ⟨T, B, fun w => ?_⟩
  obtain ⟨hrun, hcut, hout, hspace⟩ := hT w
  refine ⟨?_, hcut, hout, hspace⟩
  rw [hrun]
  congr 1
  funext j
  have m1 : 1 % (K + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  have m2 : 2 % (K + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  have h1 : (j = 1) ↔ j.val = 1 := by
    rw [Fin.ext_iff]; simp [m1]
  have h2 : (j = 2) ↔ j.val = 2 := by
    rw [Fin.ext_iff]; simp [m2]
  by_cases a : j.val = 1
  · simp [h1.mpr a, EffectiveMachineCode.toK_machine]
  · by_cases b : j.val = 2
    · have hne : (2 : Fin (K + (1 + 2))) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp [m1, m2] at this
      simp [h2.mpr b, hne, m2, EffectiveMachineCode.toK_machine]
    · simp [a, b, h1, h2]

/-- **`U₀`, the self-application universal machine** (`Complexity.space_hierarchy`'s sketch;
the sibling of `Complexity.space_universal`, with the native device in place of the
bounded-prefix one). For an effective scheme `c` there is a binary machine `U₀` such that
for every code `α` there is a constant `C > 0` with: whenever the machine coded by `α` halts
on `pairEncode α w` with some output, having visited at most `s` cells, `U₀` halts on the same
input with the same output, having visited at most `C · (s + 1)` cells. Only this forward
direction is claimed; `Complexity.space_hierarchy` instantiates
`c := Complexity.TimeHierarchy.code`. [AB09, Exercise 4.1, forward clause, at self-application;
§4.1.3, Theorem 4.8]

Deviation: `C` depends on the code `α` (as in `Turing.universal`), and the input is the coded
machine's own input (self-application), so no copy and no position counter is needed.

**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfUniversalK`, whose
sketch is this construction at `k` mirrored tapes (the startup, then H2-F's forwarding round loop
`Turing.StepBlock.exists_forwardLoopTM`, the wrapped rounds with the reset invariant, made a public
host). Its forward clause gives the halting run within `C · (t + 1)` steps, so `t' := C · (t + 1)`,
and the space `≤ C · (spaceUsed + 1) ≤ C · (s + 1)`; its time clause and converse are dropped. -/
theorem exists_selfUniversal (c : EffectiveMachineCode) :
    ∃ U₀ : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (c.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (c.decode α).toFinTM.tm.spaceUsed
            ((c.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
          ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
            U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1) := by
  obtain ⟨U, hU⟩ := exists_selfUniversalK 1 c.toK
  refine ⟨U, fun α => ?_⟩
  obtain ⟨C, hC, h⟩ := hU α
  refine ⟨C, hC, fun w output t s hrun hs => ⟨C * (t + 1), ((h w).1 output t hrun).1, ?_⟩⟩
  have hsp := ((h w).1 output t hrun).2
  rw [EffectiveMachineCode.toK_toFinTM] at hsp
  exact hsp.trans (Nat.mul_le_mul_left C (by omega))

end Turing
