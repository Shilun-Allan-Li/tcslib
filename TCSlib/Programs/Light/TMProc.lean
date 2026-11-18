/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.Renumber
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Regions
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running a Turing machine inside a Light program

For every finite binary Turing machine `M` there is a Light procedure that runs `M` on a bit string
held in memory and writes `M`'s output to memory, within a time linear in `M`'s running time plus
the input length (`Light.exists_tmProc`). The procedure is part of a program `Q` that depends on
`M` only. Placed behind any program with `Program.behind` (`Light/Renumber`), and followed by any
procedures, it keeps its specification, so other programs can call it as a subroutine.

This is the reverse of stage 2 (`WordRAM.exists_simulation`, a word-RAM program run by a Turing
machine). It lets a program call any polynomial-time function given only by a machine, for
instance an abstract operation known to be `PolyTimeComputable`.

## Main results

* `Light.exists_tmProc`: the procedure and its specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.6: Turing machines and their simulation; Exercise
  1.9.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the language Light and its logic (`TCSlib/Programs/Light`).
-/

namespace Light

/-- **A Turing machine as a Light procedure.** For every finite binary machine `M` there are a
program `Q`, a procedure number `p` in it, and constants `A` and `k` such that, wherever `Q` is
placed (behind any program `Pre`, followed by any procedures `Post`), procedure `p + |Pre|`, called
with the arguments `[a, len, b, sc]`, does the following. If the memory holds the input `x` at
`a`, one cell per bit (`0` or `1`), and `M` computes `out` from `x` within `t` steps, then within
`A·(t + len + 1)` steps it returns `|out|`, holds `out` at `b`, one cell per bit, and changes no
cell outside the output's cells and the scratch region of `A·(t + len + 1)` cells at `sc`. The
hypotheses: the regions fit in memory and are pairwise apart; addresses fit in a word; and the
procedure's call depth `k` fits.

`Q`, `p`, `A` and `k` depend on `M` only, so a uniform machine gives a uniform procedure, and a
program calling it stays one program for all inputs.

**Proof sketch.**
- **Encoding.** Keep the state as a number, by `Fintype.equivFin`. Cell values are `0` for blank
  and `1`, `2` for `false`, `true`. Each work tape is laid out in the scratch region with cell `z`
  of tape `j` at an offset determined by `(2|z| + [z < 0])·M.k + j`, so the `t + 1` cells
  reachable in `t` steps fit in `O(M.k·(t + 1))` cells, with no bound needed in advance. Keep the
  heads and the input head as numbers in locals or scratch cells.
- **One step.** Either write the transition table into the scratch region by a constant prologue
  generated from `M`, so that one interpreter is verified once, or emit one code branch per
  `(state, symbols)` case. Each step reads the `M.k + 1` scanned symbols, looks up the action,
  writes and moves, and appends the output bit at `b`, in `O_M(1)` Light steps.
- **The run.** A `while` loop until the state is halted, with the invariant that the memory
  encodes `M.tm.runFrom (M.tm.initCfg x) i` after `i` iterations (the `Turing.Cfg` fields read
  through their published readers). `ComputesInTime` gives the halting time `≤ t` and the output.
- **Placement.** `Ends.shift_append` (`Light/Renumber`) carries the specification from `Q` to
  `Program.behind Pre Q ++ Post`. -/
theorem exists_tmProc (M : Turing.FinTM Bool) :
    ∃ (Q : Program) (p A k : ℕ), ∀ (Pre Post : Program) (lim : Limits) (d : ℕ)
      (a len b sc : ℕ) (μ : ℕ → ℤ) (x out : List Bool) (t : ℕ),
      x.length = len →
      (∀ i < len, μ (a + i) = ((x.getD i false).toNat : ℤ)) →
      M.ComputesInTime x out t →
      (lim.space : ℤ) ≤ lim.word →
      a + len ≤ lim.space → b + out.length ≤ lim.space → sc + A * (t + len + 1) ≤ lim.space →
      Apart a len b out.length → Apart a len sc (A * (t + len + 1)) →
      Apart b out.length sc (A * (t + len + 1)) →
      d + k ≤ lim.depth →
      Meets lim (Program.behind Pre Q ++ Post) (p + Pre.length) d [(a : ℤ), len, b, sc] μ
        (A * (t + len + 1)) fun r μ' =>
          r = out.length ∧ (∀ i < out.length, μ' (b + i) = ((out.getD i false).toNat : ℤ)) ∧
          SameOutside2 μ μ' b out.length sc (A * (t + len + 1)) := by
  sorry

end Light
