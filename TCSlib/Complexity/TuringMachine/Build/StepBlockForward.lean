/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step block's forwarding round loop (H2-F)

**Status: statement gate passed** (2026-10-15, `audits/u2-statements-findings.md`: PASS,
0 blockers, 0 majors, 2 minors; resolutions `audits/u2-statements-resolutions.md`). The contract
`Turing.StepBlock.exists_forwardLoopTM` is sorried with its proof sketch; the encoding is defined.

**H2's unclocked loop form** (host H2, `machine-library-design.md` §14): the step block
`Turing.StepBlock.roundTM` followed by a forwarding leaf, run until the simulated machine halts.
One finite machine per work-tape count `k` simulates any `k`-work-tape binary transition table,
held as data in the `Turing.tableBitsK` layout, in macro-step lockstep (`Turing.Lockstep`) through
the encoding `Turing.StepBlock.forwardLoopCfg`, forwarding each simulated emission to its own
output, with a per-step cost bounded by the table's length and a per-head space ledger. It is the
loop of the `k`-generic universal machine U2 (`TCSlib.Complexity.TuringMachine.UniversalK`;
design note `audits/evidence/u2/U2-design.md` §2.2), and of B6's `U₀` at `k = 1`.

H2's clocked loop form, the counter loop over the step block, is
`TCSlib.Complexity.TuringMachine.Build.StepBlockLoop`. The forwarding form has its own module
(user, 2026-10-15) so that the clocked form's consumers, `CodeSimulator` among them, do not depend
on it.

## Main definitions

* `Turing.StepBlock.forwardLoopCfg` — H2-F's encoding of a source configuration.

## Main results

* `Turing.StepBlock.exists_forwardLoopTM` — H2-F, the forwarding round loop: a macro-step
  lockstep of any `k`-tape table with its emissions forwarded, per-step cost
  `≤ 50 · (|table| + 1) + C`, and the space ledger (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, proof of Theorem 1.9.)
-/

namespace Turing

namespace StepBlock

/-! ## The forwarding round loop (H2-F) -/

/-- **The forwarding round loop's configuration for a source configuration** (H2-F's encoding):
for a `k`-work-tape binary machine `M` with `n + 1` states and a configuration `c` of `M` on the
input `x`, the `(k + 2)`-tape configuration whose input head and mirrored tapes `0, …, k - 1`
(contents and heads) are `c`'s, whose tape `k` holds the table `tableBitsK M.tr` and tape
`k + 1` the blank summary cell followed by the unary current state (empty when `c` is halted),
both auxiliary heads at `0`, whose output is `c`'s output, and whose control is `entry` while
`c` is live and halted once `c` is. It is the step block's seam relation `Turing.StepBlock.Rep`
for `c` with its output erased (so the summary cell is blank), with the physical output
restored: the reset invariant of `Turing.exists_selfUniversal`'s sketch (the H2-S gate's
finding 4). [AB09, §1.4.1, proof of Theorem 1.9] -/
def forwardLoopCfg {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Cfg (k + 2) Bool Q x where
  state := c.state.map fun _ => entry
  inputPos := c.inputPos
  workTapes := Fin.addCases (motive := fun _ => ℤ → Option Bool) c.workTapes fun j =>
    if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
    else summaryCells none ((c.state.map unaryFin).getD [])
  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0
  output := c.output

/-- **H2-F, the forwarding round loop** (host H2's unclocked loop form; `machine-library-design.md`
§14; U2 design note `audits/evidence/u2/U2-design.md` §2.2). For each work-tape count `k` there
is one finite `(k + 2)`-tape binary machine `L`, with an entry state and a constant `C`, such
that for every `k`-work-tape binary machine `M` with `n + 1` states and every input `x`, `L`
simulates `M` step by step through `forwardLoopCfg`: there is a cost function on `M`'s
configurations with
* **a macro-step lockstep** (`Turing.Lockstep`, exits `{none}` on both sides): from the encoding
  of a live configuration `c`, `L` reaches the encoding of `M.step c` after exactly `cost c`
  steps, without halting before; the encoding of a halted configuration is halted. So `L` halts
  exactly when `M` does, with `M`'s output, which it emits step by step
  (`Turing.Lockstep.runFrom`, `Turing.Lockstep.cut`);
* **a per-step bound**: `0 < cost c ≤ 50 · (|tableBitsK M.tr| + 1) + C` for live `c`, a constant
  for a fixed table (the step block's bound plus the leaf's);
* **a space ledger**: over `t` source steps that are live before `t`, each mirrored head visits
  only cells that `M`'s head visits, and the two auxiliary heads stay within
  `50 · (|tableBitsK M.tr| + 1) + C` of their home.

The control of `L` does not depend on `M`, `n` or `x`. [AB09, §1.4.1, proof of Theorem 1.9:
each step of `M` is simulated in a number of steps depending only on `M`'s table]

**Proof sketch.** `L` is the step block `roundTM k` followed, at either of its exits, by a
forwarding leaf on the summary tape: read the summary cell, emit its bit if it holds one, blank
it, then return to the block's entry (exit `entry`) or halt (exit `halt`). For a live `c`, the
block-control part of `forwardLoopCfg entry M c` represents `{c with output := []}` (`Rep`: a blank
summary, the unary state word, both auxiliary heads home), so `roundTM_effect` gives a first exit
after `T ≤ 50 · (|tableBitsK M.tr| + 1)` steps at the representation of
`a.apply {c with output := []}`, silent before, with summary cell
`summaryEmit none a.output = a.output` (`summaryEmit_none`); the exit time is unique
(`roundTM_firstExit_unique`). The leaf emits `a.output`, making the physical output
`(a.apply c).output`, blanks the cell, and enters `entry` or halts according to the exit: the
result is exactly `forwardLoopCfg entry M (M.step c)`. Take `cost c` the block's exit time plus the
leaf's length (at most `C`); the inner times are live by the block's cut and the leaf's. The space
ledger is `roundTM_visited` per round, summed by `MultiTapeTM.visitedByTapeHead_add_subset`; the
leaf moves no head. -/
theorem exists_forwardLoopTM (k : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM (k + 2) Bool Q)
      (entry : Q) (C : ℕ),
      ∀ {n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ cost : Cfg k Bool (Fin (n + 1)) x → ℕ,
          Lockstep M L (forwardLoopCfg entry M) cost {none} {none} ∧
          (∀ c, c.state ≠ none → 0 < cost c ∧
            cost c ≤ 50 * ((tableBitsK M.tr).length + 1) + C) ∧
          ∀ (c : Cfg k Bool (Fin (n + 1)) x) (t : ℕ), (∀ u < t, (M.runFrom c u).state ≠ none) →
            (∀ i : Fin k, L.visitedByTapeHead (forwardLoopCfg entry M c)
                (∑ u ∈ Finset.range t, cost (M.runFrom c u)) (Fin.castAdd 2 i) ⊆
              M.visitedByTapeHead c t i) ∧
            ∀ j : Fin (k + 2), k ≤ j.val →
              L.visitedByTapeHead (forwardLoopCfg entry M c)
                  (∑ u ∈ Finset.range t, cost (M.runFrom c u)) j ⊆
                Finset.Icc (-((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ))
                  ((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ) := by
  sorry

end StepBlock

end Turing
