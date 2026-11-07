# MIG-1 megafill — checkpoint cp02 (F-A complete) — PARTIAL

Agent: Claude (Anthropic). Branch `fill/mig1-mega` from exactly
`83ac315ed9e7089466bd16a32f3b71fbadc556d2`; records `7df0d047d501a1d08982d17d20208faf49d39131`.
Commits: `COMMITS.txt` (2 commits: F-A 1/2 = cp01, F-A 2/2). Verdict: **partial (checkpoint)**.

## Checkpoints reached
cp01 (same-home group) and **cp02: all nine F-A specs proved**, rows re-pointed.

## F-A targets
| Target | Status |
|---|---|
| `Turing.FinTM.idTM_computes` | proved (Composition) |
| `Turing.FinTM.ifEqTM_computes` | proved (Composition) |
| `Turing.FinTM.condTM_computes_iff` | proved (Composition) |
| `Turing.FinTM.branchTM_spaceUsed` | proved (Simulation) |
| `Turing.FinTM.timedCondTM_computes` | proved (Wrappers) |
| `Turing.FinTM.timedCondTM_spaceUsed` | proved (Wrappers) |
| `Turing.pairDiagTM_computes` | proved (Encoding) |
| `Turing.FinTM.lengthBitsTM_computes` | proved (TimeConstructible) |
| `Turing.FinTM.lengthBitsTM_spaceUsed` | proved (TimeConstructible) |

Axioms (fresh, `evidence/logs/axioms/Ax_cp02.*`): all 22 checked names (9 specs + 13 changed public
proofs) depend only on `propext`, `Classical.choice`, `Quot.sound`.

Remaining exact obligations after cp02: Loop `loopHostTM_contracts`, `loopHostTM_decides`,
`loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes` (F-C); Primitives
`polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes` and the three forwarding
exports (F-B); all F-D retirements. Frozen RAM admissions (unchanged, out of scope):
`WordRAM.WordSizeComputable.mono`, `WordRAM.wordSizeComputable_logSpace`,
`WordRAM.wordSizeComputable_of_spaceConstructible`. Static count `static-sorry-cp02.log`: 20 → 11.

## Moved private material (original → final home)
| Catalog source (deleted in F-D) | Final home / replacement |
|---|---|
| `f2_branch_space`, `f2_sum_add`, `f2_finSumEquiv` | `Simulation.branchTM_spaceUsed` with `Fin.sum_univ_add` (no copy of the equivalence) |
| `f2_cond_space` | `Wrappers.timedCondTM_spaceUsed` |
| `f2_cond_ledger`, `f2_condHeads`, `f2_control_heads`, `f2_branch_heads`, `f2_read_heads` | `Wrappers.timed_ledger`, `timedHeads`, `timed_control_heads`, `timed_branch_heads`, `timed_read_heads` (+ new private `timedReadyCfg_workTapePos`, `timedReady_dispatch`) |
| `f2_counter_count_space`, `f2_counter_heads`, `f2_counter_space` | merged into `TimeConstructible.counter_count` (strengthened in place), `lengthBitsTM_spaceUsed`; new private `counter_emit_start`, `counter_halt` shared by time and space |
| `f2_head_steps` | replaced by the published `MultiTapeTM.workTapePos_runFrom_mem_Icc` |
| `f2_cond_time`, `f2_counter_computes` copies | replaced by the specs (deletion in F-D) |

## Assigned MIG-24 factoring (dispositions so far)
- **T1 (Simulation part): done** — private `rewind_first_step` shared by `rewind_from_any`,
  `timed_rewind`, `rewind_heads` (relative order frozen, so no public lemma became a corollary of a
  later one). Loop/Primitives parts follow in F-C/F-B.
- **T4: done** — `exists_comp_partial`, `computesFunInTime_comp`, `exists_comp_on_image` are now
  one-line corollaries of `bufferedCompTM_computes_iff`, `_computesFunInTime`, `_on_image`.
- **T7 (Simulation/Encoding singletons), inspected:** `bufferedSecondCfg_run` ↔
  `VirtualInput.vhostEmitTM_runFrom` are two lockstep hosts in different files; unifying them needs
  a new public interface (`Turing.Lockstep`-style), so no change (gap recorded, no new debt).
  `Encoding.toCodeTM_computesInTime_iff` ↔ `exists_codeTM_spaceUsed` (49%): different statements
  sharing the relabeling scaffold; no change.

## Rule-10 seal (fresh, `evidence/seal/`)
- Sealed copies, each changed/new F-A declaration in its own section with
  `attribute [local irreducible]` on the foreign TCSlib definitions reached and
  `attribute [-simp]` on the `@[simp]` definitions `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`:
  Composition, Encoding, TimeConstructible, Simulation, Wrappers — all **exit 0, 0 errors**
  (`Seal_*.out`). Earlier attempts (`*-try*`) are retained; they found definitional reads that were
  then replaced by published equations (`Cfg.init_*`, `initCfg_eq`, `runFrom_succ_eq_step`,
  `runFrom_zero`, `Cfg.workTapeSymbols_eq`).
- Sealed set: `core-list.txt` (14 core definitions) plus `simulation-list-v3.txt` (5) for non-
  Simulation homes. **Unsealable / not sealed, inventoried:** `Cfg.Halted` (reducible abbrev);
  `Turing.FinTM.branchTM`, `leftCfg`, `rightCfg` for the Composition and Wrappers homes. `branchTM`'s
  tape count and state type are read definitionally in *types* (`(branchTM M₁ M₂ b).k` as
  `M₁.k + M₂.k`), which no equation can replace. `leftCfg`/`rightCfg` have **no published field
  equations**; see escalation E1.
- Paired controls: `controls/ControlsUnsealed` (38 examples, exit 0, 0 errors) and
  `controls/ControlsSealed` (38 examples = pointwise + abstracted for each of 19 sealed definitions,
  exit 1, exactly 38 errors). Multiplicity checker `tools/ctlcheck.py`: both PASS; its negative
  controls (duplicate diagnostic, missing diagnostic, zero exit) all FAIL as required
  (`check-neg-*.txt`).
- Argument inspection `seal/argscan/*.txt`: the only foreign definitions passed to
  `simp`/`rw`/`unfold`/`show`/`change` in the changed regions are `leftCfg`/`rightCfg`
  (Composition 1, Wrappers 6) — E1.

## Escalations
- **E1 (missing public statements, Simulation).** Field equations for the block embeddings, needed
  to read `leftCfg`/`rightCfg` from other files without unfolding:
  `Turing.FinTM.rightCfg_state : (rightCfg f c tapes heads).state = c.state.map f`,
  `rightCfg_output : (rightCfg f c tapes heads).output = c.output`,
  `rightCfg_inputPos`, `rightCfg_workTapePos : (rightCfg f c tapes heads).workTapePos =
  Fin.addCases heads c.workTapePos` and the four `leftCfg_*` analogues (a `simps` attribute would
  generate them). Not added (no public addition authorized); the moved proofs keep the base's
  existing `simp [leftCfg, rightCfg]` reads.

## Imports
Approved `Mathlib.Algebra.BigOperators.Fin` added to Simulation. No other import change.

## Fresh checks in this zip
Everything in cp01, plus: `elab/fa*.summary`, `elab/cp02pre.summary` (edited chain, all exit 0);
`bootstrap-cp02/summary.log` (all 51 bootstrap modules at the cp02 commit, failed=0; Loop's later
F-C edits were made after the sweep compiled Loop at 07:55:11Z and are *not* in this commit);
`axioms/Ax_cp02.*`; `freeze-cp02.log` (PASS; the one import change is the approved one);
`static-sorry-cp02.log`.

## NOT RUN at cp02
Unfiltered compiled non-private census, copy-text screens, 641-module final sweep, policy lint.
