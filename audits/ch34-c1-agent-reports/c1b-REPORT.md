# C1b delivery: zero space, parity in L, and the reachable-register run bound

**13/13 targets proved. Proved-modulo set: empty. Escalations: none.**
The two required public exports are proved as well. There are no remaining
`sorry` terms in the three owned modules, and none of the 15 axiom prints
uses `sorryAx`.

## Base, branch, and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Checked-out campaign branch: `complexity/arora-barak-ch3-4`, not `main`.
- Recorded base: `29aa75bef39708af94cbd7fda4f0b84a4c488394`.
- Required ancestor: `44853c6f3177fed8f7f8d2288210593e9c094f7e`.
- `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD`
  succeeded with exit 0 before the fill; the check was also repeated before commit.
- Local working branch: `fill/ch34-c1b`; delivery commit: `40f186b10b5ae1a024b6d762a93da55d148cfc11`.
- No rebase, push, or PR was performed.

The complete brief and cited audits were read, including the R2 binding routes,
P0 findings and resolutions, P4.1 findings, policy, workflow, plan §4e, and the
maintainer's pre-ship Lean probe and output. The fill order was Examples first,
then ZeroSpace in file order; the counter-program target was independent.

Exactly these three tracked sources differ from the base:

```text
TCSlib/Complexity/SpaceComplexity/Examples.lean
TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean
TCSlib/Complexity/TuringMachine/CounterProgRun.lean
```

`evidence/check-scope.py` restores the 13 target bodies to their received
`sorry` bodies and removes only the explicitly permitted additions and status
edits; the resulting files equal the base byte for byte. This verifies the
received signatures, docstrings, declaration order, and all other bodies.
CounterProgRun changes only the body of `sim_run_of_regs_le`.

## Filled targets and binding proof routes

| ID | Declaration | Proof route |
|---|---|---|
| E1 | `Complexity.evenLang_mem_LOGSPACE` | Exported zero-tape scanner, shared bridge, then space monotonicity to `0 * logSpace n`. |
| Z1 | `Turing.FinTM.k_le_spaceUsed` | Time zero makes every visited image nonempty; sum the lower bound one. |
| Z2 | `Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` | Instantiate at `List.replicate n false`, use Z1 and `omega`. |
| Z3 | `Complexity.SPACE_eq_zero_of_exists_zero` | Z2 at the scaled bound, the shared bridge, and `SPACE.mono` for the reverse inclusion. |
| Z4 | `Complexity.SPACE_id_eq_SPACE_zero` | Z3 at the zero length. |
| Z5 | `Complexity.SPACE_succ_of_pos` | `SPACE.mono` and `SPACE.mono_const (a := 2)`, using positivity at every length. |
| Z6 | `Complexity.SPACE_succ_eq_max_one` | The same two shared monotonicity results and the `max 1` inequalities. |
| Z7 | `Turing.pairEncode_bits_inj` | Cite `pairEncode_injective` and `Complexity.LogProg.bits_injective`. |
| Z8 | `Complexity.trueLang_mem_SPACE_zero` | Private one-step constant machine and the shared zero-tape bridge. |
| Z9 | `Complexity.evenLang_mem_SPACE_zero` | The Examples exports and shared bridge directly. |
| Z10 | `Complexity.exists_zeroTape_const_oneStep` | Reuse the same private constant machine and contract. |
| Z11 | `Complexity.exists_zeroTape_parity_decider` | Reuse the two Examples exports. |
| C1 | `Complexity.CounterProg.sim_run_of_regs_le` | Induction, one-step `sim_run` at headroom one, and composition of runs. |

The parity state starts at `true` (even), stays unchanged on `false`, and toggles
on `true`. Its single private invariant records the parity of
`(x.take j).count true`, head position `j + 1`, and empty output. At the right
blank it emits that state and halts, proving the `n + 1` contract, including the
empty input. This is bit parity. E1 uses the bridge directly and imports no
ZeroSpace module. The constant machine emits and halts in one transition.

**C1 step discharge.** In the successor case, call
`sim_run P x l₀ (B + 1) 1 s hp ...`. The hypothesis `hB 0` and `run_zero`
supply the required headroom, giving a cost at most
`1 * (2 * (B + 1) + 3) = 2 * B + 5`; the received `sim_run` handles halted
states. The suffix starts at `run P x s 1`; `step_pos_le` supplies its position
bound, and `hB (1 + j)` with `run_add` supplies its reachable-register bounds.
`runFrom_add`/`run_add` compose the witnesses and `nlinarith` closes the total
bound. The frozen statement remains `t * (2 * B + 5)`. There is no additional
register hypothesis on the final state and no new corollary.

## New declarations, imports, and documentation edits

| Visibility | Declaration | Role |
|---|---|---|
| Public, required export | `Complexity.evenScanTM` | The one zero-work-tape, two-state parity scanner. |
| Public, required export | `Complexity.evenScanTM_decidesInTime` | Its decision contract within `n + 1` steps. |
| Private | `Complexity.evenScanTM_prefix` | The single prefix invariant for that scanner. |
| Private | `Complexity.constTrueTM` | The one zero-work-tape, one-state constant-true machine. |
| Private | `Complexity.constTrueTM_computesInTime` | Its one-step contract on every input. |

These are all new declarations. Each required public export has statement
prose citing `[AB09, Example 4.7]`. Both machine docstrings identify the missing
catalog row: the existing transducer halts silently, and the received private
constant machine takes two steps. There are exactly two new machines. There
is no private variant of either shared lemma and no repeated bits-injectivity
proof. Requested shared lemmas: none.

**Flagged import:** exactly
`import TCSlib.Complexity.SpaceComplexity.Machines.Bin` was added to ZeroSpace.
No Mathlib tactic import was added.

**Flagged status edits:** the received “sorried” label was removed from each
owned space module's Main results heading. ZeroSpace's “elaborated sanity
statements — their proofs are fill obligations” clause now says “proved sanity
statements”. Examples gains one Main definitions bullet for the scanner and
one Main results bullet for its contract. No other received prose or
attributions changed. Sketch appendices: none.

## Duplication governance

**new copies: none**

The brief's exact text screen and all 11 paths were used before and after.
The 43 received directed pairs are unchanged. The only new pair is the
brief's pre-identified E1/Z9 pairing, in both directions:

- E1 reproduces Z9: `108/131 = 82%`.
- Z9 reproduces E1: `108/179 = 60%`.

Both short bodies cite the same exported scanner contract and the shared
bridge; they do not duplicate the machine, invariant, or bridge proof. There
are no new in-file pairs and no other new cross-file pairs. The scanner
invariant does not pair with `transducer_run`; Z7 does not add a pair against
the encoding lemmas; C1 does not pair with `sim_run`.

The received `CounterProgRun::run_pos_le` / `CounterProg::run_regs_le` debt is
untouched: its screen fractions remain `94/116 = 81%` and `94/172 = 55%`.

The private-copy ledger is empty. All three new private declarations are
specific to the two required machines. The mandated screen and source review
identify zero copied private declarations in each touched file (cumulative
count 0, fraction 0%); the text matches above are the sanctioned public bridge
consumers and received public run-bound debt.

### Before — complete screen output

```text
declarations screened: 134; copy pairs (target reproduces >= half of source): 43; reproduced text: 7,779 chars
   CounterProg.lean::tapes_update  reproduces  CounterProg.lean::heads_update: 75/75 = 100%
   CounterProg.lean::heads_update  reproduces  CounterProg.lean::tapes_update: 75/75 = 100%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Composition.lean::controlCfg_run: 150/166 = 90%
   CounterProg.lean::apply_act  reproduces  CounterProg.lean::tapes_update: 67/75 = 89%
   CounterProg.lean::apply_act  reproduces  CounterProg.lean::heads_update: 67/75 = 89%
   Composition.lean::controlCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 150/171 = 88%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   CounterProgRun.lean::run_pos_le  reproduces  CounterProg.lean::run_regs_le: 94/116 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Composition.lean::computesFunInTime_comp  reproduces  Composition.lean::exists_comp_on_image: 178/238 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Composition.lean::exists_comp_partial  reproduces  Composition.lean::bufferedCompTM_computesInTime: 319/450 = 71%
   Composition.lean::controlCfg  reproduces  Simulation.lean::leftCfg: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   CounterProg.lean::back_walk  reproduces  CounterProg.lean::print_walk: 538/770 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   CounterProg.lean::print_walk  reproduces  CounterProg.lean::back_walk: 538/790 = 68%
   Composition.lean::condTM_start  reproduces  Simulation.lean::leftCfg_apply: 125/188 = 66%
   Composition.lean::condTM_start  reproduces  Simulation.lean::rightCfg_apply: 125/192 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Bin.lean::bits_getLast  reproduces  Bin.lean::bitsVal_bits: 251/398 = 63%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Composition.lean::exists_comp_on_image  reproduces  Composition.lean::computesFunInTime_comp: 178/295 = 60%
   Composition.lean::controlCfg_step  reproduces  Simulation.lean::leftCfg_apply: 113/188 = 60%
   Composition.lean::controlCfg_step  reproduces  Simulation.lean::rightCfg_apply: 113/192 = 59%
   Simulation.lean::leftCfg  reproduces  Composition.lean::controlCfg: 92/158 = 58%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   CounterProg.lean::run_regs_le  reproduces  CounterProgRun.lean::run_pos_le: 94/172 = 55%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Composition.lean::controlCfg_step: 351/661 = 53%
   Composition.lean::controlCfg  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
```

### After — complete screen output

```text
declarations screened: 149; copy pairs (target reproduces >= half of source): 45; reproduced text: 7,995 chars
   CounterProg.lean::tapes_update  reproduces  CounterProg.lean::heads_update: 75/75 = 100%
   CounterProg.lean::heads_update  reproduces  CounterProg.lean::tapes_update: 75/75 = 100%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Composition.lean::controlCfg_run: 150/166 = 90%
   CounterProg.lean::apply_act  reproduces  CounterProg.lean::tapes_update: 67/75 = 89%
   CounterProg.lean::apply_act  reproduces  CounterProg.lean::heads_update: 67/75 = 89%
   Composition.lean::controlCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 150/171 = 88%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   Examples.lean::evenLang_mem_LOGSPACE  reproduces  ZeroSpace.lean::evenLang_mem_SPACE_zero: 108/131 = 82%
   CounterProgRun.lean::run_pos_le  reproduces  CounterProg.lean::run_regs_le: 94/116 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Composition.lean::computesFunInTime_comp  reproduces  Composition.lean::exists_comp_on_image: 178/238 = 75%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Composition.lean::exists_comp_partial  reproduces  Composition.lean::bufferedCompTM_computesInTime: 319/450 = 71%
   Composition.lean::controlCfg  reproduces  Simulation.lean::leftCfg: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   CounterProg.lean::back_walk  reproduces  CounterProg.lean::print_walk: 538/770 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   CounterProg.lean::print_walk  reproduces  CounterProg.lean::back_walk: 538/790 = 68%
   Composition.lean::condTM_start  reproduces  Simulation.lean::leftCfg_apply: 125/188 = 66%
   Composition.lean::condTM_start  reproduces  Simulation.lean::rightCfg_apply: 125/192 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Bin.lean::bits_getLast  reproduces  Bin.lean::bitsVal_bits: 251/398 = 63%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Composition.lean::exists_comp_on_image  reproduces  Composition.lean::computesFunInTime_comp: 178/295 = 60%
   ZeroSpace.lean::evenLang_mem_SPACE_zero  reproduces  Examples.lean::evenLang_mem_LOGSPACE: 108/179 = 60%
   Composition.lean::controlCfg_step  reproduces  Simulation.lean::leftCfg_apply: 113/188 = 60%
   Composition.lean::controlCfg_step  reproduces  Simulation.lean::rightCfg_apply: 113/192 = 59%
   Simulation.lean::leftCfg  reproduces  Composition.lean::controlCfg: 92/158 = 58%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   CounterProg.lean::run_regs_le  reproduces  CounterProgRun.lean::run_pos_le: 94/172 = 55%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Composition.lean::controlCfg_step: 351/661 = 53%
   Composition.lean::controlCfg  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
```

## Verification

All Lean elaboration checks used the unchanged `scripts/lean_check_tree.sh`.
The pinned toolchain is Lean 4.25.0, with mathlib commit
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. `lake exe cache get` completed
successfully for the Mathlib roots required by the bootstrap. `lake build`
was never invoked. The manifest and toolchain declaration are unchanged.

The dependency-ordered bootstrap completed all 118 modules in
`briefs/orders/ch34-c1b.txt` before applying the draft to the working branch.
Its recorded base warning set contains 52 distinct sorry declarations, of
which exactly 13 are in the required replay set: precisely this batch's targets.
All 39 out-of-scope sorry declarations and all non-owned source files remain
untouched. The final replay's sorry-warning set is empty, exactly the base
replay set minus those 13. The facades are included; root TCSlib and the
maintainer's separate integration replay are outside this brief's check set.

| Gate | Result |
|---|---|
| Owned modules | 3/3 passed; zero errors and zero sorry warnings |
| Ordered replay | 15/15 passed; zero errors and zero sorry warnings |
| Axiom prints | 15/15; only the allowed standard axioms, no `sorryAx` |
| Scope/signature/docstring freeze | Passed; exactly the three owned files |
| Duplication comparison | Passed; only the sanctioned E1/Z9 pairing |
| Style lint | 0 FAIL in each required subtree |
| Whitespace | `git diff --check` passed |
| Delivery integrity | Patch application, bundle verification, and all archive checksums passed |

The final owned/replay check sequence and sweep tail follow; the complete
diagnostics are in `final-sweep.log`. Existing lint warnings are retained,
including the unused `x` binder in ZeroSpace's frozen full-language statement.

```text
OWNED MODULES
MODULE TCSlib/Complexity/SpaceComplexity/Examples
PASS TCSlib/Complexity/SpaceComplexity/Examples
MODULE TCSlib/Complexity/SpaceComplexity/ZeroSpace
PASS TCSlib/Complexity/SpaceComplexity/ZeroSpace
MODULE TCSlib/Complexity/TuringMachine/CounterProgRun
PASS TCSlib/Complexity/TuringMachine/CounterProgRun
OWNED_OK 3 modules
REPLAY SET IN BRIEF ORDER
MODULE TCSlib/Complexity/TuringMachine/CounterProgRun
PASS TCSlib/Complexity/TuringMachine/CounterProgRun
MODULE TCSlib/Complexity/ClassNP/CounterProgPolyTime
PASS TCSlib/Complexity/ClassNP/CounterProgPolyTime
MODULE TCSlib/Complexity/TuringMachine/CounterProgInput
PASS TCSlib/Complexity/TuringMachine/CounterProgInput
MODULE TCSlib/Complexity/ClassNP/PolyTimePrefix
PASS TCSlib/Complexity/ClassNP/PolyTimePrefix
MODULE TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
PASS TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
MODULE TCSlib/Complexity/ClassNP/PolyTimeBlockTests
PASS TCSlib/Complexity/ClassNP/PolyTimeBlockTests
MODULE TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
PASS TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
MODULE TCSlib/Complexity/ClassNP/PClosure
PASS TCSlib/Complexity/ClassNP/PClosure
MODULE TCSlib/Complexity/SpaceComplexity/CounterProgSim
PASS TCSlib/Complexity/SpaceComplexity/CounterProgSim
MODULE TCSlib/Complexity/SpaceComplexity/CounterProgSimRun
PASS TCSlib/Complexity/SpaceComplexity/CounterProgSimRun
MODULE TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
MODULE TCSlib/Complexity/SpaceComplexity/Examples
PASS TCSlib/Complexity/SpaceComplexity/Examples
MODULE TCSlib/Complexity/SpaceComplexity/ZeroSpace
PASS TCSlib/Complexity/SpaceComplexity/ZeroSpace
MODULE TCSlib/Complexity/SpaceComplexity
PASS TCSlib/Complexity/SpaceComplexity
MODULE TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine
REPLAY_OK 15 modules
FINAL_SWEEP_OK: 3 owned + 15 replay; zero errors and zero sorry warnings
```

The two required style-lint summary lines:

```text
SpaceComplexity: style_lint: 0 FAIL, 0 WARN over 42 files
TuringMachine: style_lint: 0 FAIL, 14 WARN over 46 files
```

All 14 lint WARN findings concern received oversized files, whose structure is
outside this batch's ownership and unchanged. No touched file exceeds the
size threshold. Full lint outputs are included in `evidence/`.

The complete 15 axiom prints, produced from imports of the freshly checked
final modules in an isolated artifact tree using the same check script:

```text
'Complexity.evenLang_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.k_le_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SPACE_eq_zero_of_exists_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SPACE_id_eq_SPACE_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SPACE_succ_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SPACE_succ_eq_max_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.pairEncode_bits_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.trueLang_mem_SPACE_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.evenLang_mem_SPACE_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.exists_zeroTape_const_oneStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.exists_zeroTape_parity_decider' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.CounterProg.sim_run_of_regs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.evenScanTM' depends on axioms: [propext, Quot.sound]
'Complexity.evenScanTM_decidesInTime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Environment recovery

The initial run was interrupted by the network/session hiccup, so the baseline
resumed at its first unfinished module. The raw baseline log preserves that
resume and the subsequent failed import attempts. Unchanged CodeParser and
SAT compiled artifacts required regeneration before MathlibBridge and
Cook–Levin Hardness respectively could import them; the same check script
then passed. No repository source was edited to resolve either issue.

The first final axiom pass exposed an old admitted CounterProgRun artifact.
Regenerating it produced the proved target without `sorryAx`. To prevent stale
artifact interference, the definitive owned/replay sweep and axiom audit used
an isolated output tree seeded from this task's checked dependencies, with
`TCSLIB_OLEANS` set for the unchanged check script. The superseded first sweep
and axiom logs are retained under `evidence/`; the root logs are the final
passing runs.

This sandbox's process and procfs namespaces differ. A small runtime
compatibility shim redirects only Lean's own `/proc/<getpid()>/exe` readlink
to `/proc/self/exe`, allowing the pinned binary to locate its installation.
It changes no Lean implementation, kernel check, or proof. Its C source and
the environment/version evidence are included for transparency. All checks
ran inside the existing sandbox. The final sweep has no crashes or failures.

## Package and integration

The ZIP includes this report, full modified sources at their repository paths,
the one-commit `git format-patch` series in `patches/`,
`tcslib-c1b.bundle`, `final-sweep.log`, `axioms.log`, supporting evidence, and
`SHA256SUMS` covering every other packaged file.

The bundle is incremental and requires the recorded base commit; it exports
`refs/heads/fill/ch34-c1b`. With that base available, `git bundle verify`
succeeds. The patch series was applied to a fresh temporary index at the
recorded base, and the resulting Git tree exactly matched the delivery
commit. No checkout or integration into a remote branch was performed.

To inspect locally after extracting, run `sha256sum -c SHA256SUMS` in the
package directory, then verify the bundle in a clone containing the base.
The patch series is suitable for the workflow's `git am -3` integration.
