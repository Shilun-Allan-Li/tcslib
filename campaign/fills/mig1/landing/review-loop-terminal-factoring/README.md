# Loop terminal-certificate factoring: passed proposal, not applied

The complete proposed source factors the repeated startup/run/certificate/time-bound suffix in
`loopHostTM_decides`, `loopHostTM_finds`, and `emitLoopTM_computes` into one private theorem,
`loop_computes_of_startup`. It is a proof property of a supplied finite machine and configuration;
it constructs no machine or host and introduces no public API. All three consumers use it.

`Loop-proposed-v1.lean.txt` is the complete proposed module. `Loop-body-only-v1.patch` is the exact
four-hunk patch; independent hunk reconstruction reproduces the complete proposed source.
The live source was **not edited** and remained identical to `Loop-before.lean.txt` at the final
check. Parent will decide when to apply it after the running replay ends.

| Pin | SHA-256 |
|---|---|
| Actual input, 295072 bytes | `0e2e7ed7b1bb07bcc15df9e99a6cf6033f2aad1b0cfd84ddf12e035add94c9d0` |
| Proposed full source, 294555 bytes | `2908372c0a10bc66db747c49de96d165fb2fa3e09bc21582bde26e157531a206` |
| Exact patch | `c055399a74303fc2c417f6772cf9af6118c0a861caa370cc24215955ee45e3d4` |

## Exact source scope

The helper composes the startup equation and halted segment with the published
`MultiTapeTM.runFrom_add`, reads the halt/output through `computesInTime_iff`, and uses
`ComputesInTime.mono` plus `B + N*B = B*(N+1)`. Each consumer instantiates
`B = 10*(T |x|+1)` and `N = R |x|+1`, preserving the exact public budget with coefficient **10**.
The emitting consumer retains its original `List.nil_append`/local `orbit` output normalization
as a premise to the shared helper. The preceding fuel, startup, configuration, segment and
summation witnesses are byte-identical prefixes, recorded in `freeze-v1.json`.

The balanced lexical freeze compares all **208** existing declarations, handling nested named
arguments rather than stopping at their `:=`. All existing headers and docstrings, imports,
visibility, relative declaration order, executable definitions, tables, types, coefficients, and
all other declaration bodies are literal-equal. Public source declarations stay **21 → 21**;
private source declarations **187 → 188**, solely the new proof helper. Existing theorem lines
and proposed theorem lines are in `source-lines.json`; the proposed helper begins at line 2536.

## Executed evidence

All elaborations used the managed plain `leanelab.sh` wrapper, local budget three, sequentially,
against the parent's read-only complete `oleans-mig1-preflight-current2` tree. The exact wrapper
commands, times, input/output hashes, and raw outputs are retained beside the inputs. No compiled
output or shared snapshot/cache was written.

| Check | Result |
|---|---|
| Complete native proposed source plus axiom prints | PASS, 0 errors, 12.37 s |
| Complete source, four complete changed/new proof regions strongly guarded | PASS, 0 errors, 13.37 s |
| Axiom inventory: four roots plus all eight compiled descendants | All 12 use only `propext`, `Classical.choice`, `Quot.sound` (or subsets) |
| Fresh unsealed controls, 30 definitions × point/abstract modes | PASS, exit 0, 0 errors, 60 kernel-checked proof constants |
| Fresh sealed counterparts | Expected FAIL, exit 1, exactly 60 identified diagnostics |
| Exact diagnostic identity/multiplicity checker | PASS; four deliberately corrupted evidence cases rejected |

The seal starts **before each docstring/header**, including the new helper. It marks the same
30 ordinary foreign definitions effectively controlled in the earlier Composition/Loop review
irreducible, and removes the three default simp definitions `Action.apply`, `Cfg.init`, and
`MultiTapeTM.initCfg`. Removing exactly the recorded instrumentation and appendix recovers the
proposed source bytes. Unchanged legacy helper proofs remain outside the guards and are consumed
opaquely. Their proofs are not independently re-audited by this proposal.

The fresh compiled inventory of the four roots' types/values and their eight descendants finds
five direct foreign ordinary definitions: `Cfg.ofWords`, `FinTM.ComputesFunInTime`,
`FinTM.ComputesInTime`, `MultiTapeTM.initCfg`, and `MultiTapeTM.runFrom`. All are guarded. Eight
other direct foreign definitions are reducible field projections and are explicitly classified
as abbreviations in `compiled-direct-inventory.json`. The conservative 30-definition seal also
blocks model/embedding operations that could be reached through same-home configuration reads;
the 30 are not claimed to be 30 direct dependencies of these four roots.

Fresh controls reuse the inspected trusted instrumentation from `review-composition-loop`,
but were executed anew in current2. They cover all 30 guarded definitions individually in both
modes, including the five direct ordinary dependencies above. They import current2's existing
Loop module solely to access the same imported foreign definitions; they do not claim to test
the newly proposed helper's behavior. No unsafe reducibility or admitted failed control is used.
The unrelated `rewind_scan.match_1` is outside the effective guard/control claim.

Manual inspection of every `rw`/`simp`/`simpa`/`dsimp` argument in all four complete proof regions
found only local definitions/hypotheses, same-home declarations, or published equation/theorem
names. In particular `captureCfg_output` is used instead of unfolding the sealed `captureCfg`.
The retained `Cfg.ext` block uses local `candidate`/same-home `loopCall` and published
`captureCfg_output`; it succeeds under the whole-region guard. No explicit foreign-definition
argument bypasses the guard.

## Limits and retained attempts

This proves the bounded proposed repair of this **three-consumer suffix family**. It does not
merge the distinct Boolean/find/emission summation statements and does not dispose of other
Loop duplication candidates, notably the separate bank-initial/bank-final scaffold. No debt is
acknowledged, external gate closed, dispatch readiness or merge clearance asserted. No screen,
replay, Git operation, actual source write, snapshot write, or cache write was performed.

The only failed setup attempt was an off-by-one parent-directory calculation, caught by an
assertion before context/runner creation or any Lean run (`setup-attempt1.json`). Both proof
checks passed on their first attempt. The negative control run is an intentional failure.
All source/probe inputs, raw outputs, receipts, freeze and inventories are retained here.
