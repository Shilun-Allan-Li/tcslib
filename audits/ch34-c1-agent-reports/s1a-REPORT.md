# Chapter 3–4 batch S1a — delivery report

**Complete: 4/4 targets and E1–E4 proved, with no `sorryAx`.** All twelve new
private declarations are complete. The proved-modulo set is empty.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch cloned: `complexity/arora-barak-ch3-4`.
- Base: `199644473a34b6da24862d94ae1eece7f8138005`.
- Local working branch: `fill/ch34-s1a`.
- Delivery commit: `99be7d9a6c7c6ea80cdd2eb2b2a3c93e6ecca134`.
- Required ancestor: `447a6cc37f9bd79306d55a2768a1c920db091ae0`.
  `git merge-base --is-ancestor 447a6cc37f9bd79306d55a2768a1c920db091ae0 HEAD`
  succeeded before editing; the supplied verifier repeats it against the base.
- No rebase, push, or PR. Only `TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean`
  changes in the commit. The patch reverse-checks against the delivered tree;
  the bundle verifies and names the base as its prerequisite.

## Completed targets and binding routes

| Target (under `Turing`) | Result and route |
|---|---|
| `NDTM.reflTransGen_cfgStep_iff` | Proved by the two required inductions: append the edge bit forward; prepend the first edge backward. |
| `NDTM.coreSum_stepWith` | Proved through `stepWith_eq_fixChoice_step`, a citation of `core_step`, the one output-symbol congruence, `step_output`, and E2. |
| `FinNDTM.acceptsWithin_of_spaceUsedWith_le` | Proved. Window facts instantiate the promoted generic lemmas. `Nat.find` minimizes accepting words with windowed actual prefixes. The splice preserves both the final vertex and every prefix vertex. The single counting lemma injects paired core/summary codes, then `AcceptsWithin.mono` pads the accepting word. No sibling-halting claim is used. |
| `FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` | Proved. Forward uses target 3; backward pads or truncates at the deciding budget using all-branch halting and `runWith_of_halt`. No C1a theorem is cited. |

## New declarations

All names below are source-level names; private kernel names are module-mangled.

| Declaration | Visibility and role |
|---|---|
| `Turing.outSummary_eq_accept_iff` | **Export E1:** exactly the sanctioned statement; recognizes `[true]`. |
| `Turing.outSummary_append_congr` | **Export E2:** exactly the sanctioned statement; the local append table handles empty, accepting, and dead histories once. |
| `Turing.NDTM.coreSum_runWith` | **Export E3:** exactly the sanctioned statement; iterates target 2 over a common choice word. |
| `Turing.FinNDTM.not_acceptsWithin_zero` | **Export E4:** exactly the sanctioned statement; the initial state is live. |
| `Turing.InWindow` | Private predicate: every head and nonblank work cell has absolute position at most the radius. |
| `Turing.NDTM.outputSymbol_congr` | Private: equal cores select equal emissions; destructures configurations, without reproducing `core_step`'s scanned-symbol proof. |
| `Turing.NDTM.take_succ_action` | Private: the **single prefix-step lemma**; successive choice prefixes differ by identity or one applied action, using the deterministic slice. |
| `Turing.NDTM.abs_lt_card_visitedWith` | Private: **visited-position window fact**, an instance of `abs_lt_card_image_of_unitSteps`. |
| `Turing.NDTM.mem_visitedWith_of_ne_none` | Private: **nonblank-cell window fact**, an instance of `mem_image_workTapePos_of_ne_none`. |
| `Turing.NDTM.visitedWith_take_subset` | Private: **prefix inclusion** for visited sets; works for every prefix index, including saturated takes. |
| `Turing.NDTM.runWith_take_inWindow` | Private: combines the two window facts, prefix inclusion, and the single-tape summand bound to window every prefix. |
| `Turing.NDTM.inWindow_of_coreSum_eq` | Private: transfers window validity through equality of vertices. |
| `Turing.NDTM.splice_vertices` | Private: deleting between equal vertices preserves the final vertex and makes every shortened prefix vertex an original prefix vertex. |
| `Turing.FinNDTM.sumCode` | Private: sends the three summaries to `Fin 3`; **no `Fintype OutSummary` instance** is added. |
| `Turing.FinNDTM.sumCode_injective` | Private: injectivity of that summary code. |
| `Turing.FinNDTM.count_windowed_vertices` | Private: the **single counting lemma**, reusable by S1b in this file. Pairwise-distinct vertices of windowed configurations have count at most `configBound`; `coreCode_inj` is cited with its window hypotheses. |

**Requested shared lemmas:** promote `NDTM.abs_lt_card_visitedWith`,
`NDTM.mem_visitedWith_of_ne_none`, and `NDTM.visitedWith_take_subset` into
`TuringMachine/NondeterministicSpace.lean` at its next shared-file window,
with `NDTM.take_succ_action` as their common prefix-step support. They remain
private here as required by file ownership. The window predicate and its
assembly/transport, splice, and counting lemmas remain local graph helpers.

**Imports: none added or changed. Mathematical escalations: none.**
No shared or consumer file was edited; no upstream `sorry` is cited.

## Frozen surface and flagged prose changes

The supplied executable scope check confirms:

- all seven original theorem statements are byte-identical;
- all five original definition/type declarations are byte-identical;
- the entire suffix from `namespace Complexity` through end-of-file is
  byte-identical, including the three summit statements, docstrings, and sorries;
- all original names remain; the only public additions are E1–E4;
- imports are byte-identical.

Flagged allowed status edits: the module's two-line status paragraph now says
that the graph contracts are proved and the three class results remain sorried;
the Main results heading says the same; each of the four target status tags
now says proved. One Main results bullet was added per delivered export.
Each export has its required `[AB09, §4.1.1]` docstring and Proof sketch.
No existing attribution or proof sketch was edited; no sketch appendix was needed.

## Verification

Lean `4.25.0`, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
Every source/probe check used the unchanged `scripts/lean_check_tree.sh`.
**No `lake build` was run.**

| Check | Result |
|---|---|
| Complete base bootstrap from `briefs/orders/ch34-s1a.txt` | 93/93 modules, zero errors, 59 existing sorry warnings |
| Final sweep, owned module and all 13 later modules | 14/14 modules, zero errors, 43 sorry warnings versus 47 in the same base population |
| `ConfigGraph` | Exactly three sorry warnings: `NSPACE_subset_exp_dtime` at line **567**, `NL_subset_P` at **587**, and `polyTimeReducible_of_mem_NL` at **607** |
| Downstream population | Its 40 sorry warnings are exactly the base multiset; includes `TQBF`, `Games`, both facades, `Inclusions`, `Examples`, `ZeroSpace`, `Savitch`, `Hierarchy`, and all four listed Logspace modules |
| Eight required axiom prints | Within `[propext, Classical.choice, Quot.sound]`; **no `sorryAx`** |
| SpaceComplexity campaign style lint | **0 FAIL, 0 WARN over 42 files** |
| `git diff --check`, freeze, duplication and archive evidence | Pass |

Warning inventories record file, declaration and shifted line. The four removed
warnings are exactly the owned targets. `evidence/verify-s1a.py`, run from the
repository root with its sibling evidence files, reproduces these comparisons.
`evidence/final-order.txt` records the complete final sweep order. Each successful
check requires a freshly generated olean, as enforced by the unchanged script.

Environment note: the runner's PID namespace differs from its procfs namespace,
so the unmodified Lean binary initially could not locate itself. The small
`evidence/proc-self-compat.c` adapter changes only executable-path lookup for
`/proc/<current process id>/exe` to `/proc/self/exe`. It was compiled as a shared
object and set via `LD_PRELOAD` for cache and check commands. No Lean source,
kernel, proof-checking command, or axiom policy was altered. A normal environment
does not need this adapter. A first full-cache attempt exceeded available disk;
the successful `lake exe cache get` was restricted to the 38 Mathlib roots in
`evidence/cache-roots.txt` (the listed `Std.Sat.CNF` is toolchain-provided).
Its success log is included. Dependency cache files with identical bytes were
deduplicated; every campaign module was independently re-elaborated in the
successful base bootstrap. Local git storage borrows existing ancestor objects;
the delivery bundle independently includes the changes above the stated base.

### Axiom output

```text
'Turing.NDTM.reflTransGen_cfgStep_iff' depends on axioms: [propext, Quot.sound]
'Turing.NDTM.coreSum_stepWith' depends on axioms: [propext, Quot.sound]
'Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Turing.outSummary_eq_accept_iff' depends on axioms: [propext]
'Turing.outSummary_append_congr' depends on axioms: [propext]
'Turing.NDTM.coreSum_runWith' depends on axioms: [propext, Quot.sound]
'Turing.FinNDTM.not_acceptsWithin_zero' depends on axioms: [propext, Quot.sound]
```

### Owned-module check

```text
CHECK TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:567:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:587:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:607:8: warning: declaration uses 'sorry'
```

### Final sweep tail

```text
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:201:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:231:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:89:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:99:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:119:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:130:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:142:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:65:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/SpaceComplexity
```

## Duplication governance

**new copies: none**

- Base: 99 declarations screened, 41 pairs, 3,852 reproduced characters.
- Final: 117 declarations screened, the same 41 pairs and 3,852 characters.
- The complete pair lists are byte-identical. There are **no new cross-file
  pairs**, **no new in-file pairs**, and no pair involving `ConfigGraph`.
- The known `visitedByTapeHead_mono`/prefix-inclusion hazard did not trigger.
- New copied material in `ConfigGraph`: zero declarations and zero characters.
  No copy debt or justification is required.

Both complete screen outputs follow and are also supplied as separate logs.

### Before

```text
declarations screened: 99; copy pairs (target reproduces >= half of source): 41; reproduced text: 3,852 chars
   OracleNondeterministic.lean::AcceptsWithin  reproduces  NTIME.lean::AcceptsWithin: 109/109 = 100%
   OracleNondeterministic.lean::runWith_append  reproduces  Nondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::runWith_append  reproduces  OracleNondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::stepWith  reproduces  Deterministic.lean::step: 87/87 = 100%
   Deterministic.lean::step  reproduces  Nondeterministic.lean::stepWith: 87/88 = 99%
   NTIME.lean::AcceptsWithin  reproduces  OracleNondeterministic.lean::AcceptsWithin: 109/111 = 98%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   OracleNondeterministic.lean::stepWith  reproduces  Nondeterministic.lean::stepWith: 85/88 = 97%
   Oracle.lean::step  reproduces  Deterministic.lean::step: 84/87 = 97%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   OracleNondeterministic.lean::stepWith  reproduces  Deterministic.lean::step: 81/87 = 93%
   Oracle.lean::step  reproduces  Nondeterministic.lean::stepWith: 81/88 = 92%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   OracleNondeterministic.lean::HaltsWithin.mono  reproduces  Nondeterministic.lean::HaltsWithin.mono: 220/252 = 87%
   OracleNondeterministic.lean::runWith_of_halt  reproduces  Nondeterministic.lean::runWith_of_halt: 68/78 = 87%
   Nondeterministic.lean::runWith_of_halt  reproduces  OracleNondeterministic.lean::runWith_of_halt: 68/79 = 86%
   Nondeterministic.lean::HaltsWithin.mono  reproduces  OracleNondeterministic.lean::HaltsWithin.mono: 220/257 = 86%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   Oracle.lean::step  reproduces  Deterministic.lean::outputSymbol: 65/86 = 76%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   OracleNondeterministic.lean::stepWith  reproduces  Deterministic.lean::outputSymbol: 62/86 = 72%
   Nondeterministic.lean::stepWith  reproduces  Deterministic.lean::outputSymbol: 62/86 = 72%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   Deterministic.lean::MultiTapeTM  reproduces  Nondeterministic.lean::NDTM: 113/160 = 71%
   Deterministic.lean::outputSymbol  reproduces  Nondeterministic.lean::stepWith: 62/88 = 70%
   OracleNondeterministic.lean::AcceptsWithin.mono  reproduces  NTIME.lean::AcceptsWithin.mono: 143/207 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   NTIME.lean::DecidesInTime  reproduces  OracleNondeterministic.lean::DecidesInTime: 61/92 = 66%
   Nondeterministic.lean::NDTM  reproduces  Deterministic.lean::MultiTapeTM: 113/171 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   NTIME.lean::AcceptsWithin.mono  reproduces  OracleNondeterministic.lean::AcceptsWithin.mono: 143/220 = 65%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   OracleNondeterministic.lean::DecidesInTime  reproduces  NTIME.lean::DecidesInTime: 61/112 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
   Deterministic.lean::step  reproduces  Oracle.lean::step: 84/165 = 51%
```

### After

```text
declarations screened: 117; copy pairs (target reproduces >= half of source): 41; reproduced text: 3,852 chars
   OracleNondeterministic.lean::AcceptsWithin  reproduces  NTIME.lean::AcceptsWithin: 109/109 = 100%
   OracleNondeterministic.lean::runWith_append  reproduces  Nondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::runWith_append  reproduces  OracleNondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::stepWith  reproduces  Deterministic.lean::step: 87/87 = 100%
   Deterministic.lean::step  reproduces  Nondeterministic.lean::stepWith: 87/88 = 99%
   NTIME.lean::AcceptsWithin  reproduces  OracleNondeterministic.lean::AcceptsWithin: 109/111 = 98%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   OracleNondeterministic.lean::stepWith  reproduces  Nondeterministic.lean::stepWith: 85/88 = 97%
   Oracle.lean::step  reproduces  Deterministic.lean::step: 84/87 = 97%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   OracleNondeterministic.lean::stepWith  reproduces  Deterministic.lean::step: 81/87 = 93%
   Oracle.lean::step  reproduces  Nondeterministic.lean::stepWith: 81/88 = 92%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   OracleNondeterministic.lean::HaltsWithin.mono  reproduces  Nondeterministic.lean::HaltsWithin.mono: 220/252 = 87%
   OracleNondeterministic.lean::runWith_of_halt  reproduces  Nondeterministic.lean::runWith_of_halt: 68/78 = 87%
   Nondeterministic.lean::runWith_of_halt  reproduces  OracleNondeterministic.lean::runWith_of_halt: 68/79 = 86%
   Nondeterministic.lean::HaltsWithin.mono  reproduces  OracleNondeterministic.lean::HaltsWithin.mono: 220/257 = 86%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   Oracle.lean::step  reproduces  Deterministic.lean::outputSymbol: 65/86 = 76%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   OracleNondeterministic.lean::stepWith  reproduces  Deterministic.lean::outputSymbol: 62/86 = 72%
   Nondeterministic.lean::stepWith  reproduces  Deterministic.lean::outputSymbol: 62/86 = 72%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   Deterministic.lean::MultiTapeTM  reproduces  Nondeterministic.lean::NDTM: 113/160 = 71%
   Deterministic.lean::outputSymbol  reproduces  Nondeterministic.lean::stepWith: 62/88 = 70%
   OracleNondeterministic.lean::AcceptsWithin.mono  reproduces  NTIME.lean::AcceptsWithin.mono: 143/207 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   NTIME.lean::DecidesInTime  reproduces  OracleNondeterministic.lean::DecidesInTime: 61/92 = 66%
   Nondeterministic.lean::NDTM  reproduces  Deterministic.lean::MultiTapeTM: 113/171 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   NTIME.lean::AcceptsWithin.mono  reproduces  OracleNondeterministic.lean::AcceptsWithin.mono: 143/220 = 65%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   OracleNondeterministic.lean::DecidesInTime  reproduces  NTIME.lean::DecidesInTime: 61/112 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
   Deterministic.lean::step  reproduces  Oracle.lean::step: 84/165 = 51%
```

## Archive contents

- `REPORT.md`
- full modified `TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean`
- `patches/0001-Prove-the-S1a-configuration-graph-lemmas.patch`
- `fill-ch34-s1a.bundle` (prerequisite: the recorded base)
- `evidence/`: successful base/final sweeps, axiom probe/output, warning
  inventories, duplication screens, lint, scope verifier, cache and environment
  evidence, and bundle verification
- `SHA256SUMS` for every other payload file
