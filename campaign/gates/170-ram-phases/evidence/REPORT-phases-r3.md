# fill-ram-phases-r3

Completed the two gate-170 repairs against **59c7b4be4a3d22b64e390ebc8b9b141ef7786c29**, exactly the dispatch base (PR #386,
`ram/fill-phases`). Local source branch: `codex/fill-ram-phases-r3`; local source commit:
**68c4a5fbc45702682a8068077de12bef09cb595a**. The source branch is not pushed, and no PR is opened.

Input: `exchange/pass-shelat-ch5-8:arora-barak-ch3-4/outbox/fills/fill-ram-phases-r3/`.
The bundle's SHA-256 is **ec5e73b93a79ebabb8bf52d6e887733a8c3c58c1916b486fcf2c54115ce64ffc**,
matching both the dispatch literal and `SHA256SUMS`; the README checksum also matches.
The first two bundle sections (COMMON including tier 2, then the R3 brief) were read first.
The bundled findings, policy, workflows and environment addendum were then consulted.
The integrity and pinned input records are under `evidence/inputs/`.

Both targets remain proved. Their admission lists are empty, with no allowance for inherited
admissions. **The entire `Sim/Phases.lean` module is byte-identical to the base**, hence both
headline statements are byte-identical. All TCSlib files outside the owned population are
unchanged except the facade's permitted Contents descriptions. No foreign declaration,
statement, reader, attribute, or proof body was changed. In particular, the existing
`Turing.Cfg.select_eq` is consumed rather than added again.

## Unified certificate and caller moves

`PhaseCertificate E P Q selected` (PhaseBlock:43) stores one finite machine,
an injective `E ↪ State` exit map, a common constant, and a restored-head run to
`exit (selected x i)` whose cut is `Set.range (fun e => some (exit e))`.
Its exit type has `Fintype` and `DecidableEq` parameters.

- `PhaseBlock` is the Unit specialization, selected by `()`.
- `PhaseBranch` is the Bool specialization, selected by its existing input/data flag.
- `PhaseCertificate.seq` (PhaseBlock:112) has the only certificate composition
  proof: a Unit-exit prefix followed by any finite-exit certificate. It cites
  `phase_reaches_seq`, transports the exit range through `Sum.inr`, and absorbs dispatch once.
- `phase_machine_ofCertificate` (PhaseControl:171) has the only fresh-entry packaging
  proof. Its two `Option E` slots route the native labels to next/jump. A present slot is the
  corresponding native exit on the seam's right; an empty slot uses the never-targeted left
  true state. The routing witness is necessary because `PhaseMachine` has exactly two distinct
  external exits. Certificate composition itself remains generic over every finite E.
  The Unit instance uses next=`some ()`, jump=`none`, classify=false. The Bool instance uses
  next=`some false`, jump=`some true`, classify=id. This fully shares seam construction,
  zero-prefix composition, fresh-entry proof, allowance absorption, and exit-cut restriction.
- `phase_machine_ofBlock` and `phase_machine_ofBranch` retain their statements and are thin
  citations supplying those routing data. Neither contains a seam/run/allowance proof.

Declarations removed, merged or renamed:

| Former declaration/interface | Replacement and callers |
|---|---|
| `structure PhaseBlock`, `structure PhaseBranch` | One `structure PhaseCertificate`; old names retained as Unit/Bool abbreviations. Their separate constructors/field families are removed. |
| `PhaseBlock.seq`, `PhaseBranch.seq` | One `PhaseCertificate.seq`. Dot calls in PhaseSchedules and PhaseOperations resolve to it; PhaseBranchMachines now explicitly cites it. |
| `PhaseBlock.weaken` | `PhaseCertificate.weaken`, generalized over E. There was no direct use of the old block-specific helper in this closure. `PhaseMachine.weaken` is unchanged. |
| Native branch `yes`, `no`, `distinct` fields | Injective Bool exit map in `phase_testBlock`, whose applications recover the same native yes/no endpoints. `Bool.range_eq` reads its two-exit cut. |
| Block's state-valued `exit` | `exit ()`; PhaseFork's redirection and continuation contract use this label and `Set.range_unique` for the singleton cut. |
| Two substantive `phase_machine_of*` proofs | One `phase_machine_ofCertificate`; the two old entry points are citation-only specializations. |
| Singleton-only `phase_reaches_add_unused` | Same owned name, generalized to restrict any cut to a subset of its old exits plus one unused state. It supports the one common packaging proof. |

New explicit public names, all in `WordRAM.Sim`: `PhaseCertificate`, `PhaseBlock_eq`,
`PhaseBranch_eq`, `PhaseCertificate.weaken`, `PhaseCertificate.seq`,
`phase_machine_ofCertificate`. The generated record constructor/projections/recursors replace
the two old generated families. Both abbreviations have published equality readers.
The complete final generated and explicit surface is in `final-declarations.tsv`.
No new private declaration, file, host, simp attribute, axiom or admission was introduced.
Local `loc`, `hloc`, `X`, `hmem`, and `hcut` establish routing inside the one packaging proof.
The existing seam/host contracts are reused; the halted Boolean padding leaf performs no
computation and the existing seam supplies dispatch. No native transition table is rederived.

Two inherited missing proof-sketch markers (phase_sourceBlock and phase_seam_fresh) were
filled in; their proof bodies were not changed. Every owned file passes the repository style
lint. No file was added/removed. The facade imports stay identical and its two Contents lines
now name the unified interface and the Bool specialization.

## Segment citations

`phase_reaches_zero` (PhaseControl:56) obtains its segment from `Turing.Segment.zero`,
reads it with `Turing.segment_iff`, and returns the bounded form through
`Turing.reachesWithin_iff`. It no longer proves the zero-time run/cut/envelope by cases.

`phase_reaches_trans` (PhaseHost:131) reads both bounded witnesses through
`reachesWithin_iff`, widens both head predicates to the summed radius about F, and uses restored
intermediate heads to identify G's center with F's. It constructs the two segments through
`segment_iff`, cites **`Turing.Segment.trans`**, then reads the result back through both
published readers. Its only additional proof work is radius and time-bound transport.
There is no `runFrom_add` call, run-prefix split, or reconstructed segment concatenation.
Both public ReachesWithin wrappers remain because their callers need that interface.

The import closure and construction registry were searched before these adapters: Segment.zero,
trans and mono; reachesWithin_iff/mono; Contract.ofReaches/seq; seam transition equations;
Mathlib Set.range_unique/range_comp', Bool.injective_iff/range_eq, and
Function.Embedding.coeFn_mk. The selected facts are cited rather than reproved.

## Source sizes

All counts are physical source lines; every owned file is below 600. Full source digests and
scope/freeze receipts are in `final-static-audit.json`.

| Owned file | Base | Delivered | Delta |
|---|---:|---:|---:|
| `PhaseAtoms.lean` | 190 | 190 | +0 |
| `PhaseBlock.lean` | 172 | 198 | +26 |
| `PhaseBounds.lean` | 89 | 89 | +0 |
| `PhaseBranchMachines.lean` | 100 | 100 | +0 |
| `PhaseBranching.lean` | 121 | 52 | -69 |
| `PhaseCoin.lean` | 147 | 147 | +0 |
| `PhaseCompute.lean` | 160 | 164 | +4 |
| `PhaseControl.lean` | 214 | 246 | +32 |
| `PhaseCore.lean` | 196 | 196 | +0 |
| `PhaseEmit.lean` | 174 | 174 | +0 |
| `PhaseFork.lean` | 229 | 229 | +0 |
| `PhaseHost.lean` | 157 | 162 | +5 |
| `PhaseInput.lean` | 109 | 109 | +0 |
| `PhaseInvariant.lean` | 135 | 135 | +0 |
| `PhaseLayout.lean` | 158 | 158 | +0 |
| `PhaseMemory.lean` | 251 | 251 | +0 |
| `PhaseMemoryMachines.lean` | 151 | 151 | +0 |
| `PhaseOperations.lean` | 152 | 152 | +0 |
| `PhaseRegister.lean` | 104 | 104 | +0 |
| `PhaseRows.lean` | 312 | 312 | +0 |
| `PhaseSchedules.lean` | 116 | 116 | +0 |
| `PhaseSemantics.lean` | 119 | 119 | +0 |
| `PhaseTable.lean` | 246 | 246 | +0 |
| `PhaseTape.lean` | 234 | 234 | +0 |
| `PhaseTests.lean` | 133 | 117 | -16 |
| `Phases.lean` | 282 | 282 | +0 |

## Readers, homes and seals

No home-file reader was added. The important changed-code reads are Segment via segment_iff;
ReachesWithin via reachesWithin_iff; frame configurations via PhaseFrame.cfg_eq; deterministic
embedding/fixed choice via their q₀/tr equations; seam transitions via seamCompTM_tr_inl/inr and
Action.mapState_state. Certificate fields are structure projections, and Unit/Bool aliases are
reducible notation with equality readers. Core/Mathlib definitions are not passed to explicit
simp/rw/unfold lists; the embedding application is read by Function.Embedding.coeFn_mk.

The unchanged proof population continues to read these other-file definitions through their
published API (the seal inventories enumerate all eligible imported TCSlib definitions, a
superset of those reached by the proofs):

| Definition family | Equations/contracts consumed |
|---|---|
| InRange; keyBits; TableOf; Encodes; ImmBound; immediates | inRange_iff; keyBits_def; tableOf_iff; encodes_iff; immBound_iff; immediates_def |
| xstep; effect; inBitWord; coinWord; touches/baseTouches | xstep_def; effect_def; inBitWord_def; coinWord_def; XInstr.touches_def; baseTouches_def |
| bvBits; word/scratch layout | bvBits_def/length/injective; wordAt_iff; wordWrite_apply; scratchBlank_iff |
| keyed/table layouts and operations | keyFields_def; keyTableLength_def; keyTableAt_iff; keyLookup_def; keyAssign_def; keyTableWrite_apply; tableFields_eq; tableAt_iff; joinFields_length; fieldsTape_of_neg/of_length_le; bufferTape_left/nat |
| Cfg.select/mapState/bindState | select_eq; mapState field equations and mapState_eq_of_fields; bindState field equations |
| embedEmitTM/embedEmitCfg | embedEmitTM_runFrom; embedEmitCfg_eq/select/state/selected_pos/unselected |
| machine run/step; action application | runFrom_zero/one/succ_eq_step'; step_of_some/of_halt; Action.apply field equations; moveInputPos_zero |
| FinTM.controlAction | controlAction_def; controlAction_apply |
| seamCompTM | tr_inl/tr_inr; Contract.seq; phase_reaches_seq |
| Segment; ReachesWithin | segment_iff; Segment.zero/trans; reachesWithin_iff; ReachesWithin.mono |
| Contract.ofReaches/seq/inPhase | pre/time/post/lo/hi equations; ofReaches_time_le; run/cut/env projections |
| phaseHostTM; NDTM.phaseHostND | phaseHostTM_run_le; phaseHostND_tr; phaseHostND_fixChoice |
| NDTM.fixChoice; MultiTapeTM.toNDTM | q₀/tr equations; phase_toNDTM_fixChoice |
| frame/register interfaces | cfg_eq, ofCfg and write/assign/emit generated field equations; phaseReady_iff; phaseScratch_iff; phaseState_iff; phasePost_iff; bank apply equations; PhaseArith.value_eq/steps_eq; PhaseTestKind.bit_eq and their contracts |

All **104 pinned base source homes** in the TCSlib import closure are archived under
`evidence/citation-homes/` as text, with paths and SHA-256 in `citation-homes.json`, including
all Segment/Reach/Seam/NDHost and catalog/word/RAM homes. The delivered owned sources supply
the corresponding current homes. No reviewer needs to retrieve an omitted citation home.

Every one of the 26 owned modules was re-elaborated in a scratch copy with all eligible
other-file TCSlib definitions locally irreducible and their simp-unfold attributes removed.
The standard inventory excludes reducible abbreviations, projections, private and internal
constants. Exact inventory names, attributes, source hashes, probe sources and logs are shipped.

| Sealed owned module | Foreign definitions | Simp attributes removed | Exit |
|---|---:|---:|---:|
| `PhaseTable` | 350 | 3 | 0 |
| `PhaseLayout` | 350 | 3 | 0 |
| `PhaseCore` | 350 | 3 | 0 |
| `PhaseTape` | 352 | 3 | 0 |
| `PhaseInvariant` | 352 | 3 | 0 |
| `PhaseRows` | 355 | 3 | 0 |
| `PhaseRegister` | 362 | 3 | 0 |
| `PhaseMemory` | 362 | 3 | 0 |
| `PhaseInput` | 366 | 3 | 0 |
| `PhaseBounds` | 367 | 3 | 0 |
| `PhaseBlock` | 369 | 3 | 0 |
| `PhaseAtoms` | 370 | 3 | 0 |
| `PhaseCompute` | 370 | 3 | 0 |
| `PhaseSchedules` | 370 | 3 | 0 |
| `PhaseOperations` | 370 | 3 | 0 |
| `PhaseControl` | 378 | 4 | 0 |
| `PhaseSemantics` | 378 | 4 | 0 |
| `PhaseMemoryMachines` | 379 | 4 | 0 |
| `PhaseTests` | 378 | 4 | 0 |
| `PhaseBranching` | 379 | 4 | 0 |
| `PhaseBranchMachines` | 380 | 4 | 0 |
| `PhaseHost` | 380 | 4 | 0 |
| `PhaseFork` | 401 | 4 | 0 |
| `PhaseCoin` | 404 | 4 | 0 |
| `PhaseEmit` | 404 | 4 | 0 |
| `Phases` | 405 | 4 | 0 |

## Complete admission walks and axiom prints

The final probe audits **all 361 owned/reader roots** by traversing both the type and
value of every reachable constant, including theorem bodies and foreign definition values.
Every direct-admission list is empty: no allowed-frontier shortcut or theorem-boundary stop.
The exact probe, prints, lists and assertions are in `FinalAxioms.lean.txt`, `final-axioms.log`,
`final-admissions.json`, and `final-target-admissions.json`.

```text
'WordRAM.Sim.exists_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
'WordRAM.Sim.exists_verdictPhase' depends on axioms: [propext, Quot.sound]
DIRECT_SORRY|WordRAM.Sim.exists_phase|[]
DIRECT_SORRY|WordRAM.Sim.exists_verdictPhase|[]
```

Separate complete graph exports make the walks independently inspectable. Each records every
visited constant and its direct type/value edges; the final checker verifies graph closure,
no unresolved constant, and no sorryAx node:

| Target | Visited constants | Direct admissions | Unresolved | Full type-and-value graph |
|---|---:|---|---|---|
| exists_phase | 9301 | `[]` | `[]` | `full-walk-WordRAM.Sim.exists_phase.json` |
| exists_verdictPhase | 2036 | `[]` | `[]` | `full-walk-WordRAM.Sim.exists_verdictPhase.json` |

Both full JSON graphs, not just their metadata allowance, are included in this delivery.

## Verification and resources

- Exact-base bootstrap: **96 TCSlib modules** plus a Mathlib-root cache probe, all exit 0,
  into a newly created `.lake/fill-ram-phases-r3-oleans`. No R1/R2 TCSlib olean was reused.
- Final official `scripts/lean_check_tree.sh` sweep: all **26 owned modules** and **8 remaining
  downstream modules** exit 0, including Phases, Simulation, Classes and RAMSimulation.
  The two doc-only fixes have refreshed source and seal receipts, followed by fresh admission
  and complete-graph probes. No proved owned target has a sorry warning.
- Every module of the final **104-module closure** has a successful receipt matching its current
  source SHA-256 and a nonempty product in the new private tree. See final-validation.json and
  the supplied order lists. The root TCSlib facade was not built.
- All 26 final seals, declaration inventory, axiom prints, all-root walks and both full-graph
  probes exit 0. The static/scope/statement audit and git diff --check pass.
- Owned style lint: exit 0, zero findings. Combined owned+facade lint: exit 1, exactly three
  pre-existing missing-option findings in the facade (baseline five findings). Adding facade
  options is outside this job's permitted imports/Contents edit. No new style finding remains.
- The patch applies cleanly to text exports of the exact base; all 27 delivered source files
  match the applied patch byte-for-byte and the local commit. `package-validation.json` records it.

Native macOS arm64, 12 logical CPUs, 18 GiB physical RAM. The addendum's Linux probes were
replaced by sysctl, vm_stat, memory_pressure, native df/mount, and /usr/bin/time -l; raw outputs
are in preflight.log. Conservative available memory was **7433699328 bytes**
(free + inactive + speculative pages, 6.92 GiB) and APFS free space was
**84233674752 bytes** (78.45 GiB), exceeding the 4/12 GiB floors.
Observed maximum RSS was **2703605760 bytes**
(2578.4 MiB). No E-RES condition or executable shim occurred.

The existing `.lake/packages` symlink points to
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages`.
Every present package URL and revision matches the current manifest; doc-gen4, UnicodeBasic,
BibtexQuery and MD4Lean are correctly recorded ABSENT. No module imports an absent package.
There are zero empty package oleans, and the real Mathlib-root probe passes. Bool's precise
Set import was already cached. No cache fetch, dependency-tree copy or cross-tree TCSlib
product reuse occurred. No `lake build` command was used.

At most **one Lean process of this job** ran at a time. Before each it checked the machine count,
then held one of the repository's three shared slot locks. Prestart counts were
[0, 1, 2]; **no Lean waits** were needed. Bootstrap used the pinned leanelab wrapper;
final checks use the official tree checker under the same shared-slot discipline. Text screens
ran one at a time under nice -n10; the sandboxed initial baseline screen could not lower priority
and logged that harmless native permission message. Later screens ran with the requested
priority. Development failures are retained (Bool embedding equation and frame/radius adapter
elaboration); final successful receipts and source hashes distinguish them from final checks.

## Copy screen: complete baseline, after and cumulative ledger

The required `scripts/copy-text-screen-v3.py` ran over all **26 Phase*.lean files including
Phases**, plus Build/Contract/Basic, Build/Contract/Seam, Build/Seam and Build/NDHost.
Both full logs, the exact population, per-pair dispositions, hashes and exact matched tile
spans are included. There are no omitted >=half pairs.

| Run | Screened declarations | Directed >=half pairs | Summed reproduced characters |
|---|---:|---:|---:|
| Exact base | 285 | 151 | 30442 |
| Delivered | 284 | 140 | 26358 |
| Difference | -1 | -11 | -4084 |

Twelve former pairs disappear, including both directions of the 661-character seq overlap and
806-character packaging overlap, and the two duplicated Unit/Bool records. Of the 140 remaining
pairs, 138 have unchanged normalized bodies, one is the same native-test adapter pair with the
same 188/343 overlap after its Bool-map edit, and one is the merged certificate/PhaseRow record
interface (159/300). The latter replaces the old records' corresponding interface matches;
it is not a new copied proof. Neither shared certificate seq nor shared packaging appears in
any remaining >=half pair. Segment algebra is cited regardless of its former textual score.

The following ledger is cumulative over the **whole supplied population**, including unchanged
construction homes. Counts and sums are directed screen accounting; they double-count
bidirectional matches and overlapping tiles across different pairs and therefore are **not**
unique lines or an assertion that each match is copied proved material. `copy-audit.json`
contains each involved declaration/body span, every tile's exact source/target line range and
normalized offset, shared characters, denominator, fraction, baseline status and explicit reason.
Frozen-home similarities and structural/contract adapters are reported rather than silently
excluded. This report does not request acceptance of either repaired major as debt.

| File | Distinct matched target declarations before/after | Directed pairs before/after | Summed chars before/after |
|---|---:|---:|---:|
| `PhaseAtoms.lean` | 3 / 3 | 3 / 3 | 533 / 533 |
| `PhaseBlock.lean` | 2 / 1 | 3 / 1 | 1075 / 159 |
| `PhaseBounds.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseBranchMachines.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseBranching.lean` | 2 / 0 | 2 / 0 | 1467 / 0 |
| `PhaseCoin.lean` | 2 / 1 | 2 / 1 | 190 / 95 |
| `PhaseCompute.lean` | 5 / 5 | 8 / 8 | 1967 / 1967 |
| `PhaseControl.lean` | 1 / 0 | 1 / 0 | 806 / 0 |
| `PhaseCore.lean` | 3 / 2 | 9 / 8 | 874 / 699 |
| `PhaseEmit.lean` | 4 / 3 | 6 / 5 | 727 / 603 |
| `PhaseFork.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseHost.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseInput.lean` | 1 / 1 | 2 / 2 | 596 / 596 |
| `PhaseInvariant.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseLayout.lean` | 1 / 1 | 1 / 1 | 98 / 98 |
| `PhaseMemory.lean` | 3 / 3 | 6 / 6 | 515 / 515 |
| `PhaseMemoryMachines.lean` | 6 / 6 | 17 / 17 | 3615 / 3615 |
| `PhaseOperations.lean` | 4 / 4 | 8 / 8 | 2569 / 2569 |
| `PhaseRegister.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseRows.lean` | 4 / 4 | 8 / 8 | 2186 / 2186 |
| `PhaseSchedules.lean` | 3 / 3 | 4 / 4 | 966 / 966 |
| `PhaseSemantics.lean` | 1 / 1 | 1 / 1 | 251 / 251 |
| `PhaseTable.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseTape.lean` | 0 / 0 | 0 / 0 | 0 / 0 |
| `PhaseTests.lean` | 2 / 1 | 4 / 1 | 689 / 188 |
| `Phases.lean` | 1 / 1 | 1 / 1 | 125 / 125 |
| `Contract/Basic.lean` | 15 / 15 | 22 / 22 | 3184 / 3184 |
| `Contract/Seam.lean` | 7 / 7 | 7 / 7 | 3115 / 3115 |
| `Seam.lean` | 11 / 11 | 15 / 15 | 1736 / 1736 |
| `NDHost.lean` | 12 / 12 | 21 / 21 | 3158 / 3158 |

All remaining directed pairs and reasons (the two span ranges are target/source screen-extracted
body spans; exact subspans are in the JSON tiles):

| # | Target reproduces source | Shared/source chars | Body lines target/source | Baseline status and reason retained |
|---|---|---:|---|---|
| 1 | `Contract/Seam::branch_positive` → `Contract/Seam::seq_positive` | 62/62 (100.0%) | 824–829 / 801–804 | baseline; Unchanged construction-home positivity adapters: both discharge positivity from their published composition time equations. These frozen homes are outside this job. |
| 2 | `Seam::seamComp_step_left` → `Seam::seamReleaseTM_step_inr` | 132/135 (97.8%) | 185–199 / 799–812 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 3 | `Basic::RoundContract` → `Basic::ReturnContract` | 412/436 (94.5%) | 872–897 / 370–411 | baseline; Unchanged construction-home record fields: finite-run/return/round contracts share endpoint, cut and envelope data but impose different return or repeated-round interfaces. Both files are frozen outside this job. |
| 4 | `NDHost::phaseHostND` → `Seam::phaseHostTM` | 111/120 (92.5%) | 110–117 / 901–908 | baseline; Unchanged deterministic/nondeterministic registered-host definitions. Their redirect and mapped-action branches coincide structurally; this job consumes their contracts and does not copy either implementation. |
| 5 | `PhaseRows::phase_unaryRow` → `PhaseRows::phase_intRow` | 385/420 (91.7%) | 269–287 / 147–162 | baseline; Unchanged native-row adapters: select the arithmetic bank, supply the native row premise, and cite shared phase_wordRow/phase_nativeRow plus embedding readers. Constants, unary and binary arithmetic have different native contracts and frame updates; no seam/packaging proof is copied. |
| 6 | `PhaseSchedules::phase_storeImmediateBlock` → `PhaseSchedules::phase_fetchBlock` | 202/222 (91.0%) | 62–72 / 45–54 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 7 | `Seam::phaseHostTM` → `NDHost::phaseHostND` | 111/122 (91.0%) | 901–908 / 110–117 | baseline; Unchanged deterministic/nondeterministic registered-host definitions. Their redirect and mapped-action branches coincide structurally; this job consumes their contracts and does not copy either implementation. |
| 8 | `NDHost::guessRunTM_runWith_live` → `NDHost::guessRunTM_runWith_handoff_state` | 81/93 (87.1%) | 1278–1294 / 1307–1327 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 9 | `NDHost::guessRunTM_runWith` → `NDHost::guessRunTM_runWith_handoff_state` | 81/93 (87.1%) | 1343–1368 / 1307–1327 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 10 | `Seam::seamCompTM_spaceUsed_le_add` → `Seam::seamCompTM_visitedByTapeHead` | 98/115 (85.2%) | 562–580 / 467–480 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 11 | `Basic::Cfg.SameOutside.keep_blank` → `Basic::endpoint_not_mem` | 97/114 (85.1%) | 322–333 / 615–626 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 12 | `Contract/Seam::seq_positive` → `Contract/Seam::branch_positive` | 62/73 (84.9%) | 801–804 / 824–829 | baseline; Unchanged construction-home positivity adapters: both discharge positivity from their published composition time equations. These frozen homes are outside this job. |
| 13 | `Basic::safeSegment_iff` → `Basic::segment_iff` | 84/99 (84.8%) | 577–596 / 435–443 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 14 | `Basic::time_box` → `Basic::time_envelope` | 123/146 (84.2%) | 806–818 / 697–717 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 15 | `PhaseRows::phase_arithRow` → `PhaseRows::phase_unaryRow` | 415/493 (84.2%) | 222–241 / 269–287 | baseline; Unchanged native-row adapters: select the arithmetic bank, supply the native row premise, and cite shared phase_wordRow/phase_nativeRow plus embedding readers. Constants, unary and binary arithmetic have different native contracts and frame updates; no seam/packaging proof is copied. |
| 16 | `PhaseLayout::phase_keyAssign_layout_mono` → `PhaseLayout::phase_tableOf_layout_bound` | 98/119 (82.4%) | 119–130 / 104–108 | baseline; Unchanged layout-bound adapters sharing the same nonnegative/cardinality arithmetic; assignment uses its keyed-update layout theorem, while the canonical table uses its table layout theorem. |
| 17 | `Basic::hullLo` → `Basic::hullHi` | 114/139 (82.0%) | 990–997 / 1005–1012 | baseline; Unchanged dual lower/upper hull equations in the frozen construction home; the only differing operation is the appropriate minimum/maximum. |
| 18 | `Basic::hullHi` → `Basic::hullLo` | 114/139 (82.0%) | 1005–1012 / 990–997 | baseline; Unchanged dual lower/upper hull equations in the frozen construction home; the only differing operation is the appropriate minimum/maximum. |
| 19 | `PhaseCompute::phase_arithBlock` → `PhaseCompute::phase_sourceBlock` | 276/343 (80.5%) | 50–73 / 86–100 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 20 | `PhaseEmit::phase_frame_emit_encodes` → `PhaseTape::phase_encodes_congr` | 61/76 (80.3%) | 122–138 / 61–70 | baseline; Unchanged encoding field-congruence glue: emission preserves the encoded memory/tape fields, so its adapter uses the existing encoding congruence reader with the same equality premises. |
| 21 | `Seam::seamCompTM_visitedByTapeHead` → `Seam::seamCompTM_spaceUsed_le_add` | 98/123 (79.7%) | 467–480 / 562–580 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 22 | `NDHost::guessCtlRunTM_runWith` → `NDHost::guessRunTM_runWith` | 432/548 (78.8%) | 1787–1818 / 1343–1368 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 23 | `PhaseCompute::phase_inputBlock` → `PhaseCompute::phase_sourceBlock` | 270/343 (78.7%) | 140–164 / 86–100 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 24 | `PhaseRows::phase_intRow` → `PhaseRows::phase_unaryRow` | 385/493 (78.1%) | 147–162 / 269–287 | baseline; Unchanged native-row adapters: select the arithmetic bank, supply the native row premise, and cite shared phase_wordRow/phase_nativeRow plus embedding readers. Constants, unary and binary arithmetic have different native contracts and frame updates; no seam/packaging proof is copied. |
| 25 | `PhaseRows::phase_arithRow` → `PhaseRows::phase_intRow` | 327/420 (77.9%) | 222–241 / 147–162 | baseline; Unchanged native-row adapters: select the arithmetic bank, supply the native row premise, and cite shared phase_wordRow/phase_nativeRow plus embedding readers. Constants, unary and binary arithmetic have different native contracts and frame updates; no seam/packaging proof is copied. |
| 26 | `Basic::endpoint_not_mem` → `Basic::traj_iff` | 80/103 (77.7%) | 615–626 / 1119–1127 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 27 | `Basic::Frames.trans` → `Basic::traj_iff` | 80/103 (77.7%) | 1178–1203 / 1119–1127 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 28 | `Basic::Cfg.SameOutside.keep_blank` → `Basic::traj_iff` | 80/103 (77.7%) | 322–333 / 1119–1127 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 29 | `Seam::seamCompTM_run` → `Seam::seamCompTM_visitedByTapeHead` | 89/115 (77.4%) | 393–414 / 467–480 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 30 | `Seam::seamCompTM_firstReturn` → `Seam::seamCompTM_run` | 181/234 (77.4%) | 429–453 / 393–414 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 31 | `Basic::round_iff` → `Basic::segment_iff` | 75/99 (75.8%) | 759–769 / 435–443 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 32 | `PhaseAtoms::phase_intBlock` → `PhaseCompute::phase_sourceBlock` | 259/343 (75.5%) | 81–98 / 86–100 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 33 | `Seam::seamCompTM` → `Seam::seamReleaseTM` | 148/196 (75.5%) | 139–152 / 773–785 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 34 | `NDHost::ndWriterTM_run_block` → `NDHost::wr_prefix` | 116/154 (75.3%) | 447–464 / 380–392 | baseline; Unchanged writer-host prefix/block proof setup in the frozen NDHost home; different prefix/block conclusions consume the same host run equations. |
| 35 | `PhaseOperations::phase_inputSchedule` → `PhaseOperations::phase_halfSchedule` | 288/383 (75.2%) | 83–98 / 67–77 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 36 | `Basic::segment_iff` → `Basic::round_iff` | 75/102 (73.5%) | 435–443 / 759–769 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 37 | `Basic::safeSegment_iff` → `Basic::round_iff` | 75/102 (73.5%) | 577–596 / 759–769 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 38 | `PhaseOperations::phase_loadSchedule` → `PhaseOperations::phase_inputSchedule` | 297/404 (73.5%) | 104–127 / 83–98 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 39 | `Basic::endpoint_not_mem` → `Basic::Cfg.SameOutside.keep_blank` | 97/132 (73.5%) | 615–626 / 322–333 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 40 | `Basic::ReturnContract` → `Basic::RoundContract` | 412/566 (72.8%) | 370–411 / 872–897 | baseline; Unchanged construction-home record fields: finite-run/return/round contracts share endpoint, cut and envelope data but impose different return or repeated-round interfaces. Both files are frozen outside this job. |
| 41 | `PhaseMemoryMachines::phase_loadMachine` → `PhaseMemoryMachines::phase_inputMachine` | 259/356 (72.8%) | 81–94 / 138–151 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 42 | `PhaseCompute::phase_signExtendBlock` → `PhaseCompute::phase_halfBlock` | 157/216 (72.7%) | 120–133 / 107–113 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 43 | `Seam::seamCompTM_spaceUsedByTape_le_max` → `Seam::seamCompTM_spaceUsedByTape_le_add` | 92/127 (72.4%) | 597–636 / 538–548 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 44 | `PhaseMemoryMachines::phase_inputMachine` → `PhaseMemoryMachines::phase_loadMachine` | 259/359 (72.1%) | 138–151 / 81–94 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 45 | `Basic::locate` → `Basic::cut` | 219/305 (71.8%) | 1375–1410 / 1354–1370 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 46 | `Seam::seamCompTM_run` → `Seam::seamCompTM_spaceUsed_le_add` | 88/123 (71.5%) | 393–414 / 562–580 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 47 | `Phases::exists_phase` → `PhaseControl::PhaseMachine.weaken` | 125/175 (71.4%) | 137–250 / 125–137 | baseline; Unchanged packaging/projection tail: the headline installs a chosen internal machine into the frozen external certificate, while weaken retains that machine and changes predicates. Both copy existing fields and adapt a run; neither reimplements finite-exit packaging. |
| 48 | `PhaseOperations::phase_halfSchedule` → `PhaseOperations::phase_inputSchedule` | 288/404 (71.3%) | 67–77 / 83–98 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 49 | `PhaseSchedules::phase_binarySchedule` → `PhaseOperations::phase_unarySchedule` | 115/163 (70.6%) | 96–116 / 53–61 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 50 | `PhaseCore::PhaseFrame.ofCfg` → `Contract/Seam::_root_.Turing.Cfg.bindState` | 86/122 (70.5%) | 50–55 / 198–213 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 51 | `Seam::seamCompTM_run` → `Seam::seamCompTM_firstReturn` | 181/257 (70.4%) | 393–414 / 429–453 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 52 | `PhaseOperations::phase_loadSchedule` → `PhaseOperations::phase_halfSchedule` | 269/383 (70.2%) | 104–127 / 67–77 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 53 | `Basic::traj_iff` → `Basic::endpoint_not_mem` | 80/114 (70.2%) | 1119–1127 / 615–626 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 54 | `Basic::Frames.trans` → `Basic::endpoint_not_mem` | 80/114 (70.2%) | 1178–1203 / 615–626 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 55 | `NDHost::GuessRunPhase.instDecidableEqCtlState` → `NDHost::GuessRunPhase.instFintypeCtlState` | 162/232 (69.8%) | 604–613 / 592–600 | baseline; Unchanged finite-control instance enumerations in the frozen nondeterministic host. Equality and finiteness enumerate the same control tags but supply different instances. |
| 56 | `PhaseMemoryMachines::phase_inputMachine` → `PhaseMemoryMachines::phase_halfMachine` | 223/321 (69.5%) | 138–151 / 120–133 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 57 | `NDHost::guessRunTM_runWith_handoff` → `NDHost::guessCtlRunTM_runWith_handoff` | 301/434 (69.4%) | 1247–1267 / 1745–1769 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 58 | `PhaseSemantics::phase_post_of_write` → `PhaseBranchMachines::phase_post_of_read` | 251/362 (69.3%) | 78–98 / 48–58 | baseline; Unchanged RAM postcondition adapters: read the phase-state encoding and transport it to the extended RAM configuration through effect/xstep and encoding-congruence readers. A write changes memory; a read retains it. |
| 59 | `PhaseMemoryMachines::phase_loadMachine` → `PhaseMemoryMachines::phase_halfMachine` | 222/321 (69.2%) | 81–94 / 120–133 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 60 | `PhaseSchedules::phase_fetchBlock` → `PhaseSchedules::phase_storeImmediateBlock` | 202/294 (68.7%) | 45–54 / 62–72 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 61 | `Seam::seamCompTM_spaceUsed_le_add_ofCfg` → `Seam::seamCompTM_spaceUsedByTape_le_add` | 87/127 (68.5%) | 510–524 / 538–548 | baseline; Unchanged nondeterministic-host configuration constructors copy their input, tapes, heads and output fields into different control layouts; baseline record syntax, not a new proof. |
| 62 | `Contract/Seam::RoundContract.release` → `Contract/Seam::ReturnContract.release` | 774/1135 (68.2%) | 617–668 / 564–612 | baseline; Unchanged return/round release combinator proofs in the frozen Contract/Seam home. Their similar endpoint/envelope transport predates the job and is included in the baseline ledger. |
| 63 | `PhaseCore::PhaseFrame.cfg` → `PhaseCore::PhaseFrame.ofCfg` | 94/138 (68.1%) | 60–65 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 64 | `PhaseInput::phase_inputRow` → `PhaseRows::phase_wordRow` | 151/223 (67.7%) | 61–109 / 86–95 | baseline; Unchanged native placement adapters: select the bank, establish scratch/word premises, embed the native contract and recover the frame. Input additionally controls inputPos; arithmetic uses its own native word row. Their reused transport is supplied by shared phase_reaches_embed and frame readers. |
| 65 | `PhaseMemory::PhaseFrame.assign` → `PhaseRows::PhaseFrame.write` | 87/129 (67.4%) | 180–187 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 66 | `PhaseEmit::PhaseFrame.emit` → `PhaseRows::PhaseFrame.write` | 87/129 (67.4%) | 38–43 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 67 | `PhaseInput::phase_inputRow` → `PhaseRows::phase_arithRow` | 445/664 (67.0%) | 61–109 / 222–241 | baseline; Unchanged native placement adapters: select the bank, establish scratch/word premises, embed the native contract and recover the frame. Input additionally controls inputPos; arithmetic uses its own native word row. Their reused transport is supplied by shared phase_reaches_embed and frame readers. |
| 68 | `PhaseCore::PhaseFrame.ofCfg` → `PhaseRows::PhaseFrame.write` | 86/129 (66.7%) | 50–55 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 69 | `PhaseCore::PhaseFrame.cfg` → `PhaseRows::PhaseFrame.write` | 86/129 (66.7%) | 60–65 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 70 | `PhaseMemoryMachines::phase_loadMachine` → `PhaseMemoryMachines::phase_oneMachine` | 228/343 (66.5%) | 81–94 / 43–56 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 71 | `Seam::seamCompTM_firstReturn` → `Seam::seamCompTM_visitedByTapeHead` | 76/115 (66.1%) | 429–453 / 467–480 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 72 | `PhaseRows::PhaseFrame.write` → `PhaseEmit::PhaseFrame.emit` | 87/134 (64.9%) | 41–46 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 73 | `PhaseMemory::PhaseFrame.assign` → `PhaseEmit::PhaseFrame.emit` | 87/134 (64.9%) | 180–187 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 74 | `PhaseMemory::phaseMemoryEntries` → `PhaseBlock::PhaseState` | 66/102 (64.7%) | 49–56 / 145–149 | baseline; Screen extraction includes adjacent type/record formula text: both refer to encoded cells/configurations and a frame cfg. These are different definitions (canonical entries versus state invariant), not copied proofs. |
| 75 | `PhaseCore::PhaseFrame.ofCfg` → `PhaseEmit::PhaseFrame.emit` | 86/134 (64.2%) | 50–55 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 76 | `PhaseCore::PhaseFrame.cfg` → `PhaseEmit::PhaseFrame.emit` | 86/134 (64.2%) | 60–65 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 77 | `PhaseCore::PhaseFrame.ofCfg` → `PhaseCore::PhaseFrame.cfg` | 94/147 (63.9%) | 50–55 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 78 | `PhaseMemoryMachines::phase_oneMachine` → `PhaseMemoryMachines::phase_loadMachine` | 228/359 (63.5%) | 43–56 / 81–94 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 79 | `NDHost::GuessRunPhase.instFintypeCtlState` → `NDHost::GuessRunPhase.instDecidableEqCtlState` | 162/256 (63.3%) | 592–600 / 604–613 | baseline; Unchanged finite-control instance enumerations in the frozen nondeterministic host. Equality and finiteness enumerate the same control tags but supply different instances. |
| 80 | `PhaseMemoryMachines::phase_halfMachine` → `PhaseMemoryMachines::phase_inputMachine` | 223/356 (62.6%) | 120–133 / 138–151 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 81 | `PhaseRows::phase_unaryRow` → `PhaseRows::phase_arithRow` | 415/664 (62.5%) | 269–287 / 222–241 | baseline; Unchanged native-row adapters: select the arithmetic bank, supply the native row premise, and cite shared phase_wordRow/phase_nativeRow plus embedding readers. Constants, unary and binary arithmetic have different native contracts and frame updates; no seam/packaging proof is copied. |
| 82 | `Contract/Seam::_root_.Turing.Cfg.bindState` → `PhaseCore::PhaseFrame.ofCfg` | 86/138 (62.3%) | 198–213 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 83 | `PhaseRows::PhaseFrame.write` → `PhaseCore::PhaseFrame.ofCfg` | 86/138 (62.3%) | 41–46 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 84 | `PhaseMemory::PhaseFrame.assign` → `PhaseCore::PhaseFrame.ofCfg` | 86/138 (62.3%) | 180–187 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 85 | `PhaseEmit::PhaseFrame.emit` → `PhaseCore::PhaseFrame.ofCfg` | 86/138 (62.3%) | 38–43 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 86 | `Basic::RoundContract` → `Basic::Contract` | 302/487 (62.0%) | 872–897 / 145–170 | baseline; Unchanged construction-home record fields: finite-run/return/round contracts share endpoint, cut and envelope data but impose different return or repeated-round interfaces. Both files are frozen outside this job. |
| 87 | `PhaseMemoryMachines::phase_halfMachine` → `PhaseMemoryMachines::phase_loadMachine` | 222/359 (61.8%) | 120–133 / 81–94 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 88 | `Seam::seamReleaseTM_step_inr` → `Seam::seamComp_step_left` | 132/216 (61.1%) | 799–812 / 185–199 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 89 | `PhaseOperations::phase_storeSchedule` → `PhaseOperations::phase_loadSchedule` | 391/641 (61.0%) | 133–152 / 104–127 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 90 | `PhaseCompute::phase_inputBlock` → `PhaseAtoms::phase_intBlock` | 269/441 (61.0%) | 140–164 / 81–98 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 91 | `Seam::seamCompTM_firstReturn` → `Seam::seamCompTM_spaceUsed_le_add` | 75/123 (61.0%) | 429–453 / 562–580 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 92 | `Basic::traj_iff` → `Basic::Cfg.SameOutside.keep_blank` | 80/132 (60.6%) | 1119–1127 / 322–333 | baseline; Unchanged construction-home characterization/endpoint clauses. The screen includes common formula tails surrounding definitional readers; these are not new phase proofs. The frozen homes are outside this job. |
| 93 | `Basic::Frames.trans` → `Basic::Cfg.SameOutside.keep_blank` | 80/132 (60.6%) | 1178–1203 / 322–333 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 94 | `PhaseMemoryMachines::phase_storeMachine` → `PhaseMemoryMachines::phase_loadMachine` | 217/359 (60.4%) | 99–115 / 81–94 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 95 | `PhaseCompute::phase_halfBlock` → `PhaseCompute::phase_signExtendBlock` | 157/260 (60.4%) | 107–113 / 120–133 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 96 | `NDHost::guessRunCfg` → `PhaseCore::PhaseFrame.ofCfg` | 83/138 (60.1%) | 838–854 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 97 | `NDHost::guessRunCfg` → `PhaseCore::PhaseFrame.cfg` | 88/147 (59.9%) | 838–854 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 98 | `PhaseCoin::phase_encoded_heads` → `PhaseRegister::phase_frame_scratch` | 95/159 (59.7%) | 43–56 / 39–47 | baseline; Unchanged projections of the same encodes_iff witness: one reads the head center and the other reads scratch blankness. Shared destructuring syntax is incidental; conclusions differ. |
| 99 | `NDHost::guessRunTM_runWith` → `NDHost::guessCtlRunTM_runWith` | 432/726 (59.5%) | 1343–1368 / 1787–1818 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 100 | `PhaseCompute::phase_sourceBlock` → `PhaseAtoms::phase_intBlock` | 259/441 (58.7%) | 86–100 / 81–98 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 101 | `PhaseOperations::phase_storeSchedule` → `PhaseSchedules::phase_binarySchedule` | 447/763 (58.6%) | 133–152 / 96–116 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 102 | `PhaseRows::PhaseFrame.write` → `PhaseCore::PhaseFrame.cfg` | 86/147 (58.5%) | 41–46 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 103 | `PhaseMemory::PhaseFrame.assign` → `PhaseCore::PhaseFrame.cfg` | 86/147 (58.5%) | 180–187 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 104 | `PhaseEmit::PhaseFrame.emit` → `PhaseCore::PhaseFrame.cfg` | 86/147 (58.5%) | 38–43 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 105 | `PhaseMemoryMachines::phase_storeMachine` → `PhaseMemoryMachines::phase_oneMachine` | 200/343 (58.3%) | 99–115 / 43–56 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 106 | `PhaseCompute::phase_arithBlock` → `PhaseAtoms::phase_intBlock` | 257/441 (58.3%) | 50–73 / 81–98 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 107 | `Seam::seamReleaseTM` → `Seam::seamCompTM` | 148/254 (58.3%) | 773–785 / 139–152 | baseline; Unchanged seam construction-home readers and run/space corollaries: the same mapped step or run equation supplies distinct endpoint, first-return or head-visit bounds. Both homes are frozen outside this job. |
| 108 | `NDHost::guessRunCfg` → `NDHost::wr_cfg` | 135/232 (58.2%) | 838–854 / 242–254 | baseline; Unchanged nondeterministic-host configuration constructors copy their input, tapes, heads and output fields into different control layouts; baseline record syntax, not a new proof. |
| 109 | `NDHost::streamStartCfg` → `PhaseRows::PhaseFrame.write` | 75/129 (58.1%) | 856–865 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 110 | `NDHost::guessRunCfg` → `PhaseRows::PhaseFrame.write` | 75/129 (58.1%) | 838–854 / 41–46 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 111 | `Contract/Seam::ReturnContract.release` → `Contract/Seam::RoundContract.release` | 774/1336 (57.9%) | 564–612 / 617–668 | baseline; Unchanged return/round release combinator proofs in the frozen Contract/Seam home. Their similar endpoint/envelope transport predates the job and is included in the baseline ledger. |
| 112 | `PhaseAtoms::phase_constBlock` → `PhaseAtoms::phase_keyBlock` | 137/237 (57.8%) | 116–129 / 102–111 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 113 | `PhaseMemoryMachines::phase_oneMachine` → `PhaseMemoryMachines::phase_halfMachine` | 185/321 (57.6%) | 43–56 / 120–133 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 114 | `PhaseSchedules::phase_binarySchedule` → `PhaseOperations::phase_storeSchedule` | 447/777 (57.5%) | 96–116 / 133–152 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 115 | `Basic::time_envelope` → `Basic::time_box` | 123/215 (57.2%) | 697–717 / 806–818 | baseline; Unchanged contract projection/transport glue in the frozen Basic home: destruct a contract witness, retain its endpoint/cut/envelope or infer blankness. The overlap is baseline construction material, not a new phase proof. |
| 116 | `PhaseMemoryMachines::phase_binaryMachine` → `PhaseMemoryMachines::phase_loadMachine` | 203/359 (56.5%) | 62–76 / 81–94 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 117 | `PhaseMemoryMachines::phase_binaryMachine` → `PhaseMemoryMachines::phase_oneMachine` | 192/343 (56.0%) | 62–76 / 43–56 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 118 | `NDHost::streamStartCfg` → `PhaseEmit::PhaseFrame.emit` | 75/134 (56.0%) | 856–865 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 119 | `NDHost::guessRunCfg` → `PhaseEmit::PhaseFrame.emit` | 75/134 (56.0%) | 838–854 / 38–43 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 120 | `PhaseCompute::phase_inputBlock` → `PhaseCompute::phase_arithBlock` | 322/579 (55.6%) | 140–164 / 50–73 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 121 | `NDHost::streamStartCfg` → `PhaseCore::PhaseFrame.cfg` | 81/147 (55.1%) | 856–865 / 60–65 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 122 | `NDHost::streamStartCfg` → `PhaseCore::PhaseFrame.ofCfg` | 76/138 (55.1%) | 856–865 / 50–55 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 123 | `PhaseTests::phase_testBlock` → `PhaseCompute::phase_sourceBlock` | 188/343 (54.8%) | 90–117 / 86–100 | existing pair, edited body; Existing native-row adapter overlap (188/343 in both runs): select the arithmetic bank, supply the known word and scratch, embed and enlarge native bounds. The edited test additionally installs an injective Bool exit map and reads Bool.range_eq; it cites the shared packaging rather than copying it. |
| 124 | `PhaseAtoms::phase_keyBlock` → `PhaseAtoms::phase_constBlock` | 137/250 (54.8%) | 102–111 / 116–129 | baseline; Unchanged block adapters over different native rows: choose its row witness, invoke PhaseBlock.ofRow, and provide its register/frame postcondition and allowance inequalities. The common block construction and sequencing are factored separately. |
| 125 | `PhaseMemoryMachines::phase_halfMachine` → `PhaseMemoryMachines::phase_oneMachine` | 185/343 (53.9%) | 120–133 / 43–56 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 126 | `PhaseEmit::phase_emitMachine` → `PhaseBranchMachines::phase_bltzMachine` | 283/529 (53.5%) | 141–174 / 84–100 | baseline; Unchanged instruction-specific final wrappers: both adapt a selected native Boolean test and weaken the encoded postcondition. Emission joins two continuations through phase_forkMachine; signed branch keeps the routed jump. Shared routing/packaging proofs are cited. |
| 127 | `Contract/Seam::Traj.seq` → `Contract/Seam::Frames.seq` | 163/305 (53.4%) | 678–697 / 707–721 | baseline; Unchanged construction-home adapters composing framed and trajectory contracts; both cite the shared seam contract with their different wrapper fields. |
| 128 | `Basic::Contract` → `Basic::RoundContract` | 302/566 (53.4%) | 145–170 / 872–897 | baseline; Unchanged construction-home record fields: finite-run/return/round contracts share endpoint, cut and envelope data but impose different return or repeated-round interfaces. Both files are frozen outside this job. |
| 129 | `PhaseMemoryMachines::phase_inputMachine` → `PhaseMemoryMachines::phase_oneMachine` | 183/343 (53.4%) | 138–151 / 43–56 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 130 | `PhaseBlock::PhaseCertificate` → `PhaseCore::PhaseRow` | 159/300 (53.0%) | 45–58 / 89–109 | new pair; Record interface fields, not a copied proof: an existential postcondition certificate and an exact frame-transforming row both store finite control and a bounded run. This replaces the two former Unit/Bool records; only one certificate composition and packaging proof remains. |
| 131 | `PhaseOperations::phase_storeSchedule` → `PhaseOperations::phase_halfSchedule` | 198/383 (51.7%) | 133–152 / 67–77 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 132 | `PhaseMemoryMachines::phase_oneMachine` → `PhaseMemoryMachines::phase_inputMachine` | 183/356 (51.4%) | 43–56 / 138–151 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 133 | `NDHost::guessCtlRunTM_runWith_handoff` → `NDHost::guessRunTM_runWith_handoff` | 301/588 (51.2%) | 1745–1769 / 1247–1267 | baseline; Unchanged guess-host run/handoff proofs in the frozen NDHost home. They share the fixed-choice/host transport setup but establish the stated live, handoff or controlled endpoint; included unchanged in the baseline. |
| 134 | `Contract/Seam::branch` → `Contract/Seam::seq` | 1194/2353 (50.7%) | 410–542 / 140–196 | baseline; Unchanged generic branch/sequential construction proofs in the frozen Contract/Seam home. The baseline already contains this shared seam setup; the phase refactor cites these contracts. |
| 135 | `PhaseMemory::phase_assignRow` → `PhaseMemory::phase_frame_assign_encodes` | 103/203 (50.7%) | 209–239 / 245–251 | baseline; Unchanged assignment adapters both obtain layout/write invariants and read frame fields, but one certifies the bounded native run while the other establishes the encoded keyed-memory postcondition. |
| 136 | `PhaseMemoryMachines::phase_loadMachine` → `PhaseMemoryMachines::phase_binaryMachine` | 203/401 (50.6%) | 81–94 / 62–76 | baseline; Unchanged instruction-specific adapters: obtain the named schedule, cite shared phase_machine_ofBlock, and weaken its postcondition using the RAM step reader. The shared fresh-entry, run and allowance proof lives only in phase_machine_ofCertificate. |
| 137 | `NDHost::wr_cfg` → `NDHost::guessRunCfg` | 135/268 (50.4%) | 242–254 / 838–854 | baseline; Unchanged nondeterministic-host configuration constructors copy their input, tapes, heads and output fields into different control layouts; baseline record syntax, not a new proof. |
| 138 | `PhaseOperations::phase_loadSchedule` → `PhaseOperations::phase_storeSchedule` | 391/777 (50.3%) | 104–127 / 133–152 | baseline; Unchanged instruction schedules: common register specifications and fetch/store citations recur, but the instruction-dependent middle operation and dependency order differ. Actual block composition now resolves to the single PhaseCertificate.seq proof. |
| 139 | `PhaseCore::PhaseFrame.cfg` → `NDHost::streamStartCfg` | 81/161 (50.3%) | 60–65 / 856–865 | baseline; Existing configuration/frame record syntax: the constructors preserve input position, work tapes, heads and output while installing, erasing, binding or changing control/one frame field. These term bodies are distinct operations, not copied tactic proofs. |
| 140 | `NDHost::guessRunCfg` → `NDHost::streamStartCfg` | 81/161 (50.3%) | 838–854 / 856–865 | baseline; Unchanged nondeterministic-host configuration constructors copy their input, tapes, heads and output fields into different control layouts; baseline record syntax, not a new proof. |

All baseline pairs absent after the refactor:

| Former target → source | Baseline shared/source |
|---|---:|
| `PhaseBranching::PhaseBranch.seq` → `PhaseBlock::PhaseBlock.seq` | 661/747 (88.5%) |
| `PhaseControl::phase_machine_ofBlock` → `PhaseBranching::phase_machine_ofBranch` | 806/1035 (77.9%) |
| `PhaseBlock::PhaseBlock.seq` → `PhaseBranching::PhaseBranch.seq` | 661/858 (77.0%) |
| `PhaseTests::PhaseBranch` → `PhaseBlock::PhaseBlock` | 239/313 (76.4%) |
| `PhaseBlock::PhaseBlock` → `PhaseTests::PhaseBranch` | 239/323 (74.0%) |
| `PhaseEmit::phase_emitBlock` → `PhaseControl::phase_reaches_zero` | 124/190 (65.3%) |
| `PhaseBranching::phase_machine_ofBranch` → `PhaseControl::phase_machine_ofBlock` | 806/1290 (62.5%) |
| `PhaseBlock::PhaseBlock` → `PhaseCore::PhaseRow` | 175/300 (58.3%) |
| `PhaseCore::PhaseRow` → `PhaseBlock::PhaseBlock` | 175/313 (55.9%) |
| `PhaseTests::PhaseBranch` → `PhaseCore::PhaseRow` | 159/300 (53.0%) |
| `PhaseTests::phase_testBlock` → `PhaseRows::phase_nativeRow` | 103/203 (50.7%) |
| `PhaseCoin::phase_choiceMachine` → `PhaseControl::phase_reaches_zero` | 95/190 (50.0%) |

## Patch and delivery

```text
 TCSlib/Complexity/RAMSimulation.lean               |   4 +-
 .../Complexity/RAMSimulation/Sim/PhaseBlock.lean   |  82 ++++++++-----
 .../RAMSimulation/Sim/PhaseBranchMachines.lean     |   4 +-
 .../RAMSimulation/Sim/PhaseBranching.lean          |  85 ++------------
 .../Complexity/RAMSimulation/Sim/PhaseCompute.lean |   6 +-
 .../Complexity/RAMSimulation/Sim/PhaseControl.lean | 130 +++++++++++++--------
 TCSlib/Complexity/RAMSimulation/Sim/PhaseFork.lean |  12 +-
 TCSlib/Complexity/RAMSimulation/Sim/PhaseHost.lean |  45 +++----
 .../RAMSimulation/Sim/PhaseSchedules.lean          |   2 +-
 .../Complexity/RAMSimulation/Sim/PhaseTests.lean   |  30 ++---
 10 files changed, 191 insertions(+), 209 deletions(-)
```

The archive contains REPORT.md, all 26 delivered owned files, the facade, the base-relative
patch, check/probe scripts and logs, full graph exports, and all pinned citation homes. No
olean, package tree, toolchain or compiled binary is shipped. Scratch probes are archived as
`.lean.txt`; rename to `.lean` to replay them. Paths referenced above are under `evidence/logs/`
unless a source/probe path is given. `SHA256SUMS` covers every other archive entry.

Delivery is only `arora-barak-ch3-4/inbox/fill-ram-phases/fill-ram-phases-r3.zip` on
`exchange/pass-shelat-ch5-8`, after `git pull --rebase`, without force or a source-branch push.
A separate managed delivery checkout avoids the shared exchange checkout's unrelated ahead
commit and untracked inbox files. Existing source-checkout blueprint edits are preserved and
excluded from the commit/patch/archive. No checkpoint is required for this completed round.
