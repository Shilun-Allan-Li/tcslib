# C1 interpreter core continuation 1 — E-RES partial delivery

**This is an environment report with unverified proof drafts, not a verified Lean fill.**
`Turing.exists_ndInterpreterCore` remains exactly `by sorry`. No complete interpreter assembly
phase is claimed. Sixteen new private declarations supplement the four supplied drafts, but
none was elaborated in this session. They must not be integrated as checked proofs.

The cache command failed with 1,952 download failures (CONNECT tunnel response 403). After the
prescribed cleanup, the retry preflight found **11.923400879 GiB free disk**, below the required
12 GiB. Work requiring Lean or the cache stopped with **E-RES**. The v2.1 memory calculation
passed: **7.545509338 GiB headroom**, no OOM event. This is not a page-cache shortage.
Independent source audits, duplication screens, reporting, and packaging were completed.

## Input identity, pin, and delivery

- Uploaded brief SHA-256:
  `5fefa735a099d3f2d542747063bc3070ed1ef7445cc876e1d1462a614bd9f194` — verified.
- Uploaded environment addendum v2.1 SHA-256:
  `2563c8d2ffed3e1fa268748edb017577522cec14a922ad2989d1aa974ab12d15` — verified;
  it supersedes all brief references to v2.
- Fresh clone: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initial checkout: `complexity/arora-barak-ch3-4`, tip
  `3de011c12bb05b97f572e6a7854a68f212125a4a`.
- The tip's `campaign/fills/c1/briefs/c1-fill-core-cont1.md` matched the attachment exactly after
  substituting its `@ANCESTOR@` placeholders. The non-normalized texts differ only there.
- `git merge-base --is-ancestor 96d60278e4fde29b986ec1d0e59cd07f768fe28a HEAD` passed before
  creating the fill branch.
- Base: **`96d60278e4fde29b986ec1d0e59cd07f768fe28a`**.
  Branch `fill/c1-core-cont1` was created at exactly this commit.
- Final HEAD: `f66a50f64829e4e393518742ed0b0d8e4c9538ba`.
- Commits, in order:
  1. `3dda9dab6545e8a11728d3839520ad6b7cff0ed3` — Draft interpreter-core components at the pinned base.
  2. `f66a50f64829e4e393518742ed0b0d8e4c9538ba` — Draft the represented replay tail with first live verdicts.
- No rebase, merge, cherry-pick, push, or PR. No `lake build` was invoked; only the cache tool's
  permitted internal validation/build machinery ran.
- Checkpoints written: `fill-c1-core-cont1-cp0.zip` (initial component drafts),
  `fill-c1-core-cont1-cp1.zip` (loop/verdict tail drafts), and
  `fill-c1-core-cont1-cp2.zip` (final E-RES report and static evidence). These are draft/evidence
  checkpoints, not assertions that an entire numbered assembly phase was completed.
- CP0 SHA-256: `3632d429689586334c3547bf7d40ef9ed5a8ccedd2ad77c4c7e212a5805b4255`.
  CP1 SHA-256: `a3d760a04e1b1dad017ba3f4baf3c434909164a0a8ea4985e93c71ffef945550`.
- Final delivery: `fill-c1-core-cont1.zip`, containing this report, the full owned source,
  two format patches against the base, a bundle whose sole prerequisite is the base,
  evidence logs including bootstrap/final/axiom skip records and both screens, the required
  shim source, and `SHA256SUMS`. No compiled shim, oleans, toolchain, or package tree is shipped.

## Resource preflight and authorized startup fallback

The preflight was performed before repository/cache/Lean work. Full raw counters, `df -B1`,
`df -T`, and processor output are in `evidence/logs/preflight.log` and
`evidence/logs/preflight-retry.log`. The clone, runtime, workspace scratch/TMPDIR, and `/tmp`
were on the disk-backed overlay filesystem; no tmpfs or `/dev/shm` was used.

| Field | Initial preflight | Cleaned-retry preflight |
|---|---:|---:|
| UTC | 2026-10-18 15:22:57 | 2026-10-18 15:59:11 |
| `nproc` | 9 | 9 |
| Free disk, bytes | 28,038,565,888 | 12,802,654,208 |
| Free disk, GiB | 26.112949371 | 11.923400879 |
| `memory.max`, bytes | 8,589,934,592 | 8,589,934,592 |
| `memory.current`, bytes (not used for headroom) | 4,192,235,520 | 6,760,271,872 |
| `anon`, bytes | 106,807,296 | 103,170,048 |
| `kernel`, bytes | 138,747,904 | 384,835,584 |
| `shmem`, bytes | 0 | 0 |
| In use = anon + kernel + shmem, bytes | 245,555,200 | 488,005,632 |
| Headroom = limit − in use, bytes | 8,344,379,392 | 8,101,928,960 |
| Headroom, GiB | 7.771308899 | 7.545509338 |
| `oom` / `oom_kill` | 0 / 0 | 0 / 0 |
| Result | PASS | E-RES: disk < 12 GiB |

The thresholds are 12,884,901,888 free disk bytes and 4,294,967,296 memory-headroom bytes.
The retry was 82,247,680 disk bytes below threshold. `file`, `active_file`, `inactive_file`,
`file_mapped`, and the `memory.events` reclaim counters were not treated as shortages.
There was no observed Lean exit 137, SIGBUS, or SIGSEGV.

A fresh official Lean 4.25.0 toolchain was extracted with `--no-same-owner` into this workspace.
The pinned unmodified executable returned `error: failed to locate application`. Only then was
Part 2's exact fallback source compiled and preloaded for Lean/Lake execution. Its SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7` and the source is included as
`evidence/runtime/executable-path.c`. The compiled `.so` is excluded. No toolchain patch,
filesystem-permission change, or sandbox escalation was used. With the fallback, Lean reported
4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.

Exact process-scoped environment settings:

```text
LEAN_SYSROOT=/workspace/scratch/1d8cbe0b04e8/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/1d8cbe0b04e8/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/1d8cbe0b04e8/runtime/executable-path.so
PATH=/workspace/scratch/1d8cbe0b04e8/runtime/bin:<inherited PATH>
TMPDIR=/workspace/scratch/1d8cbe0b04e8/tmp
TAR_OPTIONS=--no-same-owner
```

The wrapper executables set the first three variables only when launching Lean or Lake. The
shim was not preloaded into unrelated audit or packaging commands. The only cache invocation
was `lake exe cache get` with the above `TAR_OPTIONS`, in the one clone. Logs went directly to
`evidence/logs/cache-get.log`. It fetched fresh package checkouts; their URLs and revisions
matched the manifest (`package-pins.log`). Four optional documentation packages were not
instantiated by this non-development Lake configuration: `«doc-gen4»`, `UnicodeBasic`,
`BibtexQuery`, and `MD4Lean`. No package mismatch was found.

The cache command exited **1**, ending with `1952 download(s) failed` after CONNECT 403 errors.
Therefore item 3's successful-cache condition failed. The prescribed cleanup deleted only
`.lake/packages` and `.lake/lakefile.olean*`; the next preflight failed disk headroom as above.
**No second cache invocation was made.** No archives or oleans were unpacked/restored by hand,
no package trees were copied/moved/deduplicated, and no other session's builds, object store,
or toolchain were reused. The cache tool used its normal `/root/.cache/mathlib` location.
No checks against missing prerequisites were attempted. The standalone Mathlib probe and
zero-sized-olean check were not reached.

## Ownership and phase reached

The first source edit was byte-for-byte the supplied overlay, SHA-256
`e0d312eeb2048ba3dd4f33d7d6f8415b5a0cbcceb82c234b65707dc58c027135`.
Exactly these three imports were added after the original imports:

```lean
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
```

The four supplied draft declarations are preserved byte-for-byte; **none was restated**.
The frozen module prefix, bridge, replay canonizer statement and `sorry`, target statement,
and pre-existing target docstring are unchanged. The only public-facing text addition is the
authorized `**Implementation status.**` paragraph. All new declarations are private, begin
with `ic_`, and occupy the one authorized region. No new public declaration, leaked `section`,
`open`, or `variable` was introduced. Only the owned file differs in the tracked tree.

| Numbered phase | Draft work reached | Still missing |
|---|---|---|
| 1. Startup | Captured-header contract; installation draft retained; seam-layout and represented-bank contracts | Global banks, two-pass composition, native rewind, counter duplication, installation routing and whole startup proof |
| 2. Window | Exact bounded-window endpoint and frame contract | Counter-preservation construction, physical window rewind, attachment to startup |
| 3. Loop/verdict | Original-branch loop contract, verdict leaf, shared phase-host instance and first-verdict tail | Attachment to the actual startup endpoint; all elaboration/verification |
| 4. Semantics/ledger | Replay/locality reused; both conditional arithmetic inequalities | Complete startup costs, one global finite machine, target witness and final proof |

These are preparatory drafts across phases 1–4, **not four completed phases**. There is no
kernel-verified phase advance in this session. The four input drafts were described as verified
in the supplied brief; that is prior evidence, not a successful local check.

Every declaration added relative to the pin is listed below. All twenty remain locally
unverified, including the four retained input drafts.

| Private declaration | Role |
|---|---|
| `ic_header_result` | Supplied header projection: selected word, suffix head, bounded halt |
| `ic_capture_return` | Supplied bounded halt transported to first live returning capture |
| `ic_replay_window` | Supplied replay and input-locality state/output correspondence |
| `ic_table_call` | Supplied installation of the whole replay serialization |
| `ic_header_capture` | Combine header and capture, with exact captured word and frame |
| `ic_layout_call` | Uniform layout endpoint/time, empty-output summary, all framed fields |
| `ic_replay_rep` | Assemble represented replay start from initial mirrored bank/table/summary |
| `ic_input_suffix` | Dropping the doubled paired header leaves the suffix |
| `ic_window_call` | Exact bounded window, head positions, frame, and short-input bound |
| `ic_loop_replay` | Hosted-loop endpoint and early bound for the original branch |
| `ic_verdictTM` | Consumer-specific one-step read into two live verdict states |
| `ic_verdictTM_run` | Correct first verdict after that one step |
| `ic_loopPh` | Two-phase state family for existing loop and verdict leaf |
| `ic_loopPh_fintype` | Finiteness of the two control types |
| `ic_loopPiece` | Select existing hosted loop or local verdict leaf |
| `ic_loopRedirect` | Redirect both loop exits, for either boundary tag |
| `ic_loopHost` | Instantiate the existing public phase host |
| `ic_loopHost_run` | Two-step dispatch/read extension and first-verdict guarantee |
| `ic_replay_tail` | Represented start to original-branch verdict, with total and prefix bounds |
| `ic_time_ledger` | Both arithmetic inequalities for a common conditional constant |

There is no second implementation of a host, seam, embedding, counter loop, parser, or layout
machine. The new one-step verdict leaf is consumer-specific; it uses the existing host.

## Layout, representation, and both ledgers

`ic_layout_call` is parameterized by three distinct tapes `src`, `tbl`, `sm`; it does not choose
a global `K` or allocate the startup banks. It starts with the installed `serializeK M` on `src`
at head zero, and blank `tbl`/`sm` at head zero. `serializeK_eq` and `unaryFin_eq` put this in the
shared layout contract's shape. The draft endpoint clears `src`, places `tableBitsK M.tr` on
`tbl`, and places `summaryCells none (unaryFin M.q₀)` on `sm`, framing other tapes and all
unselected heads. The summary identity uses `summaryCells_eq` and `bufferTape_of_neg`.
The layout time is chosen before the starting configuration and depends only on the word.

The proposed seven-tape hosted replay portion is:

| Tape | Role |
|---:|---|
| 0 | Virtual-input window |
| 1–2 | Original machine's blank mirrored work bank |
| 3 | Last mirrored tape: choice stream |
| 4 | Transition table |
| 5 | Output/state summary |
| 6 | Preserved deadline counter |

Thus eventual layout `tbl` and `sm` correspond to tapes 4 and 5 of this portion. `src` must be a
separate disposable installation tape, and the captured-header banks must be allocated outside
the persistent portion or connected by the published embeddings. **Those choices and their
composition are not constructed.** The source therefore exposes generic tapes, not a false
claim of a complete concrete allocation.

`ic_replay_rep` assembles the public `Rep_iff` fields: native input at one, the blank initial
work bank followed by the whole stream, table contents, empty-output initial-state summary,
and table/summary heads at zero. It uses the published `withChoiceTape` and initial-configuration
fields and `outputSummary_nil`; it does not inspect the arbitrary coded transition function.
The composition of these representation fields with the actual window/startup end is open.

Write `d = |bits t|`, `L = |tableBitsK replay.tr|`, and let `a`, `b`, `w` be nonnegative
per-code coefficients. The draft common constant is

```text
C = a + b + w + 50*(L + 1) + 10.
```

Here `a` must bound fixed startup, installation, layout, and final dispatch/read costs; in
particular it includes the tail's two additional steps. `b` is the remaining binary-width
coefficient; `w` includes window-copy and rewind work. `L` is fixed by the decoded code.
The intended startup estimate uses the prescribed two prefix passes and native rewind
(`36*d + 18*|α| + 59`) plus per-code installation/layout costs. No complete startup estimate
or proof that these coefficients bound the assembled machine is supplied.

The exact conditional inequalities in `ic_time_ledger` are:

```text
a + (b+4)*d + w*(min(t, |x|)+1) + (50*(L+1)+4)*t + 2 <= C*(t+1)
a + (b+4)*d + w*(min(t, |x|)+1) + (50*(L+1)+4)*r
  <= C*(r + |x| + d + 1).
```

The first uses `length_bits_le_self` and `min(t, |x|) <= t`; the second uses
`min(t, |x|) <= |x|`. The represented tail separately states total cost
`t*50*(L+1) + 4*t + 2*d + 4`, and, when the branch has halted by `r <= t`, cost
`r*50*(L+1) + 4*r + 2*d + 2`. Absorbing its two added dispatch/read steps into `a` aligns these
with the conditional ledger. The target has not been derived from these expressions.

The draft contracts retain `t = 0`, shorter inputs, longer streams, and arbitrary decoded
machines. No whole-machine edge-case theorem or test is claimed: the actual initial configuration
has not yet been connected to the represented start.

## Open declarations, axiom walk, promotions, and escalation

Open owned target: **`Turing.exists_ndInterpreterCore`** (unchanged `sorry`).
**Proof sketch:** choose disjoint startup banks and persistent tapes; compose the two returning
header captures with native rewind; duplicate/rewind the counter before the destructive window
copy; install the full replay serialization and apply the shared seam layout; copy and rewind
the bounded input window; assemble the represented hosted start and retain the untouched loop
counter and stream; compose it with `ic_loopHost`, transport every first-verdict cut, select
both live verdicts, and apply the two time ledgers with actual per-code startup constants.
Every draft proof must first pass elaboration, the extended probe, and the seal test.

Frozen out-of-scope open declaration: **`Turing.exists_replayCanonizer`**.
**Proof sketch:** as in its unchanged source docstring, apply the effective scheme's canonizer
and primitive-recursively transform its two choice-slice tables into the deterministic replay
serialization; the branch-choice tape is last. Its proof remains for the separate wave.
The window and seam-layout contracts are also untouched external stubs.

**Target axiom walk, source level only:** `exists_ndInterpreterCore -> its own sorry`.
Thus this delivery is **not proved modulo exactly the three permitted stubs**. No axiom print
ran. The intended direct stub dependencies of helpers are `ic_table_call ->
exists_replayCanonizer`, `ic_layout_call -> exists_seamLayoutTM`, and `ic_window_call ->
exists_inputWindowCopyTM`. Other helper bodies visibly use proved public contracts and local
helpers, but neither their transitive axioms nor successful elaboration are certified here.
The frozen bridge's existing proof was not changed. No new `sorry` or axiom was added.

Promotion candidates (notes only):
- `ic_header_result`: the common header split used by both projections, relevant to UN setup
  and B5a's H1.
- `ic_capture_return`: first-halt returning capture of a bounded native-input run, replacing
  repeated inline capture arguments in future shared infrastructure.

**Escalation E-RES:** the cleaned-retry filesystem has 12,802,654,208 bytes free, strictly less
than 12,884,901,888. Memory headroom is 8,101,928,960 bytes with `oom = oom_kill = 0`; it does
not trigger the stop. The earlier CONNECT 403 cache failure prevented prerequisite validation.
Continue on a host satisfying the resource preflight. No mathematical impossibility or missing
public API lemma is asserted. The open assembly work is an implementation gap, not a claim
that the frozen theorem is false. Only dependent cache/Lean tasks stopped; independent audits
and delivery continued.

## Rule 10 and Rule 11 audit

`evidence/logs/external-citations-static.txt` lists the explicit external contracts, definitions,
projections, and standard-library references for all twenty private declarations. It normalizes
method notation; it is a source-level inventory, not an elaborated dependency list.
Same-file `exists_replayCanonizer` and `ic_*` calls are excluded from that external list.
The final report reproduces the inventory below.

The unchanged 96-check base probe was preserved and extended by 54 names (including the newly
used public equations and explicit standard-library proof references). Its extension is recorded
in `import-probe.log`. **It was prepared but not executed.** A candidate seal source with
36 foreign TCSlib definitions marked locally irreducible was prepared. **The seal test was not
executed**; no claim of a passing complete irreducibility check is made. A continuation must
check the inventory for completeness and run both through `scripts/lean_check_tree.sh`.

All `rw`, `simp`, `simpa`, `dsimp`, `unfold`, `exact`, `rfl`, `show`, `change`, `decide`, and
arithmetic sites in the added region were inspected in their full source context; the line
inventory is in `tactic-inspection.txt`. Explicit named reductions are local definitions/lets
or the owned verdict/control definitions. Configuration fields, serialization, counter values,
replay and run algebra use published equations/contracts. No added explicit expansion of a
foreign TCSlib definition was found. Record-field construction and local control reduction
account for the `rfl` sites. This static inspection cannot certify hidden definitional closure;
that remains blocked pending the seal test and kernel elaboration.

The diff grep found no occurrence of any of the six prohibited canonical rows:
`transferTM_run`, `copyTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
`incrementTM_run_overflow`. It scanned 745 other tracked TCSlib files and 5,049 distinct private
names. Four textual collisions were classified: `S` and `T` are local binders; `.trans` is
on local order/equality proofs, not `TreeIsSubtree.trans`; `Cfg.mapState_state` is the public
configuration lemma, not the private seam lemma with the same short name. No foreign private
citation was found. Full grep/classification is in `rule11-grep.log`.

## Verification status and final sweep tail

| Required activity | Result |
|---|---|
| Fresh dependency cache | FAILED, exit 1, 1,952 CONNECT 403 download failures |
| Cleaned retry | Stopped before cache command: preflight E-RES |
| Zero-sized-olean check and Mathlib probe | SKIPPED; successful cache unavailable |
| 81-module bootstrap | SKIPPED; zero module checks started |
| Optional upstream-first subset | Planned 37 modules in supplied order, none checked; remaining 44 also unbuilt |
| Owned-module check | SKIPPED |
| 81-module final sweep | SKIPPED |
| Original/extended import probe | PREPARED, NOT EXECUTED |
| Seal test | PREPARED, NOT EXECUTED |
| Target and every-private axiom prints | SKIPPED |
| Before/after duplication screens | Completed sequentially under `nice -n 10`; no new pairs |
| Freeze/scope inspection | Completed; only authorized regions changed |
| Style lint | `style_lint: 0 FAIL, 63 WARN over 80 files` |
| New lines over 100 characters | 0 |

No Lean check was run against missing prerequisites, no short timeout was applied, and no
failed check was reclassified as a mathematical finding. The baseline's 35 sorry entries in
15 modules were recorded by name before proof work and are reproduced below. There is **no
measured final warning difference**: neither bootstrap nor final sweep ran. At source level
both owned sorries remain and no new one was introduced.

Final sweep log (the entire log is a skip record, not a successful sweep):

```text
SKIPPED: missing verified dependency cache and bootstrap products. Planned sweep: 81 modules.
No proof-check failure or sorry-count difference is inferred from this skip.
```

Axiom log:

```text
SKIPPED: no fresh owned-module olean is available. No axiom print was executed.
Source-level target walk: exists_ndInterpreterCore -> its unchanged sorry.
This is not a proof modulo the three cited stubs.
```

The full modified source is **758 lines**, **3 public declarations** (unchanged), and
**20 private declarations** (four supplied plus sixteen new). Source SHA-256:
`e862c398afffbe00a7e5846ba21394456da2588fc054cb4775720fa6f121690f`.
The tracked working tree matched committed HEAD when checked. Unrelated untracked campaign
files and scratch `FillChecks` sources are not committed or included in the patch/bundle.

## Duplication result

**new copies: none**. The before screen, taken immediately after the overlay edit, is
byte-identical to the supplied screen base: 407 declarations, 115 pairs, 43,357 reproduced
characters. The final after screen reports 422 screened declarations, the same 115 pairs and
43,357 characters. The pair sets are identical. There are no new cross-file pairs and no new
in-file pairs to justify. Both full outputs are quoted below and included as separate logs.
The extra intermediate draft screen is historical; only `screen-after.txt` is the final result.

## REPORT.md checklist

- [x] The preflight's numbers, using **addendum v2.1 Part 1**, recorded above with exact memory
      computation; genuine disk E-RES recorded separately from healthy memory headroom.
- [x] The phase reached, base hash, ancestor check, and checkpoint zips recorded. **Target not
      proved; not certified modulo the three stubs.** Source-level target axiom walk disclosed.
- [x] Three imports and four drafts as the byte-for-byte first overlay edit; no restated draft;
      changes outside imports restricted to the authorized private region and status paragraph.
- [x] Every new declaration listed with its role; partial status paragraph present.
- [x] Generic layout tapes, proposed hosted allocation, representation fields, and missing global
      allocation/composition disclosed.
- [x] Conditional per-code constant and both ledgers stated; missing startup bound disclosed.
- [x] Promotion candidates and E-RES escalation stated; no mathematical/API escalation asserted.
- [ ] Rule 10's **executed** probe re-run and seal test: blocked by E-RES. Static external-citation
      inventory and tactic inspection completed; Rule 11 diff/private-name grep completed.
- [x] Both v3 screens completed and quoted; no new pairs; **new copies: none**.
- [ ] Successful final sweep and axiom prints: blocked by E-RES. File size/counts, explicit skip
      logs, base sorry inventory, and successful lint line are provided.

Unchecked boxes are unresolved verification gates, not omitted reporting. This package is a
continuation checkpoint suitable for review of drafts and environment evidence only.

## Baseline sorry inventory (recorded, not remeasured)

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/Build/SeamLayout: 1: exists_seamLayoutTM
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

## Static external-citation inventory

```text
STATIC SOURCE CITATION INVENTORY
Scope: all 20 private declarations added relative to the pin, including the four supplied drafts.
No elaborated dependency inventory or axiom certification is claimed. Method notation is normalized.
Turing.exists_replayCanonizer and all ic_* names are same-file references and are excluded below.
Inherited bridge/target text is frozen and not part of the new-proof inventory.

Header and capture contracts:
Turing.Cfg.init_state
Turing.FinTM.pairExtractTM_fst
Turing.FinTM.pairExtractTM_snd
Turing.MultiTapeTM.exists_first_halt
Turing.MultiTapeTM.initCfg_eq
Turing.embedSilentCfg_cap
Turing.embedSilentCfg_inputPos
Turing.embedSilentCfg_output
Turing.embedSilentCfg_unselected
Turing.embedSilentRetTM_run
Turing.length_pairEncode
Turing.pairDecode_pairEncode
Turing.prefixCanon_complete

Install, layout, window, representation:
Turing.Cfg.init_inputPos
Turing.Cfg.init_output
Turing.Cfg.init_workTapePos
Turing.Cfg.init_workTapes
Turing.FinTM.bufferTape_eq
Turing.FinTM.bufferTape_of_neg
Turing.FinTM.exists_installCallTM
Turing.NDTM.initCfg_eq
Turing.NDTM.withChoiceTape_inputPos
Turing.NDTM.withChoiceTape_output
Turing.NDTM.withChoiceTape_state
Turing.NDTM.withChoiceTape_workTapePos
Turing.NDTM.withChoiceTape_workTapes
Turing.StepBlock.Rep_iff
Turing.StepBlock.outputSummary_nil
Turing.StepBlock.summaryCells_eq
Turing.counterValue_bits
Turing.counterValue_eq
Turing.exists_inputWindowCopyTM
Turing.exists_seamLayoutTM
Turing.pairEncode_eq
Turing.serializeK_eq
Turing.unaryFin_eq

Replay, loop, verdict, and arithmetic contracts:
Turing.Action.apply_state
Turing.Cfg.ext
Turing.Cfg.mapState_inputPos
Turing.Cfg.mapState_output
Turing.Cfg.mapState_state
Turing.Cfg.mapState_workTapePos
Turing.Cfg.mapState_workTapes
Turing.Cfg.workTapeSymbols_eq
Turing.FinTM.VirtualTag_iff
Turing.MultiTapeTM.runFrom_add
Turing.MultiTapeTM.runFrom_succ_eq_step'
Turing.MultiTapeTM.runFrom_zero
Turing.MultiTapeTM.step_of_some
Turing.NDTM.replayTM_runFrom
Turing.NDTM.runWith_initCfg_take
Turing.StepBlock.hostedLoopTM_run
Turing.StepBlock.hostedLoop_read
Turing.StepBlock.outputSummary_true
Turing.counter_cfg_eq
Turing.length_bits_le_self
Turing.phaseHostTM_run
Turing.vhostCfg_state

TCSlib types, constructors, projections, and opaque definitions appearing in the private region:
Turing.Cfg
Turing.Cfg.inputPos
Turing.Cfg.mapState
Turing.Cfg.ofWords
Turing.Cfg.output
Turing.Cfg.state
Turing.Cfg.workTapePos
Turing.Cfg.workTapeSymbols
Turing.Cfg.workTapes
Turing.CounterLoopState
Turing.CounterLoopState.body
Turing.CounterLoopState.dec
Turing.CounterLoopState.done
Turing.CounterLoopState.escape
Turing.EffectiveNDMachineCode
Turing.EffectiveNDMachineCode.decode
Turing.FinTM
Turing.FinTM.State
Turing.FinTM.VirtualTag
Turing.FinTM.bufferTape
Turing.FinTM.k
Turing.FinTM.pairExtractTM
Turing.FinTM.tm
Turing.MultiTapeTM
Turing.MultiTapeTM.initCfg
Turing.MultiTapeTM.q₀
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.tr
Turing.NDTM
Turing.NDTM.initCfg
Turing.NDTM.q₀
Turing.NDTM.replayTM
Turing.NDTM.runWith
Turing.NDTM.withChoiceTape
Turing.StepBlock.Ph
Turing.StepBlock.Rep
Turing.StepBlock.exit
Turing.StepBlock.hostedLoopTM
Turing.StepBlock.outputSummary
Turing.StepBlock.summaryCells
Turing.StepBlock.summaryTape
Turing.StepBlock.tableTape
Turing.counterLoopCfg
Turing.embedSilentCfg
Turing.embedSilentRetTM
Turing.pairEncode
Turing.phaseHostTM
Turing.prefixCanonTM
Turing.serializeK
Turing.stateWord
Turing.tableBitsK
Turing.unaryFin
Turing.vhostBank
Turing.vhostCfg

Explicit standard-library and Mathlib proof references:
Bool.false_and
Bool.false_eq_true
Bool.noConfusion
Bool.not_false
Bool.not_true
Bool.true_and
False.elim
Fin.ext
Function.comp_def
Function.update_of_ne
Function.update_self
List.append_nil
List.drop_left
List.getElem?_eq_none
List.length_nil
List.length_take
List.nil_append
Nat.add_zero
Nat.zero_le
Option.getD_some
Option.isNone_iff_eq_none
Option.map_map
Option.map_some
Option.noConfusion
Option.not_isSome
Option.some.inj
Option.some_ne_none
Sigma.fst
Sigma.mk.inj
Sum.noConfusion
congrArg
decide_false
false_and
if_neg
if_pos
le_rfl
min_le_left
min_le_right
sub_zero
true_and
zero_add

Standard datatypes/functions written in the new region (not a transitive dependency inventory):
Bool
Bool.toNat
DecidableEq
Fin
Fin.castAdd
Fin.castSucc
Fin.lastCases
Fintype
Function.update
Int
List
List.drop
List.length
List.map
List.replicate
List.take
Nat
Nat.bits
Nat.ofDigits
Option
Option.getD
Option.isNone
Option.isSome
Option.map
Option.none
Option.some
Set.range
Sigma.mk
Sum.inl
Sum.inr
Type
decide
min
```

## Complete before-screen output

```text
declarations screened: 407; copy pairs (target reproduces >= half of source): 115; reproduced text: 43,357 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/232 = 84%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/244 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/912 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonEmbedWords  reproduces  Embed.lean::embedEmitCfg_ofWords_eq: 88/137 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Embed.lean::embedEmitCfg_ofWords_eq  reproduces  CodeSimulator.lean::canonEmbedWords: 88/148 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/161 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 460/912 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
```

## Complete final after-screen output

```text
declarations screened: 422; copy pairs (target reproduces >= half of source): 115; reproduced text: 43,357 chars
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/232 = 84%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/244 = 80%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/912 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   CodeSimulator.lean::exists_canonOffsetTM  reproduces  CodeSimulator.lean::exists_canonCountTM: 270/397 = 68%
   CodeSimulator.lean::exists_canonReadySeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   CodeSimulator.lean::exists_canonHeaderCountSeam  reproduces  CodeSimulator.lean::canonBlankLift: 78/115 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   CodeSimulator.lean::canonEmbedWords  reproduces  Embed.lean::embedEmitCfg_ofWords_eq: 88/137 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Embed.lean::embedEmitCfg_ofWords_eq  reproduces  CodeSimulator.lean::canonEmbedWords: 88/148 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   CodeSimulator.lean::canonStrictInstall  reproduces  CodeSimulator.lean::exists_canonHeaderSeam: 382/648 = 59%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/161 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   CodeSimulator.lean::exists_canonHeaderSeam  reproduces  CodeSimulator.lean::canonStrictInstall: 382/671 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   CodeSimulator.lean::scan_grammar_guard  reproduces  CodeSimulator.lean::canonScan_all: 152/278 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 460/912 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
```
