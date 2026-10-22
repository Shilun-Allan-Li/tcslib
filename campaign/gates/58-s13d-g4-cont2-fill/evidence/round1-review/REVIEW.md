# Gate 58 review: the findings on PR #143 (§13d G4 continuation 2, partial landing)

**Result.** All 20 notes are **true**. Two of them contain a precision point that corrects a pack
statement: finding 15 (probe counts) and finding 17 (which top pair shares the adapter).
- **The gate closes:** PASS, 0 blockers and 0 majors.
- **No `.lean` change to #143.** No note finds an error in the landed text, and continuation 3
  applied #143's two commits by `git am`.
- **Records:** two pack errata, the resolutions, and one backlog line.
- **Nothing needs the user's decision.**

**#143 is not yet clear to merge.** Gate 58 closes and lg4c2 passed at `c60ed898`. But #137 merged
(`2ff214c5`, 2026-10-22 00:21) after lg4c2 was recorded (`1d4fcf3e`, 00:19). The merged tree differs
from lg4c2's in `Build/InputWindow` and the facade. Replay those two modules on the merged tree
from a copy of `oleans-lg4c2`. #143 is clear to merge once that passes.

Paths: `$S = $S`.
Evidence is under `$S/review/gate58/out/` (index `out/INDEX.txt`). Probes are in `probes/` and
scripts in `scripts/`. The records drafts are in `records/` (`resolutions.md`, `resolutions.diff`,
`backlog.diff`, and `tree/` with the patched copies).

## Method

- **The findings** were read as data, with `python3 -I`.
- **Every claim was checked against the repository:**
  - `git` at `96d60278`, `4b76f0ff`, `c60ed898`, the tip `25d0ffa7` and the merged tree;
  - the bundle in `exchange/outbox/gates/58-s13d-g4-cont2-fill-gate/`;
  - the cont2 review's `out/` and `probes/`, and the gate's `evidence/`.
- **Lean ran only through `tools/leanelab.sh`, one run at a time:**
  - in my detached worktree `$S/review/gate58/wt` at `c60ed898` (with the `.lake/packages` link),
    against `oleans-lg4c2`;
  - four runs: the module, the seal, the axiom walk, and the 439-check probe as a standalone import.
- **Not run:** no build or cache command, and no copy-text screen. The landed tree's screen is
  continuation 3's screen base, which I compared byte for byte instead.
- **Nothing outside `$S/review/gate58/` was written.**

## Findings

The "Cont3" column gives the class: **(a)** handle at continuation 3's review; **(b)** carry to a
continuation-4 draft; **(c)** nothing.

| # | Verdict | Evidence (`out/`) | Proposed resolution | Cont3 |
|---|---|---|---|---|
| 1 | True | `01-identity.txt`, `16-elab-landed-lg4c2.out` | Done in part. Bundle `869b4564…` OK, 65 sections; the bundle's owned file is byte-equal to blob `e8353f20…`. Re-ran at `c60ed898` against `oleans-lg4c2`: the module (exit 0, warnings at 1195 and 1237 only), plus the seal, axioms and probe (rows 14, 15). The sweep, archive and environment checks rest on the review's records. | (c) |
| 2 | True | `01-identity.txt`, `02-freeze.txt` | None. Blobs: `e88edbda` → `77c9119d` → `e8353f20`. Lines 861 → 1,365 → 1,370; 18 → 18 public; 31 → 65 private. The code is identical with comments stripped. The maintainer commit has four hunks, all in owned regions. | (c) |
| 3 | True | source, lines 68–126 and 273–345 | None. | (c) |
| 4 | True | source, lines 637–646 and 1085–1087 | None. | (c) |
| 5 | True | source, lines 648–858 and 1089–1112 | None. Its remark (the delimiters come from `zoneRowPre`'s blank scratch, not from the copy) bears on the left pass: see carry-forward 4. | (c) |
| 6 | True | source, lines 860–1015 | None. The direction-parametrized walk is already binding in continuation 3 (item 3). | (b) if not reached |
| 7 | True | source, lines 1017–1083 | None. | (c) |
| 8 | True | `08-route.txt`; the two statements are identical to cont3's `G4C3Targets.lean.txt` | None. The open items are exactly continuation 3's 1.1b: endpoint, envelopes, the bridge and the second seek's agreement, and the re-wrap. Check each at continuation 3's review. | (a) check; (b) what stays open |
| 9 | True | `09-10-19-arithmetic.txt` | None. Level one: time 48, bound 96. | (c) |
| 10 | True | `09-10-19-arithmetic.txt`, cont2 `out/levelone.out` | None. | (b) if not reached |
| 11 | True | `08-route.txt` (the level-one hand instance of the 1.1b endpoint) | At continuation 3's review, instantiate the proved endpoint at `D.1 = 0`. Expected: cells 5 and 6 hold `inr (some none)`, cells 7 and 8 hold `inr none`, the tape-0 head is at 7, the scratch head stays at `q`, and the time is 48. | (a) |
| 12 | True (as plausibility) | — | Keep the admission. | (b) if not reached |
| 13 | True (as plausibility) | — | Keep the admission. | (c) |
| 14 | True | `14-seal-landed-lg4c2.out`, `14-rwargs-vs-seal.txt` | None for #143. The seal re-run at the landed head: the two controls fail inside and pass outside, nothing else fails. No home argument names a sealed definition, and the six `change` steps are inherited and sealed. Reviewer addition, outside the gate: see "Further observations". | (c) |
| 15 | True; adds precision | `15-probe-distinct.txt`, `15-axioms-probe.txt`, `15-importprobe-landed-lg4c2.out`, `cont3-brief-claims.txt` | **Pack erratum** (`pack.md:78`): 439 checks of **428 distinct names**. Expansions A (39) and B (62) share 11 names, so there are 90 names beyond the 338. Landed re-runs: axioms equal name by name; the probe as a standalone import gives 439 outputs, 0 errors and 0 warnings. | (a) and (b) |
| 16 | True | cont2 `out/elab-*.out`, `out/sweep-check.txt`; `16-elab-landed-lg4c2.out` | None. | (c) |
| 17 | True; adds precision | `17-screen-pairs.txt` | **Pack erratum** (`pack.md:61`): only the 81% pair shares the adapter. The 80% pair is two `copyMapTM_contract` instances; the review's "respectively" was right. The landed tree's screen equals the worker head's. Factoring is already continuation 3's work. | (a) and (b) |
| 18 | True | `18-public-text.txt` | None. **Records:** gate 44's minor 3 (its appendix line) is discharged by this landing. | (c) |
| 19 | True | `09-10-19-arithmetic.txt`, cont2 `out/environment-v23.txt` | None. The pre-cache figure is the arithmetic line's sample. The raw sample beside it gives 8,158,609,408 B, also above 4 GiB. Addendum v2.4 already notes that the cache tool compiles itself. | (c) |
| 20 | True | `20-replay-precheck.txt`, `20-merge-status.txt` | None to the replay: the nine pins equal the repository diff, the sorry counts sum to 10, and the facade is last. **But a merge-time replay is owed** (see the alert at the top). | (c) |

### Details

- **Finding 15:**
  - The 11 shared names: `Cfg`, `Cfg.ext`, `Contract.exit_mem`, `FinTM.bufferTape`,
    `FinTM.bufferTape_nat`, `SeekPhase`, `SeekPhase.done`, `SeekPhase.run`, `SweepPhase`,
    `SweepPhase.sweep`, `seamCompTM`.
  - `G4C3ImportProbe.lean.txt` (continuation 3's input) is byte-equal to the cont2 review's
    `G4C2ImportProbeOnHead.lean.txt`. It embeds the **cont2 worker's** 1,365-line module (blob
    `77c9119d`), not the landed 1,370-line file. The code is the same, so the import context is
    the same and the 439 results stand.
  - But its own run shows the two targets' sorry warnings at 1191 and 1232, as the pre-ship log
    records. The brief says "0 errors, 0 warnings" and gives the targets at 1195 and 1237.
- **Finding 17:**
  - The adapter's four instances are `zr_rightSeekBackContract`, `zr_rightRulerContract`,
    `zr_adjustedWalkContract` and `zr_adjustedBackContract` (lines 692, 784, 908, 975).
  - The 80% pair is `zr_halfCopyContract` against `zr_rulerCopyContract` (66 of 82 characters): two
    three-line `copyMapTM_contract` instances that differ in direction and merge.
- **Finding 8:** the endpoint statement holds by hand. Inner `[N, N+m)` holds `some none`, outer
  `[N+m, N+2m)` holds `none`, the tape-0 head is at `N+m`, the scratch ruler is `[q, q+m)`, and the
  scratch head is back at `q`. This follows from `zr_rightRuler_post`, `zr_constantCopy_cell`,
  `zr_adjustedBack_post` and the copies returning their heads. The pass's own exit set is the
  nested image, so the 1.1b re-wrap stands.

## For the maintainer at continuation 3's review (class (a))

Continuation 3's brief is dispatched and unchanged. These points make some of its claims inexact.
None changes its route.

1. **Finding 17:** the brief's "The composite adapter above keeps its two top pairs from drifting
   toward 90%" (lines 478–479) holds for the 81% pair only.
   - Check that the adapter helper **re-points the four existing instances**. An instance left in
     place reproduces most of the helper's text and may pair with it at 90% or more.
   - Check the copy-instance pair separately. New constant copies (left pass, cleanup) should reuse
     `zr_halfCopyContract`/`zr_rulerCopyContract`, or one parametrized constant-copy definition (as
     `zr_constantCopy_cell` already is), rather than add a third instance.
2. **Finding 15:** the brief says "439 names" (line 383), "the 101 its worker cited beyond them"
   (lines 140–141) and "0 errors, 0 warnings" (line 141).
   - Read the worker's probe re-run as **439 checks of 428 names**.
   - Expect the two sorry warnings at 1191 and 1232 if the worker ran the file as shipped.
   - Re-run the 439 checks yourself as a standalone `import` of the delivered module, as in
     `probes/G58ImportProbe.lean.txt`. Its olean comes from the delivery's replay snapshot, or
     append the checks to the delivered file.
3. **Findings 8 and 11:** check each 1.1b item:
   - the endpoint and the tape-0 envelope (the two `G4C3Targets` statements, or their corrected
     forms with reasons);
   - the scratch envelope `q − 1 … q + m + 1`;
   - the bridge to `zonedTape_extend` (cells `≥ 0`) and to `zonedTape z` (cells `≤ 0`);
   - the singleton-exit re-wrap.

   Then instantiate the proved endpoint at level one (finding 11's values).
4. **Reviewer addition: region (a)'s end line.** The brief gives the home as lines 127–1147 (line
   159). The landed home ends at 1148 (the `omega` of `zr_rightPass_time_le`), and 1149 is the blank
   line before 1150. Run the region check as 127–1149.
5. **Reviewer addition: the snapshot.** The brief says `oleans-lg4c2` is "exactly that tree"
   (line 86). Continuation 3's base contains #137, which lg4c2 lacks.
   - The pre-ship results for `Build/ZoneRebalance` hold, because its upstream closure is the same.
   - Continuation 3's landing replay must chain from #143's merged-tree re-replay (the alert at the
     top), not from lg4c2 directly.
6. **Finding 14:** the frozen frames lemma's unfoldings (see "Further observations") are outside
   region (a) and frozen for the worker. Do not count them against continuation 3. Its seal covers
   the home only.

## Carry-forwards for a continuation-4 draft (class (b); records only, conditional on continuation 3)

1. **The probe:**
   - deduplicate it (428 names plus continuation 3's additions);
   - state it as "N checks of M distinct names";
   - build it as a standalone import of the landed module (its olean is in the landing's replay
     snapshot), not by embedding a module text, so its line numbers and warnings do not drift;
   - state the expected warnings (none).
2. **Duplication text:**
   - name each top pair's shared text exactly (adapter or copy instance);
   - list the adapter helper's re-pointed instances;
   - route every constant copy through one definition.
3. **Whatever of 1.1b stays open, as stated:**
   - the endpoint, and the tape-0 and scratch envelopes;
   - the bridge to `zonedTape_extend`;
   - the second seek's agreement on `[−zoneStart ℓ, 0]`, through the right pass's frame;
   - the singleton-exit re-wrap;
   - the level-one sanity instance.
4. **The left pass, if open:**
   - the direction-parametrized adjusted walk and scratch rewind (finding 6);
   - the ruler's repositioning, the leftward composition and the restoration (finding 10);
   - the left ruler's delimiters, read from the right pass's scratch frame (blank outside
     `[q, q + m)`), not from `zoneRowPre`'s global blankness (finding 5's remark).
5. **The rest of phase 1, then phase 2, as continuation 3's brief states them** (findings 12 and
   13):
   - the `ℓ = 0` branch by the leaf (cells `±2`, `±3`);
   - cleanup and assembly;
   - then the rebalance row.
6. **Lines re-derived** from the file as landed (item 4 above). Rule 10's two checks stay binding.

## Records drafts (against `$S/wt-hk`: HEAD `25d0ffa7`, plus the working copy's uncommitted edits)

- **`campaign/gates/58-s13d-g4-cont2-fill/resolutions.md`** (new): `records/resolutions.md`, also as
  `records/resolutions.diff`. The text is reproduced below. It carries both pack errata, since the
  pack is preserved as dispatched, as in gate 44.
- **`campaign/backlog.md`**, the line "landed as #143 (gate 58)" (line 1286 at 05:35Z): `records/backlog.diff`. The diff is against `$S/wt-hk`'s working copy at 05:35Z, which already has the maintainer's uncommitted edits. It records gate 58 as closed and
  #143 as not yet clear to merge, with the reason. This is optional; the maintainer may prefer
  their own wording.
- **Evidence:** copy `out/` and `probes/` to `campaign/gates/58-s13d-g4-cont2-fill/evidence/round1-review/`,
  as gate 53 did. The resolutions cite the file names in `out/`.
- **No change** to `pack.md` (it stays as dispatched), to the cont2 `REVIEW.md` (its (e) sentence
  is correct), or to continuation 3's brief (dispatched).

## Further observations (not findings; no action for #143)

- **The frozen frames lemma.** `zoneRebalancePost_frames` (landed line 1302) unfolds `zonedTape`
  and passes `zoneCellAt` and `ZoneContents.words` to `simp`. All three are other files'
  definitions.
  - It is a frozen public lemma from the G2–G4 statements (`dc7d8a23`, 2026-10-15), from before the
    2026-10-16 no-unfolding ruling. #143 leaves it unchanged.
  - It is a re-pointing candidate for integration, like `zr_mirror_tape` was. It belongs in the
    backlog, not in this gate.
- **A stray symlink in the main repository.** `<repo>/.lake/packages/packages`
  points back to `.lake/packages`. It was created at 01:14, before my worktree (01:23); I did not
  create it and left it in place.
  - It is harmless to `leanelab.sh`'s `LEAN_PATH` loop, because `packages/packages/.lake` does not
    exist.
  - It is a recursive link that a tool walking `.lake/packages` could follow, so the maintainer may
    want to remove it.

## Ready-to-paste: `campaign/gates/58-s13d-g4-cont2-fill/resolutions.md`

The exact text is in `records/resolutions.md` (58 lines); it is reproduced here.

````markdown
# §13d G4 continuation 2, the partial's landing (PR #143, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #143 (`lean/g4-cont2-partial` at `c60ed898`, on the campaign branch
at `eb08fb16`): the worker's commit `4b76f0ff` (`6fe3bf88` cherry-picked; 34 private `zr_`
declarations composing `zr_rightPassContract`, and `zr_left_two_walks` restated) and the
maintainer's docstring commit `c60ed898`. Both targets stay admitted. Pack `pack.md`; bundle
SHA-256 `869b4564cdc6c5a0d0b789f4a6b0be3c00d70cffa63291f6a7556f1106c13515` (65 sections; folder
`58-s13d-g4-cont2-fill-gate/`). Replay passed (user, 2026-10-22): 13 of 13 at `c60ed898`,
static-equal (10).

**Round 1** (`findings.md`, verbatim; received 2026-10-22): **PASS, 0 blockers, 0 majors, 0 minors,
20 notes. The gate is closed; the landing is a partial.** No `.lean` change: no note finds an error
in the landed text, and continuation 3 applied #143's two commits by `git am`, so a new commit on
#143 would make its landing diverge from continuation 3's base. Two pack statements are corrected
(errata below; the pack is preserved as dispatched). The maintainer's review sub-agent verified
every finding: all true. At `c60ed898` against `oleans-lg4c2` it re-ran the module, the 56-name seal
with its controls, the axiom and admission walk, and the 439-check import probe as a standalone
import (`evidence/round1-review/`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 15 | note | The axiom and import inventories support the admission isolation and the import coverage; the probe's 439 entries are check commands, not 439 distinct names. | **True; records.** 439 checks of **428 distinct names**: Expansion A (39) and Expansion B (62) share 11 (`Cfg`, `Cfg.ext`, `Contract.exit_mem`, `FinTM.bufferTape`, `FinTM.bufferTape_nat`, `SeekPhase` with `done` and `run`, `SweepPhase` with `sweep`, `seamCompTM`), so 90 names beyond the brief's 338 (`15-probe-distinct.txt`). **Pack erratum:** `pack.md:78`, "439/439, the brief's 338 plus 101 names", reads **"439/439 checks of 428 distinct names: the brief's 338, plus Expansions A (39) and B (62), which share 11"**. Re-run at the landed head, as a standalone import of `Build/ZoneRebalance` against `oleans-lg4c2`: 439 outputs, 0 errors, 0 warnings, exit 0 (`15-importprobe-landed-lg4c2.out`). The axiom walk there gives the same axiom set as the review's, name by name; `sorryAx` reaches each target only through its own body; 65/65 external-dependency checks are empty (`15-axioms-probe.txt`). **At continuation 3's review:** its brief (dispatched) says "439 names", "the 101 its worker cited beyond them" and "0 errors, 0 warnings". Also, `G4C3ImportProbe.lean.txt` is byte-equal to the review's `G4C2ImportProbeOnHead.lean.txt`: it embeds the cont2 worker's 1,365-line module (code-identical to the landing), so its run shows the two targets' sorry warnings at 1191 and 1232 (as in the pre-ship log). The maintainer re-runs the 439 checks as a standalone import of the delivered module. **Carried** to the continuation-4 draft (below). |
| 17 | note | No new copied implementation needs a debt acknowledgment; the 81% pair shares the singleton-exit adapter, the 80% pair a mapped-copy invocation; factor the adapter at the start of continuation 3. | **True; records.** `zr_halfCopyContract`/`zr_rulerCopyContract` (66/82) are two three-line `copyMapTM_contract` instances. The adapter's four instances are `zr_rightSeekBackContract`, `zr_rightRulerContract`, `zr_adjustedWalkContract` and `zr_adjustedBackContract` (`17-screen-pairs.txt`). The review's (e) says this ("respectively"). **Pack erratum:** `pack.md:61`, "The top two share a four-line composite adapter", reads **"The top pair (81%) shares a four-line composite adapter …; the second (80%) shares a `copyMapTM_contract` instance"**. The landed tree's screen (continuation 3's screen base) is byte-equal to the worker head's, so the docstring commit moved no pair. The factoring is already continuation 3's (checkpoint 1.1b). **At continuation 3's review:** its brief's "keeps its two top pairs from drifting toward 90%" holds for the first pair only. Check that the helper re-points the four existing instances, since one left in place may pair with the helper at 90% or more. Check that new constant copies reuse `zr_halfCopyContract`/`zr_rulerCopyContract` (or one parametrized definition) rather than add a third instance. |
| 8, 11 | notes | Landing the composed pass as a partial is right. Before the dependent checkpoints: both characterizations, the scratch envelope and the second seek's interval agreement, and the exit set normalized. Boundary instances at level one: ruler −7, −6; inner cells 5, 6; outer 7, 8; heads 7 and −7; time 48. | **True; already continuation 3's checkpoint 1.1b** (its items 1.1b and 3, the second seek), so the dispatched route needs no change. The level-one values follow by hand from the 1.1b endpoint statement (`08-route.txt`). **At continuation 3's review:** instantiate the proved endpoint at `D.1 = 0` in a probe and check those values. Whatever of 1.1b stays open **carries** to the continuation-4 draft as stated. |
| 6, 10, 12 | notes | Parametrize the walk by direction for the left pass. The left ruler's repositioning, composition and restoration remain open. The extension specification is credible and unproved. | **True; already in continuation 3's route** (items 3–6; the direction-parametrized walk is binding there). **Carried** to the continuation-4 draft only for what continuation 3 does not reach. |
| 14 | note | The seal and the argument inspection support rules 10 and 11; preserve both checks. | **True; re-run at the landed head.** With the review's 56-name seal on `c60ed898`'s home, the two `rfl` controls fail inside and pass outside, and nothing else fails (`14-seal-landed-lg4c2.out`). No rewrite or `simp` argument in the home names a sealed definition (`14-rwargs-vs-seal.txt`). Both checks stay binding for continuation 3 (its ground rule 10). **A reviewer addition (outside the gate):** outside the home, the frozen public `zoneRebalancePost_frames` unfolds `zonedTape`, `zoneCellAt` and `ZoneContents.words` (other files' definitions). It came with the G2–G4 statements (`dc7d8a23`, 2026-10-15, before the no-unfolding ruling) and #143 does not change it. It is a re-pointing candidate for integration, like `zr_mirror_tape` before it. |
| 18 | note | The public-facing repairs are present; the new lint warning is only size. | **True.** None of the 530 added lines carries a campaign label, path, date or narrative (the screen's one hit, "return-home rounds", names the iteration's rounds); widths are at most 99 (`18-public-text.txt`). **Gate 44's minor 3 is discharged by this landing:** the base's "The left route is stopped under ground rule 4: … (… escalation cont1-E1; `audits/evidence/…`, F2)" (base 723–725) is gone, and the landed file has no "ground rule", "cont1-E1", "audits/" or "corrected". |
| 20 | note | The merged-tree replay supports this partial landing. | **True.** The script's nine blob pins equal the repository's `e9e97970..c60ed898` Lean diff, and the sorry counts sum to 10 (`20-replay-precheck.txt`). **#143 is not yet clear to merge:** #137 merged (`2ff214c5`, 2026-10-22 00:21) after lg4c2 was recorded (`1d4fcf3e`, 00:19). The merged tree (tip `25d0ffa7` with #143; `git merge-tree` clean, tree `0d740fec72d7b04f7e3e39fde6a98a1f4f44cc95`) differs from lg4c2's in `Build/InputWindow` and the facade only (`20-merge-status.txt`). Replay those two modules on the merged tree from a copy of `oleans-lg4c2` (the review's (h): whichever merges later re-replays the facade); #143 is clear once that passes. |
| 1 | note | The packet is intact; this is a source-and-evidence audit, not a fresh Lean certification. | **True; done in part.** The bundle hash and the 65-section list were re-checked, and the bundle's owned-file section is byte-equal to blob `e8353f209617492693aae17c81adc816bad6137e` (`01-identity.txt`). At the landed head against `oleans-lg4c2`, the module was re-elaborated (exit 0; warnings at 1195 and 1237 only; `16-elab-landed-lg4c2.out`), along with the seal, the axioms and the probe (rows 14, 15). The sweep, archive and environment checks rest on the review's records. |
| 2–5, 7, 9, 13, 16, 19 | notes | Ownership and the freeze; the retained definitions; the data and words; the ruler prefix; the writers; the exact time and its bound; the rebalance's credibility; the elaboration and sweep records; the environment record. | No action. (Reproduced for the records: the code identity with comments stripped, 18 → 18 public and 31 → 65 private, and the maintainer commit's four hunks, all in owned regions (`02-freeze.txt`); the route, eight seams and no host or trace (`08-route.txt`); the cost sum and the bound for `ℓ ≤ 39`, the left displacement, and the headroom and disk figures (`09-10-19-arithmetic.txt`). For finding 19, the raw `memory.stat` sample beside the pre-cache line gives 8,158,609,408 B, also above the 4 GiB floor. Addendum v2.4 already states that the cache tool compiles itself.) |

**Reviewer additions (records):**
- Gate 44's replay-message note is discharged: every failure message in `replay-lg4c2.sh` names the
  commit it checks (`e9e97970`).
- **At continuation 3's review**, its brief (dispatched; not to be edited) gives region (a) as
  lines 127–1147. The landed home's last line is 1148 (the `omega` closing
  `zr_rightPass_time_le`), and 1149 is the blank line before 1150. Read the region as 127–1149.
  The brief also says that `oleans-lg4c2` is "exactly that tree", but continuation 3's base
  contains #137, which lg4c2 lacks. For `Build/ZoneRebalance` the upstream closure is the same, so
  the pre-ship results hold. Continuation 3's landing replay starts from #143's merged-tree
  snapshot, not from lg4c2 (`cont3-brief-claims.txt`).

**Carried to the continuation-4 draft** (conditional on continuation 3's outcome; records only):
- **The probe:** deduplicated (428 names plus continuation 3's), counted as "N checks of M names",
  and built as a standalone import of the landed module, with its expected warnings stated.
- **The duplication text:** name each top pair's shared text exactly. List the adapter helper's
  re-pointed instances. Route constant copies through one definition.
- **Whatever of 1.1b is open:** the endpoint, the tape-0 and scratch envelopes, the bridge to
  `zonedTape_extend`, the second seek's agreement on `[−zoneStart ℓ, 0]`, the singleton-exit
  re-wrap, and the level-one sanity instance.
- **The left pass, if open:**
  - the direction-parametrized adjusted walk;
  - the ruler's repositioning, the leftward composition and the restoration;
  - the left ruler's delimiters from the right pass's scratch frame (blank outside `[q, q + m)`),
    not from `zoneRowPre`.
- **The rest of phase 1, then phase 2, as continuation 3's brief states them:** the `ℓ = 0` branch
  by the leaf (cells `±2`, `±3`), cleanup and assembly, then the rebalance row.
- **Region lines re-derived** from the file as landed.
````
