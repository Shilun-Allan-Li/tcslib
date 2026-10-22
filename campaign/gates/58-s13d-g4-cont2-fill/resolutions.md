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
| 20 | note | The merged-tree replay supports this partial landing. | **True.** The script's nine blob pins equal the repository's `e9e97970..c60ed898` Lean diff, and the sorry counts sum to 10 (`20-replay-precheck.txt`). #137 merged (`2ff214c5`, 2026-10-22 00:21) after lg4c2 was recorded (`1d4fcf3e`, 00:19). The merged tree (tip `25d0ffa7` with #143; `git merge-tree` clean, tree `0d740fec72d7b04f7e3e39fde6a98a1f4f44cc95`) differs from lg4c2's in `Build/InputWindow` and the facade only (`20-merge-status.txt`): see **Merge state** below. |
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

**Merge state.** Since the replay `lg4c2`, the campaign branch gained #137 (`Build/InputWindow` and
the facade's line). Its closure meets #143's only at the `TuringMachine` facade, so no re-replay is
needed under the campaign's standing rule for facade-only overlaps. The review proposed a 2-module
re-replay of the merged tree (`Build/InputWindow`, the facade) from `oleans-lg4c2`; it stays
available if the user prefers it.
**#143 merged** (2026-10-22, `b7447492`), under the facade rule.
