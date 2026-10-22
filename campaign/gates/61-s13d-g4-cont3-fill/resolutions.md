# §13d G4 continuation 3: checkpoint 1.1b's landing (PR #148, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #148 (`lean/g4-cont3-partial` at `13e17589`, on the campaign branch
at `43d22595`, its parent and merge-base): the worker's commit `01bcc6e0` cherry-picked, 8
private `zr_` declarations added and 4 re-pointed; both targets stay admitted. Pack `pack.md`;
bundle SHA-256 `d8a7ec3ae0b1f2df87159d35fec4bc2db97a25f5c93d7ec00df493240ac22abb` (107 sections;
folder `61-s13d-g4-cont3-fill-gate/`). Replay `replay-lg4c3.sh` passed (user, 2026-10-22): 16 of
16 at `13e17589`, static-equal (10).

**Round 1** (`findings.md`, verbatim; received 2026-10-22, SHA-256
`30d8e6293e445347d71933455655d1da77016cc4ecc74ab3f3a70bf1abc5488e`): **PASS, 0 blockers, 0 majors,
2 minors, 16 notes. The gate is closed; the landing is a partial.** No `.lean` change. The
maintainer's review sub-agent verified every finding (with gates 59 and 60): 17 true, 1 partly
true (`campaign/gates/59-c1-seamlayout-fill/evidence/round1-review/REVIEW.md` and its `out/`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 10 | minor | `seal-head.out`, `seal-tip.out` and `targets-1_1b.out` are absent from the bundle's 107 sections and from the pinned tree, so the seal and characterization results are reviewer attestations. | **Partly true; records.** Absent from the bundle: true. Absent from the pinned tree: **false**. All three were committed with the review at `ca7d1fed` (13:46), before the bundle's records revision `050d547e` (13:52), with the same blobs then and now. The bundle list kept only the first 60 entries of the review's 81 `out/` entries, and the cut fell just before `seal-head.out` (`out/61-F10-missing-outputs.txt`). Their contents show what the review said: four errors at the four `rfl` controls inside the seal and nothing else failing, the outside controls clean, the two targets' warnings; and the characterization probe at exit 0 with every example elaborating. **Evidence note:** `evidence/round1-review/10-outputs.txt` (the three outputs by path and blob, with their probes, commands and exits). No re-run is needed: both probes embed the landed bytes. **Review erratum** (here; the review stays as written): for `targets-1_1b.out`, "0 errors, only the two target warnings" reads "0 errors; the two target warnings and one unused-variable linter warning in the reviewer's appendix (line 1693)". |
| 11 | minor | The report puts `Turing.two_le_zoneStart` in the supplied inventory; it is in neither probe. The counts are 439/428, 445/434 and 446/435. | **True, and more than stated:** the frozen public `zoneRebalancePost_frames` already cited it at the base, so the brief's 439-check inventory missed a base citation too (`out/61-F11-probe-counts.txt`). It is public (`Build/ZoneTape.lean:184`) and cited by the new `zr_rightPass_bounds` and `zr_rightPass_tape`. **Report erratum** `campaign/fills/s13d/reports/g4-cont3-ERRATUM.md` (item 1). **Carried** to continuation 4 (below): 446 checks of 435 names, and an inventory taken from the whole module's elaborated constants. |
| 8 | note | The re-wrap removes the exit-set mismatch, subject to the instance requirement; the probe's `let _C := …seq …` is a partial application. | **True; carried.** `Contract.seq` takes `link` and `hlink`: the probe gave a placeholder `link` and no `hlink`. The instance remedy was already carried; **the real `link` and the proof of `hlink` were carried nowhere**, and now are (below). **Review erratum** (here): the review's row "Re-wrap composes: PASS" reads "the types compose (a partial application: `link` a placeholder, `hlink` not supplied)". |
| 6, 13 | notes | Use the preserved left interval, not global scratch blankness, for the second seek; introduce per-stage field lemmas before the left pass. | **True; already carried** (the review's (h) list, gate 58's list, the backlog); restated below so that continuation 4's draft has one list. |
| 3 | note | The adapter and the re-wrap mean what they should; promoting the adapter is a suitable later API change. | **True; backlog** (the shared-API window): promote `zr_singletonContract` beside `Contract.ofSegment` (`Build/Contract/Basic`) or as a `Contract.seq` corollary (`Build/Contract/Seam`), as a `def` with non-`simp` field lemmas, by an API PR with its gate. |
| 7 | note | The boundary instances show no counterexample; keep them in future integration probes. | **True; carried** (below): level one (scratch at −7: cells 5–8, heads 7 and −7, time 48) and level two (scratch at 5: halves 10–13 and 14–17, heads 14 and 5, time 73). |
| 15, 16 | notes | Both frozen statements are credible and unproved. | **True; carried** (below: the open obligations). |
| 17 | note | The recovered checkpoint is self-consistent; keep the review's corrections with the historical records. | **True; report erratum** items 2 and 3 (the review's F2 and F3: the seal without controls, the fixed-text rewrite audit, the empty packaging log, the stale `Work.lean`, a 4,096 B disk discrepancy). |
| 2, 9 | notes | Only the authorized partial lands (do not re-land #143's commits); the seal and the argument inspection support rules 10 and 11. | **No action**; both carried as continuation 4's base and evidence rules (below). |
| 1, 4, 5, 12, 14, 18 | notes | Bundle identity; the four refactored contracts; the endpoint; elaboration, axioms and probes; lint and status text; the interruption and the replay. | **No action.** Re-checked: the hash and the 107 sections; the owned section equals blob `1abbb8716d0450ea9b7cc10ef15e6204ed920b4a`; the freeze 18 → 18 public, 65 → 73 private; lint 0 FAIL, 31 WARN over 39 files; the replay's 11 pins. |

**The carry into G4 continuation 4's draft (C61-1).** The draft is not written yet. It takes the
g4-cont3 review's (h) list, gate 58's carry list less its 1.1b items (discharged by this landing),
and these points:

> - **The return home's seam.** Sequence `zr_rightPassRow` into the return home's first row by
>   `Contract.seq`. Give the 12-leaf state type's `DecidableEq` explicitly (a private instance
>   term, or `set_option synthInstance.maxSize 256 in` on that declaration alone; default search
>   fails, and more heartbeats do not help). Supply the real `link` (the outer half's word) and
>   **prove `hlink`**: the next row's precondition from `zr_rightPass_post`, with
>   `zonedTape_blank_outside` for the cell beyond the old layout. Gate 61's probe checked only
>   that the types fit.
> - **The second seek.** State its precondition by two local facts: tape 0 equals the start's at
>   every `q ≤ 0` (`zr_rightPass_tape`), hence agreement on `[−zoneStart ℓ, 0]`; and scratch is
>   blank off `[q, q + m)` (`zr_rightPass_post`). Not `zoneRowPre`'s global facts, which fail
>   after the right pass.
> - **Per-stage field lemmas.** Prove `time`/`lo`/`hi` per sub-composite and combine them; do not
>   add a third whole-composite `simp only` expansion beside `zr_rightPass_time` and
>   `zr_rightPass_bounds` (already an 85% pair).
> - **The probe.** Start from 446 checks of 435 names (the worker's 445 of 434, plus
>   `Turing.two_le_zoneStart`), add continuation 4's own, count it as "N checks of M names", and
>   build it as a standalone import of the landed module with its expected warnings stated. Take
>   the inventory from an elaborated-constant walk of the whole module.
> - **Boundary instances** as probe examples: level one and level two (above), and the left
>   pass's `ℓ = 1` instance.
> - **Rule-10 evidence.** A seal with controls (failing inside, passing outside) and an
>   argument-by-argument inspection table; the raw outputs of the seal, its controls and the
>   characterization probes shipped with their commands and exit statuses.
> - **Open.** The extension: the return home, the left pass, the `ℓ = 0` branch (a separate fixed
>   sequence), ruler cleanup and assembly. The rebalance: the scan, the guarded column moves, the
>   passes, the home move, the mirror and cleanup. Both admissions stay until proved.
> - **Base.** The campaign branch with #143 and #148 merged; do not re-apply #143's commits.
>   Region lines from the landed file (1,572 lines, 18 public / 73 private; targets at 1396 and
>   1439).

**Reviewer additions (records):** the bundle-list cap (minor 10's cause; the lesson is in gate
59's resolutions), and the two review errata above (rows 8 and 10).

**Merge state.** #148 is on the campaign branch (not stacked); its closure meets the other open
PRs' only at the facade. **Clear to merge.**
