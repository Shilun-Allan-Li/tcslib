# External audit pack — §13d G4, continuation 4: the zone extension and rebalance rows (the G4 landing, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, the §13d zone revision (the Hennie–Stearns
simulation's machine rows, [AB09, §1.7]). The fill brief G4 continuation 4
(`campaign/fills/s13d/briefs/s13d-fill-g4-cont4.md`, issued at the inputs commit `f89c5c8d`)
targets `Turing.exists_zoneExtendTM` and `Turing.exists_zoneRebalanceTM`
(`TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`). It was delivered complete on
2026-10-25 (`fill-s13d-g4-cont4.zip`, SHA-256
`4d1667b72b5c366ad3cbd5c679ac9d4f93e7dcda1687ebc966af5cc24b37fce7`). The worker's report is
`campaign/fills/s13d/reports/g4-cont4-REPORT.md`; the maintainer's review is
`campaign/fills/s13d/reviews/g4-cont4/REVIEW.md` ("complete (2/2), no admission; land by a
maintainer PR with one re-point and the status edits, after the user's rulings"), with its
evidence (`out/`, `probe/`, `scripts/`). The process rule of the §13d revision applies: a PR the
user merges, and this gate.

**The user's rulings (2026-10-25)** on the review's decisions:
- **F5, the route deviations:** accepted (no level-zero branch; the column moves cut their
  scratch copies instead of re-packing by `scanTM_contract`; `dir = false` by the mirrored machine
  and `Turing.Contract.lockstep`), with the targets' construction sketches brought in line (B1,
  B2).
- **F2, `zr_pinLoop`** (it re-does `Turing.Round.iterate`'s induction along a sequence of pass
  indices): land with a ledger entry (RI-1); an API PR then adds the sequence form to
  `Build/Contract/Basic` and re-points it.
- **F3, the missing proof sketches:** the maintainer writes them before this gate.

**The landing:** PR #165 on `lean/g4-cont4-landing` at `37fe114e`: 39 commits on the campaign
branch at `cfaaf75a` (Lean equal to the tree after #161), then a records-only merge of the campaign
branch (`37fe114e`). The 39 commits' content is what this gate audits
(`campaign/fills/s13d/evidence/s13d-g4-cont4-landing/patches/`):
- 37 commits, the delivery's format-patch series applied unchanged by `git am -3` (the worker's
  authorship and subjects kept, as for F3 continuation 2); they reproduce the delivered file
  byte for byte (blob `7e42db77`);
- `4d69c096`, the review's landing edits: A1–A3 (the module's status paragraph, its main-results
  entry and the `TuringMachine` facade's entry say the rows are proved), C1 (F1: the private
  `zr_contents_ext`, a copy of the published `Turing.ZoneContents.ext'`, deleted and its four uses
  re-pointed), B1–B2 (the two rows' construction sketches describe the proofs taken);
- `292acad2`, the maintainer's 83 proof sketches (F3), docstrings only: the code is identical
  with comments stripped.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Targets proved** | `Turing.exists_zoneExtendTM` (`C = 135`), `Turing.exists_zoneRebalanceTM` (`C = 2300`), with no `sorryAx` |
| **Privates** | 73 → 853: 782 new `zr_` declarations (783 delivered, less `zr_contents_ext`), 2 removed before zip 3 (`zr_RightData`, `zr_left_two_walks`), 36 inherited ones restated or re-proved inside the owned regions |
| **Frozen** | every public statement and docstring outside the authorized status paragraphs; 18 → 18 public declarations; imports unchanged |
| **Text** | the status paragraph and main-results entry (A1, A2), the facade's entry (A3), the two construction sketches (B1, B2), 83 proof sketches |

## Brief for the auditor

1. **Faithfulness.** Do the proofs establish the frozen statements, for both directions and every
   level, including `ℓ = 0`, `i₀ = 0` and the short escape? Check the constants `135` and `2300`
   against the time bounds (`zr_extend_time_le`, `zr_rowC_time`, `zr_fpSeg_time`) and the head
   envelopes.
2. **The accepted route deviations (F5).** Is each sound and within the brief's binding rules (no
   new public name, no admission, no unpublished lemma)? In particular the mirror: is
   `zr_mir_step` exact (tape `0` and its head reflected, the input head and the other tape
   unchanged), and does the lockstep transport give exactly `zoneRebalancePost false` with the
   reflected envelopes (`zr_mir_post`, `zr_mir_env`, `zoneRebalance_false`, `zr_mirror_tape`)?
3. **Rule 10** (with the scope of 2026-10-23). The review's seal: 82 TCSlib definitions sealed and
   `Action.apply` erased from `simp`; the body has 0 errors; 81 of 82 controls fail sealed and
   close unsealed, the 82nd (`Contract._sizeOf_inst`) used only by compiler-generated helpers. No
   other-file definition is passed to `rw`, `simp` or `unfold`; the core simproc `reduceCtorEq` is
   used 8 times. Does any step still close only because another file's definition reduces?
   **Rule 11:** no R3 row, no other file's private.
4. **Duplication.** Text: the v3 screen on the brief's 10-file population, under the lock, at the
   campaign tip (`39c649e6`, the tree after #161) and at the landing's last content commit
   `292acad2` (`screen-base-tip.txt`, `screen-head-292acad2.txt`): 847 → 1,391 declarations,
   477 → 970 pairs; 500 new and 7 gone, every new pair inside `ZoneRebalance` and none at 90% or
   more (the highest 88%), no cross-file pair (`pairdiff-head-vs-tip.txt`). The base equals the
   brief's screen base exactly, and the head's pairs are exactly the worker's after-screen's
   (`pairdiff-head-vs-worker-after.txt`; the landing edits change no pair). Are the in-file pairs
   justified (the worker's lists, `campaign/fills/s13d/reports/g4-cont4-REPORT.md`)? Semantic: the
   review's search (`out/34-semantic-dup.txt`) found F1 (fixed by C1) and F2 (RI-1, ledgered by
   the ruling). Is any other new private a re-derivation of published API (the catalog contracts,
   `Contract.seq`/`branch`/`inPhase`, `Round.iterate`, `Turing.Lockstep`, the phase host's lemmas,
   the `Cfg.mapState_*` and `seekPost_*` field equations)?
5. **The maintainer's text.** The 83 proof sketches were written by the maintainer, not the
   worker, from the proofs: is each an accurate reading of its proof, naming its key steps? A1–A3
   and B1–B2: accurate? All public-facing (no campaign labels, paths or dates in new Lean text;
   the frozen statement docstrings keep their old "§13d G4" headings)?
6. **Records.** The review's F6 (the worker's seal gaps, closed by the review's seal), F7 (no
   checkpoint zips in the inbox; pairs justified by class in undelivered reports; labelled commit
   subjects; `synthInstance.maxSize` up to 1024) and F8 (4.4–4.5 GiB peak memory on the fill
   host, above the addendum's measurement): any correctness gap?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the review: the delivered file with no diagnostic at all at the base
  (`oleans-lphl2`), at the campaign tip `5cade0b8` (`oleans-lrcan3`) and after #161
  (`oleans-lu2api`). The maintainer: the landing head's file against `oleans-lu2api`, with no
  diagnostic, in 185 seconds and 3.6 GiB, with both targets' axiom prints
  (`campaign/fills/s13d/evidence/s13d-g4-cont4-landing/`).
- **Axioms:** both targets on `[propext, Classical.choice, Quot.sound]` (the review, all 872
  declarations; the maintainer, at the landing head).
- **Probes** (the review): the brief's import probe (448 checks) and the worker's (501), 0 errors.
- **Sweep** (the worker; checked by the review): 96 modules, 27 → 25 sorry warnings, exactly the
  base set less the two targets.
- **Lint** (the landing head): `TuringMachine` 0 FAIL, 67 WARN over 83 files, exactly the base's
  lines (`ZoneRebalance` now 15,355 lines, 18 public / 853 private); no line over 100 characters.
- **Replay:** `replay-lg4c4.sh` (in the landing evidence), `ZoneRebalance`'s downstream closure
  (2 modules: `ZoneRebalance`, the `TuringMachine` facade) at `37fe114e`, chained from
  `oleans-lu2api`. **Pending** (the gate is dispatched before it). It meets #162's closure only at
  the facade, which both edit in different lines.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/75-s13d-g4-cont4-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `s13d-g4-cont4-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
