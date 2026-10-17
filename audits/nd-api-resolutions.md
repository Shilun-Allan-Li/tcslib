# The ND inventory API gate (PR #119): resolutions

**Gate:** PR #119, the ND inventory API. It publishes the nondeterministic model's equations that
C1's pre-ship inventory found missing (`audits/evidence/nd-api/NOTES.md`).
- Pack: `audits/nd-api-pack.md`, preserved as dispatched.
- Round 1 bundle SHA-256: `5d9590b3889ec38e701a46beff6b8b128b997d929cb68b9688440a7519977a3c`
  (90 sections; folder `infra_local/gate-dispatches/37-nd-api-gate/`; Lean `1e45f50a`, base
  `531b98a2`).
- **#119 merged before the gate returned** (user, 2026-10-17; tip `75edca6f`). Round 1's repairs
  therefore go into a follow-up PR, which is round 2's object (below).

## Round 1

The findings are in `audits/nd-api-findings.md`, verbatim. **FAIL: 0 blockers, 2 majors,
3 minors, 2 notes.**
- The auditor could not run Lean. It found all 59 new equations faithful and the diff additive.
- It reproduced the patch reversals, the blob pins, the axiom prints, the lint counts, the replay
  log's 189 rows and the screen on the 12 attached population files.

The maintainer's review sub-agent verified every finding at the tip `75edca6f`. All are true, at
the auditor's severities. **Neither major touches a wave-1 route**, so wave 1 issued (ancestor
`83ec6348`). Both are on wave 2's routes (RC and NF).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | RC's route reads `workReadsK`, `tableBitsK` and `actionBitsK`, which have no zero/successor, generic or field equations. `mem_workReadsK` and `length_workReadsK` do not fix the order, and `tableBitsK_two` covers only two tapes, while RC builds a three-tape table. The seeds omit `workReadsK`, `actionBitsK` and `codeSkipActionK`. NOTES' claim that StepBlock's 8 remaining warnings are internals is false for RC. | **True.** The review's table of RC's route also finds the four bit encoders (`signBits`, `optBoolBits`, `optOptBoolBits`, `optStateBits`) unpublished, since RC's sketch re-emits the choice field at the bit level. **The repair, in round 2:** `workReadsK_zero`, `workReadsK_succ` and `tableBitsK_eq` in `Build/StepBlock`; `actionBitsK_eq` and the convenience `codeSkipActionK_append` in `CodeFormat`; the twelve encoder case equations in `Encoding`. All are `rfl` except the skip law. The review's consumer probe (`$S/review/nd-api-gate/probes/RCApiDraft.lean`) derives `workReadsK 3`'s order, the k = 3 table and the choice field's bits with every definition irreducible. **The method:** RC's inventory is re-run against `oleans-lndnf` before its brief is drafted, with the route's definitions themselves as seeds. The maintainer's wave-2 inventory had run against a snapshot without #119 (it flagged `replayTM`'s fields, which #119 publishes). |
| 2 | major | `ndWriterTM`'s only run contract fixes the controller to `Unit`, `stop := false` and `bounded := true`. NF's controller-stopped writer is a different machine (the auditor's Boolean-controller counterexample), so W's same-file exemption cannot cover it. | **True. Resolved by the user's ruling** (2026-10-17; `audits/evidence/c1/C1-fill-plan.md`, last section): a public controller contract, `ndWriterTM_run_controller` in `Build/NDHost`, stated by its own PR and gate after W integrates, and filled by a W continuation. NF's brief (wave 2) cites it. The review checked the draft (`audits/evidence/c1/nf-writer/WriterControllerDraft.lean.txt`) against `ndWriterTM`'s table and found it faithful. Its gate adds a boundary probe at `m = 0` (the stop on the first step, nothing written). |
| 3 | minor | `vhostSilentCfg_eq`'s docstring says the capture tape holds `capPre`; it holds `capPre ++ c.output`. The equation is right. | **True. Fixed in round 2** (a `.lean` docstring): "the capture tape `vhostCap m` holding `capPre` followed by the source's emissions `c.output`, and the physical output `out₀`." |
| 4 | minor | The bundle has no PR body and no `StateRenaming.lean`, one of the 13 screened files. | **True; records.** The PR body is snapshotted at `audits/evidence/nd-api/pr-body.md` (retrieved 2026-10-17, head `1e45f50a`). `StateRenaming.lean` is unchanged by #119: blob `3c6e7ee0` at `531b98a2`, at `1e45f50a` and at the tip. So the screen's 13th member is the base file. For gate 37 as dispatched, the PR-body and 13-file checks rest on these attestations. Round 2's bundle includes the PR body and every screened file. |
| 5 | minor | The pack says eight touched files; there are nine. NOTES says 47 seeds; the seed command passes 48 identifiers, the inductive `NDWriterState` among them. | **True. Pack erratum** (the pack is preserved as dispatched): "eight touched files" (`nd-api-pack.md:35`) reads **nine**. **NOTES corrected:** "over 48 seed identifiers (the inductive `NDWriterState` among them; 29 are definitions and print `SEED` rows)". The 152 output rows stand. |
| 6 | note | The 59 equations are faithful and the diff additive. | No action. |
| 7 | note | The five new screen pairs are configuration boilerplate. | No action. Deriving the ND live-step lemma through `stepWith_eq_fixChoice_step` stays optional. |

**Further NOTES corrections** (the review):
- The `tableBitsK` entry in the "Covered" row is wrong for RC (finding 1). It now points to round 2.
- "those 8 are the step block's internals, read through its run lemmas" is false for RC. It now
  says that RC reads `workReadsK` and `tableBitsK` (finding 1), and the rest are internals.
- The `ndWriterTM` row now reads: "`ndWriterTM` — W's own file (the bounded flavor,
  `ndWriterTM_run_block`). NF's controller-stopped flavor reads a public contract to be stated in
  `Build/NDHost` (user, 2026-10-17; `C1-fill-plan.md`, last section), not the exemption."

**A wave-1 record fix, done before issue:** R's brief reads `tableBitsK` opaquely ("`tableBitsK`
read opaquely (through `serializeK_eq` and `Rep_iff`)", `briefs/c1-fill-core.md:93`), so its
worker does not look for k = 3 lemmas.

**The auditor's suggested sanity lemmas** (zero-budget nonhalting and nonacceptance, the empty
`guessRunCfg` patch, the capture word of `vhostSilentCfg`) are not gate requirements. They are
offered to the fills that meet them.

## Round 2: PR #122 (`lean/nd-api-r2` at `6a48b93e`)

Five commits on #121's round-2 head `0a5878ed`: finding 1's API and finding 3's docstring, gate 38's
minor 5, and the equations the reviews of C1 wave 1's first deliveries found missing
(`counterValue_eq`, `codeBitsNat_eq`, `agreeOn_iff`, `bufferTape_eq`, `bufferTape_of_neg`), and
gate 40's minor 1 (`NDCodeSimulator`'s Design bullet). 22 equations, 3 docstrings
(`audits/nd-api-r2-pack.md`; evidence `audits/evidence/nd-api/r2/`). **Replay passed (user,
2026-10-17):** 313 of 313, static-equal (96). Gate 41 is staged.

## Round 2's plan (as written before the PR)

A follow-up Lean PR, stacked on #121's round-2 head `0a5878ed` (its replay closure overlaps
#121's). It carries finding 1's API and finding 3's docstring, together with gate 38's minor 5 (the
`ClassNP` facade's Contents line; `audits/nd-normalform-resolutions.md`). It is additive, with
docstrings only otherwise.
- Replay: the downstream closure of `Build/StepBlock`, `CodeFormat`, `Encoding`,
  `Build/VirtualInput` and the facade, about 255 modules (91 without `Encoding`; the review
  recommends including the encoders).
- Its gate's pack cites gate 37's findings 1 and 3 and gate 38's minor 5 as the findings it
  repairs. The bundle carries the PR body and every screened file.
