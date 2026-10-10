# Chapter 7 fill gate — resolutions (CLOSED, round 2)

## Round 1 (2026-10-10): 0 blockers, 0 majors, 2 minors, 2 notes

Findings verbatim in `audits/ch7-fill-findings.md`.

**Provenance.** The auditor hashed its input as `00be8b1d…`. That is
`0c22ae33:audits/ch7-fill-bundle.md`, the bundle from Aparna's fork, not the
merged-tree adaptation `audits/ch7-fill-bundle.md` (`39eacf62…`). Round 1
therefore audited questions 1–6 on the fork's sources, and **question 7
(duplication, `audits/TEMPLATE.md` failure mode 5) was never asked.**

**Transfer to the merged tree (verified, `audits/logs/ch7-fill-r2-transfer.log`).**
Of the nine Lean files round 1 audited, six are byte-identical at the round-2
commit to `0c22ae33`. The other three, `EmitIterEmbed`, `PolyTimeBlockLoop`
and `PClosure`, differ in comments only (comment- and whitespace-stripped
identical): the P0 finding-5 docstrings in `PClosure` and the round-1 sweep
below. The statement findings of questions 1–6 therefore carry over unchanged.

**User decisions (2026-10-10).** (1) A short follow-up round on the merged
tree asks question 7 only; questions 1–6 are not reopened. (2) The maintainer
sweeps the minors on the campaign branch, and Aparna pulls them on her side.
(3) Finding 2 is resolved by correcting the summary; any API change waits for
12.2c item 6 (EmitIter ↔ §12 unification).

| Finding | Disposition |
|---|---|
| 1 (minor): `PolyTimeBlockLoop`'s module summary credits XOR to the abandoned one-pass counter program | **Swept** (doc-only): the bullet now reads "polynomial-time, via the emit-iteration loop" |
| 2 (minor): `EmitIterEmbed`'s summary advertises `Turing.control_step`/`control_step'`, which are private in `EmitIterBody` | **Swept** (doc-only): both names are removed from *Main results*, and the "control steps" bullet now says these are private helpers of `EmitIterBody`, not exports of this module. No API change; 12.2c item 6 settles that layer |
| 3 (note): the three block headlines are total extensions through default decoding | **Carried as documentation**: one paragraph added to `PClosure`'s "Block-query closure" section docstring. Malformed words are classified by the same test on their default-decoded components, an invalid inner pair keeps only the outer mask, and `V` is consulted only on re-encoded queries. Statements unchanged |
| 4 (note): `exists_emitIterTM`'s all-iterations orbit bound is sufficient, not necessary | **Carried.** No change; a scheduled-orbit generalization is optional future work |

**Sweep verification.** The diff is
`audits/evidence/ch7/ch7-fill-r1-minor-sweep.diff`, comment-only in all three
files. The seven-module chain from `Build/EmitIterEmbed` to
`Randomized/PolyTimeModel` re-checks with 0 errors
(`audits/logs/ch7-fill-r2-docfix-sweep.log`). Lint reports 0 FAIL in
`ClassNP` and `TuringMachine/Build`.

## Round 2 (2026-10-10): 0 blockers, 2 majors, 2 minors, 2 notes — CLOSED on the user's acknowledgments

Findings verbatim in `audits/ch7-fill-r2-findings.md`, audited at `4502c30f`.
Questions 1–6 transfer unchanged (R2-6: the transfer attestation and the
round-1 sweep check out, including the nested malformed-input reductions).
Both majors are **governance majors** under `audits/TEMPLATE.md` failure
mode 5. Neither refutes a statement. Per that rule, the gate closes once the
human maintainer explicitly accepts each debt and names its resolution.

| Finding | Disposition |
|---|---|
| R2-1 (major): `EmitIterEmbed` re-proves five existing run facts, at least 5/18 = 27.8%: `step_output_prefix` and `runFrom_output_prefix` (Loop's private `emLoop_step_prefix`/`emLoop_run_prefix`), `runFrom_output_extends` (a specialization of `Finite`'s public `MultiTapeTM.output_prefix`), `runFrom_of_halted` (`Deterministic`'s public `runFrom_of_halt`), and `state_isSome_of_runFrom` (Loop's private `loop_live_prefix`) | **ACKNOWLEDGED (user, 2026-10-10)** as `backlog.md` **CH7-D2**: owner 12.2c item 6. One home for the run facts in `Deterministic.lean`/`Finite.lean`; `EmitIterEmbed`'s five become citations or re-exports, statements unchanged; Loop's three private copies deleted. |
| R2-2 (major): under the standing source-inclusive census, CH7-D1 reaches at least 12/25 in `PolyTimeBlockTests`, which crosses one fifth in a further file; at least 8/14 in `PolyTimeBlockMajority`; and 1/32 in `PolyTimeBlockLoop`. The auditor found four further cross-file adaptations (`anyStep`/`majStep`, `anyEmit`/`majEmit`, the orbit lemmas, the loop outputs; 81–93%) and two length correspondences | **ACKNOWLEDGED (user, 2026-10-10)**: the CH7-D1 extension, with the same owner (12.2c item 7) and resolution, its scope widened to the full family. The ledger now uses the source-inclusive census. The auditor confirms the generic-lemma resolution remains feasible. |
| R2-3 (minor): the screen description overstated its method, and the `EmitIterBody` count was stale | **Swept.** The screen record's method text is corrected, with a pointer to the round-2 misses, and the ledger watch item now says 20 declarations (1 public, 19 private). |
| R2-4 (minor): the pack inventory still listed `control_step`/`control_step'` | **Swept.** An erratum is in `audits/ch7-fill-pack.md`'s scope row. |
| R2-5 (note): contract-level facts comparing EmitIter with `Build/Embed` | **Carried** into 12.2c item 6 as its scoping facts. |
| R2-6 (note): transfer and sweep verified | No action. |

## Round 2 pack (as issued)

Pack: `audits/ch7-fill-r2-pack.md`, with bundle `audits/ch7-fill-r2-bundle.md`.
It asks question 7 on the merged tree and checks the round-1 sweep. Findings
go to `audits/ch7-fill-r2-findings.md`. The gate closes on zero blockers and
zero majors.
