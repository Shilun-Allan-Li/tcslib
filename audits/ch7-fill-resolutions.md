# Chapter 7 fill gate — resolutions (OPEN: round 2 asks the duplication question)

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

## Round 2 (pending)

Pack: `audits/ch7-fill-r2-pack.md`, with bundle `audits/ch7-fill-r2-bundle.md`.
It asks question 7 on the merged tree and checks the round-1 sweep. Findings
go to `audits/ch7-fill-r2-findings.md`. The gate closes on zero blockers and
zero majors.
