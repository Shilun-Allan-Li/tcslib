# Gate 11 · Levin padding proof

Round 1. Auditor Codex. Draft [PR #286](https://github.com/Shilun-Allan-Li/tcslib/pull/286)
at `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` on branch `codex/pass-shelat-levin-padding`,
targeting `cryptography/pass-shelat-ch2-4` on base `5bcf11aaf08963ab33ce608ea7509e7403e4351a`.
The campaign has since merged #284/#285 (`4a09f399`), which change none of the PR's files; the
maintainer verification ran on a trial merge with that head.

This proof audit covers the formerly admitted `PadQuad.exists_linearTime_gStr`
(`Asymptotic/UniversalPadding.lean`) and everything added to prove it. With it, Lemma 64.3
(`lemma_64_3`) and the conditional Theorem 63.1 (`theorem_63_1`, under its explicit canonizer
hypothesis) print only standard axioms. The source is [PS10], R. Pass and a. shelat, *A Course
in Cryptography*, third edition, January 2010, Theorem 63.1 and Lemma 64.3 (Levin's universal
one-way function, book pp. 63–64), with the padding argument of [Gar26, Lemma 2.3] cited in the
module docstring. `exists_canonizerExp` remains a separate admitted task and is out of scope.

## The padding theorem

Check that `exists_linearTime_gStr` is proved with its original header, for every function `F`
computed by a finite machine in time `C·(n+1)^c`, and that the padded function is computed in
linear time as stated. Follow the route: parameter recovery from the input length (`Parameter`),
binary search for the shifted root (`BinaryRoot`), padding assembly (`Machine`), quantitative
concatenation (`WordTiming`), unary polynomial evaluation (`UnaryPolynomial`) and binary-to-unary
emission (`ClassP/BinaryArith/Unary`). Derive the time bound independently. Test small inputs
(the absorbed finite prefix), the boundary lengths where the recovered parameter changes, empty
data, and inputs whose length is not of the padded form. Confirm that no step's cost is charged
at the wrong argument length.

## Changed infrastructure

`TuringMachine/Build/EmitIterBody` gains `exists_emitIterTM_withFuel` (a supplied fuel machine and
a separate round-count bound) and re-derives `exists_emitIterTM` from it; `TuringMachine/Build/
Primitives` changes `pairMap_computes`. Check that every older statement and definition is
preserved (the statement comparison reports CHANGED only the two `pairSplitAt` theorems below)
and that the moved `nu` block in `UniversalPadding/Parameter` is verbatim, with its new reader
`nu_eq`.

## The maintainer repair commit

The final commit publishes readers so that no touched proof reads another file's definition:
`Turing.safeRun_iff` (`Build/EmitIterEmbed`), and `Turing.pairSplitAt` with three readers
(`Randomized/Build/PairSplit`). `exists_pairSplitTM` and `computesFunInTime_pairSplitAt` are
restated against `pairSplitAt`; they must be the same propositions as before. Check that
the consumers (`Randomized/Primitives`' typed cuts, `UniversalPadding/Machine`) prove what they
did, and that the deleted private `split`/`split_pair` copies left no use behind.

## Rule 10 and evidence

Policy §1, rule 10: no touched statement or proof reads another file's definition. The
verification seals each changed file against its whole import closure, computes the touched
set against the PR base, compares untouched failures with a base control, runs controls and an
explicit-reader scan. Rulings in force: the 52 approved provider pairs (provider reuse,
2026-11-10); F3, a docstring-only change counts as untouched; `PolyExpr.eval` is notation.
Inherited untouched failures stay in the deferred cleanup ledger and are not findings of this
gate unless the PR made them worse. Review the evidence against its stated coverage and the
recorded attempt dispositions, including the segmented and chunked seals and the superseded
attempts.

Inspect the sixteen source files and exact diff, the worker report, the maintainer verification
and policy. Check imports, docstrings with proof sketches, the facades' exports and global
attributes. The PR's 15 module-docstring lines over 100 characters are known; report them as
minor only if you consider them a policy defect.

## Findings delivery

Return `gate11-levin-findings.md` as a Markdown file in this chat. For multiple evidence files,
return a ZIP containing the Markdown and the evidence. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use blocker for a false or unusable statement or substantive scope violation, major for a
missing premise, an incomplete machine or timing argument, a forbidden new read in a touched
declaration, or unverifiable necessary evidence, minor for documentation or API defects, and
note for further observations. Report the exact audited head and counts by severity. The gate
closes at zero blockers and zero majors.
