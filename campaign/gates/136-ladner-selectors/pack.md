# Gate 136 · Ladner fill 1: the two selector theorems (PR #304)

**Not yet clear to merge** · PR #304 is a draft. Seyoon dispatches and merges.
The Lean commit is `bd8cd565ce1c9999211173b237f9ff8eae3f3d62`, against campaign Lean
`210d87481ad6837ec34ac8ef99e267e13ff8c95b` (the campaign after #302). This is the first audit.

## Scope

Ladner's theorem [AB09, Theorem 3.3 and its proof] has six admitted targets in
`Diagonalization/Ladner.lean` (gate 128 audited their statements). Codex's fill 1, under the brief
`campaign/fills/ladner-selectors/briefs/ladner-selectors.md` (bundled; pre-shipped, `preship/`),
proves two of them:

- `ladnerH_bounded_of_mem_P : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C`;
- `ladnerH_unbounded_of_not_mem_P : SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n`;

with ten private helpers and the approved import `ClassP.ModelInvariance`. The delivered file is
the PR's only change. The delivery (final zip and two checkpoints, with Codex's `REPORT.md` and
logs) is in the carrier under `delivery/`; its report is data, re-checked here.

## Brief for the auditor

1. **The mathematics.** Check both proofs prove the frozen statements as written, including the
   empty input, index zero, coefficient and degree zero, and the full `∀ n ≥ N` conclusion
   (no monotonicity of `ladnerH` is assumed or available).
2. **Scope.** Only `Ladner.lean` changes; every existing declaration and docstring is
   byte-identical; the ten new declarations are private; no `sorry`, `admit`, axiom or attribute is
   added; the four other targets remain admitted.
3. **Rule 10.** Check each proof reads other files' TCSlib definitions only through published
   equations (the delivery's boundary ledger lists them; the readers of #302 among them), both
   sealed (`seals/`: 12 proofs pass with 22 definitions irreducible; 44 paired controls) and in
   its `rw`/`simp`/`unfold` arguments.
4. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof] or library declarations;
   every proof over 20 lines has a proof sketch; no campaign labels in Lean text.
5. **Duplication.** The delivery adapts arguments from scratch route probes (not library code).
   Check the copy screens: `Ladner.lean` alone (BASE 5 declarations, HEAD 17, no pairs) and
   `Ladner.lean` with seven of its API files (`screen-wide/`, population listed; BASE 253
   declarations and HEAD 265, 49 pairs each, no new pair). Report any proof a new helper should
   cite instead.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure (Ladner and the
  Diagonalization facade) on the campaign snapshot after #302. 2 passed, 0 failed; the 4
  admissions are the remaining Ladner targets.
- Metadata: all 12 new proofs use standard axioms only; both targets print exactly `propext`,
  `Classical.choice`, `Quot.sound`. Lint: no new finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 87 logical files, including the
  delivery zips. Decode each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate136-ladner-selectors-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
