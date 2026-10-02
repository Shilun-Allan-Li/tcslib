# External re-audit pack — Chapter-6 circuit surface, round 3

Audits commit `3ff0d76b` on `complexity/arora-barak-ch1`. Round 2
(pack `audits/ch6-circuits-reaudit-pack.md`, auditing `12ff3add`)
returned **0 blockers, 3 majors, 3 minors**
(`audits/ch6-circuits-reaudit-findings.md`, attached verbatim): round-1
major 2 and minors 5–7/9–10 discharged, the Def 6.1 / Def 6.2 verdicts
upgraded, and the three surviving majors all incomplete propagation of
round-1 repairs. All six round-2 findings were accepted; none contested.
The repairs — commit `3ff0d76b`, documentation only, zero Lean
statements changed — are itemized in the updated
`audits/ch6-circuits-resolutions.md` (attached), together with erratum
**R-E1** (this file's own round-1 "removed" claim, corrected per R2-1)
and erratum **R-E2** (the round-2 pack's "31", corrected to 32; total
55, matching the log). Both sent packs remain immutable.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Freeze.** `3ff0d76b` touches, relative to the audited `12ff3add`:
   six in-scope Lean files (`FeedForward`, `Hierarchy`, `PPoly`,
   `HardFunctions`, `Parity`, `UnaryLanguages`), the catalog,
   `backlog.md` §3's wrapper sentence, the resolutions file, and the
   newly committed `audits/logs/`. Docstrings and comment prose only;
   no `def`/`theorem`/`lemma`/`structure`/`instance` signature or body
   changed. Zero sorries in scope, as before.
2. **Exhaustive-propagation grep.** On the full `TCSlib/` tree plus the
   catalog and `backlog.md`, the retired phrases — "embedding is
   faithful", "is a weaker statement", "never rules out", "never
   discharge", "never a gate basis", "fan-in matters only", "embedded
   feedforward", "whose class is `Language.InSIZE`", "image size never
   mentions" — now have **zero occurrences**. (Round 2's majors were
   exactly phrase-survivals; this attestation is the systematic check
   round 1's repairs lacked.)
3. **Elaboration.** Post-repair fresh-olean sweep (run D of the
   resolutions appendix): the circuit order list from `FeedForward`
   onward plus the catalog, 20 modules, zero `error:` lines — the
   Switching/LMN trees import none of the six edited files. Lean 4.25.0
   / mathlib `029db123ddaa`. Raw logs for runs A–D are now committed
   under `audits/logs/`, addressing round 2's provenance caveat to the
   extent a bundle can.
4. **Policy.** Style lint: 0 FAIL / 0 WARN over `CircuitComplexity/`,
   unchanged.

## What round 3 asks

A closing verification round. The settled round-1/round-2 verdicts and
attack results stand unless a round-2 repair touched their text. Tasks:

1. **R2-1 … R2-3.** Judge whether each repair discharges the finding:
   the conversion overview and remaining "embedded" docstrings in
   `FeedForward.lean` (R2-1); the Main-results bullet in
   `Hierarchy.lean` and the fan-in sentence in `PPoly.lean` (R2-2); the
   "weaker statement" conclusion and the sharing warning in
   `HardFunctions.lean` (R2-3).
2. **R2-4 … R2-6.** Verify the two prose minors and the reconciled
   verification appendix (runs A–D, the disjointness claim for run C's
   two segments, erratum R-E2's arithmetic `22 + 32 + 1 = 55`, and the
   committed logs' consistency with the attested counts).
3. **Residual pass** over the newly written prose, including the two
   errata texts, under the round-1 severity scheme.

Findings to `audits/ch6-circuits-round3-findings.md`. The gate closes on
zero blockers/majors in this round.
