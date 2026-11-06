# External audit pack, round 3: G5's landing, `Turing.FinTM.two_work_tapes_run` (PR #211, a fill gate)

**Round 2** (`pack-r2.md`, `findings-r2.md`, `resolutions.md` § Round 2) found both round-1 issues
fixed (note 3) and no soundness defect. Its verdict was **HOLD, 0 blockers, 2 majors, 0 minors**,
both majors about the zero-time impossibility outside #211's file:
- **Finding 1:** the deterministic sweep missed `Build/Loop`'s private
  `emCall_prepared_eval_first` and `CircuitComplexity/Advice`'s
  `DTIMEAdvice_eq_empty_of_eq_zero`, which re-derive `FinTM.not_computesInTime_zero`.
- **Finding 2:** NZ-1, the nondeterministic reading, had at least four members, not two, and
  was unacknowledged.

**Both are fixed in PR #217**, not in #211. The two deterministic sites lie outside #211's one
file, and `Loop`'s downstream closure is large. The user acknowledged NZ-1 on 2026-11-06 and ruled
"publish and re-point now". #217 has its own dedup gate, **gate 108**
(`campaign/gates/108-nz1-dedup/pack.md`, in this bundle). #217 does the following:
- publishes `Turing.NDTM.not_haltsWithin_zero`;
- re-points the five NDTM copies: round 2's four, plus `BPTIMEThreshold`'s
  `BPDecidesInTimeWith.one_le`, found by the by-kind search;
- re-points both deterministic sites to `FinTM.not_computesInTime_zero`.

The ledger's NZ-1 entry now covers both readings, with the search and its exclusions.

**#211 is unchanged since round 2:** head `e7e78aaf`, one file, `TwoTapes.lean`. This round
re-checks the dispositions only.

## Brief for the auditor

1. **Findings 1 and 2 of round 2:** are both resolved by #217 as described? Is the NZ-1 entry's
   census and search by kind adequate? Gate 108 audits #217 itself; here the question is whether
   round 2's two majors are discharged.
2. **#211:** confirm that its head and file are unchanged from round 2 (`e7e78aaf`), so that
   round 2's notes 3–6 still stand.

## Repository-side attestations (verify or challenge)

- **#211:** head `e7e78aaf`, unchanged since round 2. Round 2's replay, seal, axioms, screen and
  lint evidence stand (`evidence/round2/`).
- **#217:** `replay-lnz1`, 261 modules, 0 failed, chained from the campaign snapshot. Its
  freeze shows the one public addition and no statement changes. Both are in gate 108's
  evidence, which this bundle includes.
- **Merge order:** #217 merges after gate 108 closes, then #211 after this round closes. #211's
  file and #217's files are disjoint (`TwoTapes` against eight others). #217's downstream closure
  does contain `TwoTapes`, which `replay-lnz1` compiled at the campaign's version, still with its
  `sorry`. So the merge that comes second is replayed on the merged tree, `TwoTapes`'
  closure included.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/102-g5-landing-fill/findings-r3.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-landing-fill-r3-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
