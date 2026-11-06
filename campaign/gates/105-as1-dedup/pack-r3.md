# External audit pack, round 3: dedup AS-1 (PR #214, a dedup gate): the dispositions only

**Round 2** (`pack-r2.md`, `findings-r2.md`) was **HOLD: 0 blockers, 2 majors, 2 minors**. Both
majors widen the family beyond what #214 changes:
- **Finding 1:** implicit `astep` reductions by unification, with no `astep` in the text, such as
  `AReach.step` followed by `change`/`exact`. `Mult` crosses one fifth.
- **Finding 2:** consumers read each machine's instruction table (`A`, `CA`, …) across files, by
  `show A .l = _ from rfl` or `simp [A]`. That read predates AS-1.

**The user ruled on 2026-11-06: land #214 and acknowledge both majors as scoped debt, with
scheduled resolutions.** They are recorded as ledger families **AS-2** and **MT-1**
(`campaign/duplication-ledger.md`), each with its named members, its threshold crossing and its
resolution. Both are separate PRs in this dedup window, AS-2 after #214 merges. Minors 3 and 4
are accepted. The accounting conventions are reconciled, and the elaboration attestation is
narrowed to the retained logs (`resolutions.md`, § Round 2).

**#214's code is unchanged since round 2:** head `92e53e6e`, the same 38 files and the same
evidence.

## Brief for the auditor

1. **The acknowledgments:** do AS-2's and MT-1's ledger entries name round 2's members, the
   threshold crossing and a concrete resolution, as TEMPLATE requires for acknowledged debt?
2. **Minors 3 and 4:** are the reconciled site counts and the narrowed elaboration attestation
   accurate?
3. **#214:** confirm that the head is unchanged from round 2, so that round 2's notes 5–7 still
   stand.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/105-as1-dedup/findings-r3.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `as1-dedup-r3-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
