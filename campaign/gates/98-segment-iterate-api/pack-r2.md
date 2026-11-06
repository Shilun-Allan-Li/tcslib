# External audit pack, round 2: segments composed along a sequence (PR #202, an API gate)

**Round 1** (`pack.md`; findings `findings.md`; dispositions `resolutions.md`) was **does not
close, 0 blockers, 1 major, 1 minor, 4 notes**. The new lemma, its statement, home and corollary
were verified (notes 3–6). The issues were the ledger and the evidence:
- **Finding 1 (major):** `Tautology`'s `tautDual_segment_add` and `CounterLoop`'s
  `counter_span_append` re-prove `Segment.trans` for private segment predicates, and no ledger
  family covered them. Round 1's pack also said that all 23 pairs with a `Contract/Basic`
  declaration were inside that file, though one is `Segment.trans` against
  `tautDual_segment_add`.
- **Finding 2 (minor):** the screen trees were not the audited head (1,339 declarations, not
  1,341), and the bundle carried 2 of the population's 17 files.

**The PR is unchanged:** #202 on `lean/segment-iterate`, head
`7b5774fb8d47fd119d2d314f9f6e717cffcee7de`, one file, `Build/Contract/Basic` (blob `43fce3e2`).

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1 | **Acknowledged by kind (the user, 2026-11-06), for the dedup window 12.2c:** the ledger's new family **SG-1** (`campaign/duplication-ledger.md`), every private predicate that restates `Turing.Segment` at fixed parameters, with its concatenation lemma. It records both members, the auditor's census (`Contract/Basic` 1 of 93, `Tautology` 1 of 93, `CounterLoop` 1 of 79, 2 of 79 with IW-1), the one-fifth rule (not reached), and the cleanup owner and window: the maintainer, in 12.2c, by bridges to `Turing.Segment` and `Segment.trans`/`mono`. The pack's erratum is in `resolutions.md`. #202 adds no member |
| 2 | **Fixed** (`evidence/screen-r2/`): the v3 screen on `git archive`s of the audited head `7b5774fb` and its base, the campaign's Lean at `bdc73ab1` (#196's merge). The population is the same 17 files at both, every campaign `.lean` file that mentions `Segment`, and all 17 are in this bundle at the head. The round-1 trees held `CfgRecord` from before #196 (blob `c82b5bc6` against `c840bc54`), which is why round 1 counted 1,339 |

## Brief for the auditor

1. **Finding 1:** does SG-1 describe the debt correctly, by kind, with its census and window?
2. **Finding 2:** does the screen on the audited trees reproduce, and does it show any new pair at
   the head?

## Repository-side attestations (verify or challenge)

- **Screen** (`evidence/screen-r2/`): @SCREEN98R2@
- Everything else is round 1's and unchanged: the seal and axioms (re-run on `oleans-lsi2`), the
  freeze, the names, the sweep, lint, and `replay-lsi2` (112 modules, 0 failed, the existing 45
  `sorry`s).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/98-segment-iterate-api/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `segment-iterate-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
