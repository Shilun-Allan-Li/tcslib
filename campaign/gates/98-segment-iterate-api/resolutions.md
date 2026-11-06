# Gate 98 (#202, `Turing.Segment.iterate_seq`): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (exchange inbox `arora-barak-ch3-4/inbox/segment-iterate-api-findings.md`,
SHA-256 `549259f210f2837e20d7d770b0f472edf48a07c8265544401bd2a6df8841590b`). **Does not close: 0
blockers, 1 major, 1 minor, 4 notes.** The new lemma, its statement, home and corollary are
verified (notes 3–6).

## Round 1 dispositions

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Acknowledged by kind (the user, 2026-11-06; for 12.2c).** The ledger's new family **SG-1**: every private predicate that restates `Turing.Segment` at fixed parameters, with its concatenation lemma. Its members are `Tautology`'s `tautDualSegment`/`tautDual_segment_add` and `CounterLoop`'s `counterSpan`/`counter_span_append`, both before #202, which adds none. The census is the auditor's: `Contract/Basic` 1 of 93 (the public `Segment.trans`, 20 lines), `Tautology` 1 of 93 (12 lines), `CounterLoop` 1 of 79 (28 lines; 4 of 79 in all, with IW-1's `counterPatch` and R8.0b E1's pair, corrected at round 2); no file past one fifth. **Cleanup owner and window:** the maintainer, in 12.2c, by a bridge from each predicate to `Turing.Segment` and `Segment.trans`/`mono` through it. **Erratum to the round-1 pack** (kept as dispatched): §5 said that all 23 pairs with a `Contract/Basic` declaration are inside the file's own layer; one is `Segment.trans` against `Tautology`'s `tautDual_segment_add` (54%), SG-1's first member. |
| 2 | minor | **Fixed** (`evidence/screen-r2/`): the screen re-run on `git archive`s of the audited head `7b5774fb` and its base, the campaign's Lean at `bdc73ab1`. The round-1 trees were taken before the campaign merge, so `CfgRecord` was #196's predecessor there: hence 1,339 against the auditor's 1,341. The population is the same 17 files at both (every campaign file mentioning `Segment`), and round 2's bundle carries all 17. |
| 3–6 | notes | Agreed. |

## Round 2 findings (received 2026-11-06)

`findings-r2.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/segment-iterate-api-r2-findings.md`,
exchange commit `481d4b0b07567fbe56284e299656c1dcd0679e4f`), SHA-256 `b3aec952fa631214c40183bc36af16b978cfd33c5bc233e2fcf73ee99158200a`.

**Verdict: CLOSE — 0 blockers, 0 majors, 1 minor, 4 notes.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Swept** (records only): SG-1's `CounterLoop` census now counts every acknowledged member once, `counter_span_append` (SG-1), `counterPatch` (IW-1) and R8.0b E1's `counterLoopTM`/`counterLoopTMVia`: **4 of 79 (5.1%)**, 68 lines; the round-1 disposition above is corrected. No threshold is crossed. |
| 2–5 | notes | Agreed. |

**Gate 98 CLOSED** (round 2, 2026-11-06). #202 is unchanged since `replay-lsi2`, which passed on the
merged tree (the campaign's Lean is still `bdc73ab1`'s).
