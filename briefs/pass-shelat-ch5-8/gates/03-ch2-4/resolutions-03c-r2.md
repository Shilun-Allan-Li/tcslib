# Gate 03c (hard-core bits and PRGs): round 2 resolutions — gate closed

- **Round 2:** findings `findings/gate03c-r2-findings.md`, verbatim, SHA-256
  `838f4142f2c9e953fc75a61897e9b6be63c9936254e3524918f19ddc6dc0cacf`; pin
  `e79397eaf68b156b9db091f464741f6eb75b9c28`; bundle SHA-256 `c80dbec7…` (19 sections). Verdict
  **CLOSE: 0 blockers, 0 majors, 1 minor, 3 notes.** All round 1 rows are fixed or recorded; none
  is unresolved.
- **The gate closes** (0 blockers, 0 majors). The scheduled clean-up items (DL-9 onward) stay on
  the clean-up's record, not this gate's.

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | minor | **Fixed.** `resolutions-03c-r1.md`'s preamble now says it was a pre-merge snapshot and gives #201's merge (`02951926`) and that round 2's pin contains every fix. 03a's resolutions were updated the same way when #203 merged; 03b's and 03e's never claimed an unmerged state. |
| R2-2 | note | **No change** (G3-2's accepted cost: exact `2n` and `n²` are not `PRG` stretches; the declared routes are `PRG.truncate` and `DoublingPRG`). Downstream uses keep the qualification. |
| R2-3 | note | **No change** (G3-7 (c)'s accepted cost: `henc`). The per-index or bounded-length generalization of `glPad` stays unformalized and is not counted as delivered. |
| R2-4 | note | **No change.** The cross-gate dispositions (03b's `HardCore` definition, 03i's OWP prints, the PRF truncation implementations, `PublicKey.lean`) are attested by their own gates, not by this one. |
