# Gate 03l: round 3 resolutions — gate closed

- **Round 3:** findings `findings/gate03l-r3-findings.md`, verbatim, SHA-256 `8f665b10000e8dac89418c265cd100133d960adf084b85000ed7b85ba528629d`; pin
  `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; bundle `7c32686f…`. **CLOSE: 0 blockers, 0 majors,
  2 minors, 16 notes.** Round 2: 1–4 fixed. Host contract H14 meets its closing threshold.

| Finding | Severity | Resolution |
|---|---|---|
| 1 | minor | **Confirmed; scheduled** (clean-up part 2, item L). `Clean.envelope`'s docstring will say the theorem deliberately publishes the coarse time-derived bound and exposes no module-specific envelope; the factor-two bound `⌊B/2⌋` that the contract implies is noted, not published. |
| 2 | minor | **Fixed** (evidence). The statement extractor stopped at any following line starting with `|`; it now stops only at a match arm. Regenerated over the batch's 21 files: the same 12 rows, and only `Clean.envelope`'s text changes, now with its full conclusion (`evidence-repairs/03-batch/ERRATUM.md`, `decls-fixed.tsv`). The fixed extractor is in the maintainer's tool set. |
| 3–18 | note | **No change.** |
