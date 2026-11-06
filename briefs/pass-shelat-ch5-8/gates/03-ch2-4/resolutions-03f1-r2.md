# Gate 03f1: round 2 resolutions — gate closed

- **Round 2:** findings `findings/gate03f1-r2-findings.md`, verbatim, SHA-256 `948a80eac39f55984dc6c9000a63ad8ca657cbce81f010897ab24fd9278dc337`; pin
  `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; bundle `e5293af0…`. **CLOSE: 0 blockers, 0 majors,
  1 minor, 7 notes.** Round 1: #1, #3, M1, M2, M3 fixed; M4 recorded; #2 not resolved (R2-1).

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | minor | **Fixed** (records). `briefs/pass-shelat/inventory-ch2.md:445`, Claim-62.2's detailed entry, now reads "In `Candidates/Rabin.lean` (`rabin_symmetry`), audited at gate 03f2." With lines 194 and 517, all three occurrences are corrected; round 1 #2 is now fully fixed. |
| R2-2, R2-3 | note | **No change.** The headline sketch and the two sampler equations are confirmed. The fill brief keeps the order `statClose_rejectBlocksL` before `statClose_sampleBelowL` (`fills/dl-candidates/brief-draft.md`, Templates). |
| R2-4, R2-5, R2-6 | note | **No change.** |
| R2-7 | note | **Fixed** (evidence). The comparator read names up to the first apostrophe and merged `uprob_permGraph_eq_of_isomorphic'` into its unprimed namesake. Corrected count: 549 prints at the head, 539 at the base, 0 changed sets (`evidence-repairs/03-batch/ERRATUM.md`, with the fixed tool). |
| R2-8 | note | **Done before issue.** The dl fill brief uses the corrected headline sketch (dl-b) and the verified corollary order (dl-a). Its issue follows this closure. |
