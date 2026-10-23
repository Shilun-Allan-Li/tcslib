| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `spaceused-api-bundle(1).md` · bundle identity | The supplied attachment is the round-1 bundle; it cannot establish closure of the round-2 gate. | SHA-256 is `2dca34f9ca5d75e387133062f7f08786db44a11b0d2ab3784899520ab2a3a155`, whereas the requested hash is `f753f518057b49e5711b00cacfc5d7be69ca53a1c9aaefdc972a9ad4d88d6995`. It contains 56 file sections, not 69. Its first section is `campaign/gates/62-spaceused-api/pack.md`, identifying head `097f3e04`; neither `pack-r2.md` nor `3d0f80b5` occurs. | Supply `spaceused-api-r2-bundle.md` matching the requested hash and 69 sections, then rerun the round-2 audit. |
| 2 | note | Round-2 brief, resolutions and repository-side attestations | The substantive round-2 review remains unperformed; this verdict concerns the supplied evidence, not the truth of the two public lemmas. | Without the requested round-2 pack and snapshot, its questions and attestations cannot be verified, including the claimed replacement of `wr_space` by the public radius lemma and the correction of the minor records finding. No repository was modified. | Reassess every round-2 question and attestation against the corrected bundle. |

FAIL — 0 blockers, 1 major, 0 minors, 1 note.

