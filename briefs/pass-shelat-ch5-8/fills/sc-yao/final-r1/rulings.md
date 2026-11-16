# sc-yao · Seyoon's rulings (2026-11-16)

These rulings were made after the review (`review.md`) and the post-merge addendum. No ruling changes the landing
branch (#341 at `e9b03c437aca251846430ff23b40ee5ff3d3347a`).

| Finding | Ruling |
|---|---|
| SY-F01 | **Confirmed.** The four helper imports outside the issued order (`ZeroKnowledge/ThreeColoring/Machines`, `PrivateKey/FromPRF/ReductionMachine`, `PrivateKey/FromPRF/HybridLemmas`, `Asymptotic/BlockEncryptor`) are approved, as in the worker's session. |
| SY-F02 | **Ledger, then promote:** ledger row DL-51. In the post-merge cleanup, `statClose_of_uprob_ne` moves to `Asymptotic/Sampling` and both users are re-pointed. |
| SY-F03 | **Ledger both, promote later:** DL-49 is extended with sc-yao's `YaoHybridProof.encodeMsgs_eq_encWords` and #327's `SequentialZK.encodeMsgs_eq_encWords`. In the post-merge cleanup, one copy goes to a common home and the rest are re-pointed. |

Still open: SY-F05's remaining pair, `OTAnswerWords.length_answersB` and `answersA_nil` against the now public
`HybridProtocol.length_answersB` and `length_answersA` (#324). The review proposed a ledger row; it waits for Seyoon's
acknowledgement and would be re-pointed after #341 merges.
