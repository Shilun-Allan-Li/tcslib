# sc-yao · maintainer addendum after #327 and #324 merged

The review (`review.md`) was written against the tip `f9fda8fe`, before #327 and #324 merged. Seyoon merged #327
(`7d532e20`) and then #324 (`201bf57a`) while the review finished. This addendum records what changes for the landing
of `land/pass-shelat-sc-yao` at `e9b03c437aca251846430ff23b40ee5ff3d3347a`. It is the maintainer's static check only.

## Merge with the new tip
- `git merge-tree --write-tree` of the records tip and the landing head is clean (tree `67b8311a`).
- No file overlap: sc-yao's 70 changed files and the files #327/#324 changed are disjoint.
- No name clash. Three short names occur on both sides, each in a different namespace:
  - `encodeMsgs_eq_encWords`: `SequentialZK` (#327) and `SecureComputation.YaoHybridProof` (sc-yao);
  - `exists_simulator`: `SecureComputation.ComposeSim` (#324) and `YaoHybridProof.FakeSimulatorFactory`;
  - `length_answersB`: `SecureComputation.HybridProtocol` (#324) and `YaoHybridProof.OTAnswerWords`.
- Expected effect: with #324's `HybridProtocol.hbcSecure_compose` proved, `yaoProtocol_hbcSecure` should use only the
  standard axioms once sc-yao lands. The integration build on the new tip checks this; it is a merge condition.

## Duplication (extends SY-F03 and SY-F05)
- **SY-F03, extended:** `YaoHybridProof.encodeMsgs_eq_encWords` is now a verbatim copy, statement and proof, of the public
  `SequentialZK.encodeMsgs_eq_encWords` (`Composability/SequentialZK/Normalization.lean:40`, from #327). The #327 copy is
  itself in the DL-49 class (`ColMachines.encodeMsgs_eq_flatMap` with `BinArith.encWords_def`) and is not on the ledger.
  Re-pointing sc-yao's `Lengths` at it would import `SequentialZK/Normalization` into a Yao helper. The recommendation
  stays a ledger row (extend DL-49 with both copies), with a promotion of one `encodeMsgs_eq_encWords` to a common home
  in the post-merge cleanup.
- **SY-F05, remainder:** `OTAnswerWords.length_answersB` is the `otFunctionality` instance of the now public
  `HybridProtocol.length_answersB` (`ComposeSecurity/Lengths.lean:60`), with `outB = 1`; `answersA_nil` is the
  analogous instance of `length_answersA`. The review planned a ledger row until #324 lands; it has landed, so the pair
  goes to the post-merge cleanup (re-point after sc-yao merges), and the ledger row stands until then.

Neither item changes the landing branch.
