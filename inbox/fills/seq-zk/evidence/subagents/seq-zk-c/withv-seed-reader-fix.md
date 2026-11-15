# Explicit withV seed conversion for Rule10

This is future work after the lead confirmed exact copying of all159 closed CP3 evidence
files (manifest7d61325022177713394c14c876e926d81e6d430db5b2bfb066c71d1ad64bb971).
No old checkpoint source or frozen reader was edited. The change is solely within c-owned
ContinuationProbability.continuationProb_real; ComputationalHybrid is rechecked unchanged.

## Why the native proof needed a reader-based refinement

The earlier native proof supplied a bare pair with types pi.P.Coins and W.Coins to the
actual pi.withV(W) execution coin space. Lean's ordinary transparency accepted this by
reducing the FOREIGN Protocol.withV implementation to read its P/V fields. That implicit
seed-type conversion can fail when withV is opaque in the Rule10 counterfactual seal.
The mathematical theorem and probability law were valid, but the implementation access
was less explicit than the public-reader discipline requires. c flagged this precise leaf;
the lead authorized and specified the reader-built replacement after copying CP3 evidence.

## Replacement

- eP maps original prover coins to actual withV-prover coins using Equiv.arrowCongr and
  finCongr on the scalar coinLen equality proved ONLY from Protocol.withV_P.
- eV is the inverse of the published Protocol.withV_vCoinsEquiv. Their product e maps
  the independent original prover/wrapper tapes into the ACTUAL execution seed space.
- List.ofFn_congr proves the prover-word equality. Public withV_vCoinsEquiv_ofFn and
  Equiv.apply_symm_apply prove the verifier-word equality.
- Protocol.viewV_withV reads the actual raw view at e(a,v), using both word equalities.
  The shared normalizePhaseMsgs_viewV is applied at this correctly typed actual seed.
- Public acceptProb_comp_equiv e reindexes the actual raw-view law before the generic
  unused-factor averaging removes the wrapper's verifier tape.

No bare original pair is implicitly converted to a withV execution seed. All public
theorem and definition statements are byte-identical to the previous checked source;
withv-seed-fix-public-statements.json independently compares every public signature.
No new public declaration, assumption, helper host, frozen-file edit or reader request.
The existing pointwise normalization proof is reused, not duplicated or weakened.

Native attempts05 (ContinuationProbability) and03 (ComputationalHybrid) use the same
shared wrapper, seq-zk-c tag, own olean tree, and complete raw-log/source-snapshot pattern.
Their closed results and final hashes are in the corresponding results JSONL files.

Closed validation: ContinuationProbability native05 passed0diagnostics,2.64s actual,
maxRSS2,248,294,400bytes; final SHA4b7b7ad15dcd6ead93532c83dfe9e2b1f9750e2d5933ae359949bd7b4475db9a,
354lines/max94columns. ComputationalHybrid native03 passed0diagnostics,2.28s,
maxRSS2,231,222,272bytes; its source remains byte-identical at07e9f3beeaca0c2d2c4d5aa4e166cda4833412ad6b9bf5b5aba62aa888fa9bb1.
A second source comparison verified ALL text outside continuationProb_real's proof is
identical to the prior checked snapshot, not only the11 public statements. Final source
hashes/API status sent to lead and b; no own live Lean process remains.
