<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.evenMajorityTotalInfluenceError_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even majority influence error bound

**Claim.** The even-majority total influence error is $O(n^{-1/2})$ along even arities $n=2m+2$.

**Proof.** Use the pointwise estimate that the absolute error is at most $4/\sqrt{2m+2}$ (`abs_evenMajorityTotalInfluenceError_le`). The comparison sequence $(2m+2)^{-1/2}$ is positive, and the negative-half-power identity `evenArity_rpow_neg_one_half` rewrites it as the reciprocal square root. Thus the error is bounded by four times the comparison sequence for every $m$, which is exactly the asserted big-$O$ estimate.

**Key facts.** `FABL.abs_evenMajorityTotalInfluenceError_le`, `FABL.evenArity_rpow_neg_one_half`.
