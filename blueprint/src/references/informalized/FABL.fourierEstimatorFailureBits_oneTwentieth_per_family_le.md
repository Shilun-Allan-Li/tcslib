<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.fourierEstimatorFailureBits_oneTwentieth_per_family_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Family Failure-Bit Bound

**Claim.** For a nonempty finite family $\mathcal F$ and the one-twentieth confidence parameter divided by $|\mathcal F|$, the failure-bit count is at most $40|\mathcal F|$.

**Proof.** Nonemptiness gives $|\mathcal F|>0$, so the family-adjusted confidence parameter is $(1/20)/|\mathcal F|$. Consequently, twice its reciprocal is exactly the integer $40|\mathcal F|$, and taking the ceiling leaves that value unchanged. Finally, $40|\mathcal F|\le 2^{40|\mathcal F|}$; the ceiling base-$2$ logarithm of the left-hand integer is therefore at most the exponent $40|\mathcal F|$.
