<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.centralBinomialRatio_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Central binomial ratio bound

**Claim.** For every natural number $j$, $\binom{2j}{j}/2^{2j}\le 1$.

**Proof.** The central binomial coefficient bound says that the central binomial coefficient $\binom{2j}{j}$ is at most half of the central binomial coefficient $\binom{2j}{j}\binom{2j}{j}$ as encoded by the central-binomial quantity, which is bounded by $4^j$ (Nat.centralBinom_le_four_pow together with Nat.centralBinom_eq_two_mul_choose). Thus $\binom{2j}{j}\le 4^j=2^{2j}$. Since the denominator is positive, division yields the asserted bound.

**Caveat.** The supplied proof uses the central-binomial bound and its conversion to a bound on the ordinary binomial coefficient; these upstream facts are not listed in the provided upstream field.
