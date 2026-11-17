<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/StableInfluences.lean :: FABL.const_hasSmallStableInfluences_zero_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Stable Influence of Constants

**Claim.** For every dimension and real constant, the constant function has stable influence at most zero at each coordinate when the noise parameter is one.

**Proof.** Fix a coordinate $i$. In the sum defining its stable influence, every indexing set $S$ contains $i$, so $S$ is nonempty. For such an $S$, the Fourier coefficient of the constant function is $c$ times the average of the monomial indexed by $S$. The average of a nonempty monomial is zero, by the monomial expectation formula (expect_monomial). Thus every summand is zero, and the stable influence is exactly zero; in particular, it is at most zero.

**Key facts.** `FABL.expect_monomial`.
