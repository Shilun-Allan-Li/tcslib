<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.isFourierSpectrumConcentratedUpTo_zero_of_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Functions Have No Nonconstant Fourier Weight

**Claim.** If a Boolean function on the sign cube is constant, then for every $\epsilon\ge 0$ the sum of its squared Fourier coefficients over nonempty coordinate sets is at most $\epsilon$.

**Proof.** Every set in the sum has positive cardinality, hence is nonempty. Constancy means the real-valued function is the same constant everywhere. Its Fourier coefficient at such a set therefore factors as that constant times the expectation of the corresponding monomial. The expectation of a monomial indexed by a nonempty set is zero (\(\texttt{FABL.expect\_monomial}\)), so every summand vanishes. The sum is zero, which is at most $\epsilon$.

**Key facts.** `FABL.expect_monomial`.
