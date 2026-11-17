<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.fourierDegree_sub_mean_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree after mean subtraction

**Claim.** Subtracting the uniform mean of $f$ leaves its Fourier degree at most $k$, provided $f$ has Fourier degree at most $k$.

**Proof.** Take any set $S$ with $|S|>k$. It is nonempty. In the Fourier coefficient of $f-\mathbb{E}[f]$, distribute the product over the difference and split the expectation into two terms. The first is the Fourier coefficient of $f$, which is zero by the degree bound (`fourierDegree_le_iff`). In the second, the mean is constant in the cube variable, so it factors out; the expected monomial on the nonempty set $S$ is zero (`expect_monomial`). Hence this coefficient vanishes. The Fourier degree criterion now gives the claimed bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.expect_monomial`.
