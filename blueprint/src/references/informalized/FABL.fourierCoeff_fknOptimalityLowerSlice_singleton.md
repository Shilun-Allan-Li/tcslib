<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierCoeff_fknOptimalityLowerSlice_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coefficient of a Centered Indicator

**Claim.** For every coordinate $i$, the Fourier coefficient of $x\mapsto 2\mathbf{1}_A(x)-1$ at the singleton frequency containing $i$ is twice the coefficient of the indicator of $A$ at that frequency.

**Proof.** In the coefficient expectation, distribute multiplication by the singleton monomial across $2\mathbf{1}_A-1$. Linearity of expectation yields twice the indicator coefficient minus the expectation of the singleton monomial. A nonempty monomial has expectation zero (`expect_monomial`), so only twice the indicator coefficient remains.

**Key facts.** `FABL.expect_monomial`.
