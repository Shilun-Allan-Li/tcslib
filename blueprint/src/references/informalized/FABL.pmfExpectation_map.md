<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under a mapped distribution

**Claim.** For finite sets $\Omega$ and $\Lambda$, the expectation of $f$ under the distribution obtained by mapping $p$ through $g$ equals the expectation of $f\circ g$ under $p$.

**Proof.** On finite spaces, expectation under a probability mass function agrees with integration against its associated measure (`FABL.pmfExpectation_eq_integral`). The measure associated to the mapped distribution is the pushforward of the original measure. The change-of-variables formula for integration against a pushforward therefore gives the integral of $f\circ g$ under the original measure, which is precisely the asserted expectation.

**Key facts.** `FABL.pmfExpectation_eq_integral`.
