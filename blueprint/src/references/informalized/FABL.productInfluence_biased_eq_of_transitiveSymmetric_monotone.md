<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productInfluence_biased_eq_of_transitiveSymmetric_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Transitive Coordinate Influences

**Claim.** For a monotone Boolean function with transitive symmetry, every coordinate has the same product influence under the biased sign distribution.

**Proof.** Fix coordinates $i$ and $j$. The influence at any coordinate $k$ is, by the monotone influence formula, the variance scale $\mathrm{biasSigma}(p)$ times the singleton biased Fourier coefficient at $k$ (`productInfluence_biased_eq_sigma_mul_singletonCoeff_of_monotone`). Applying this formula at $i$ and $j$ reduces the desired equality to equality of their singleton coefficients. Transitive symmetry gives that equality (`biasedFourierCoeff_singleton_eq_of_transitiveSymmetric`); multiplying both sides by the same variance scale proves the result.

**Key facts.** `FABL.productInfluence_biased_eq_sigma_mul_singletonCoeff_of_monotone`, `FABL.biasedFourierCoeff_singleton_eq_of_transitiveSymmetric`.
