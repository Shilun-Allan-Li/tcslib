<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.mean_discreteDerivative_eq_fourierCoeff_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Derivative and Singleton Coefficient

**Claim.** For any real-valued function on the sign cube and any coordinate $i$, the mean of its discrete derivative in coordinate $i$ equals its Fourier coefficient at the singleton set $\{i\}$.

**Proof.** Expand the discrete derivative as a sum over frequency sets containing $i$: the summand for a set $S$ is its Fourier coefficient times the monomial on $S$ with $i$ removed (FABL.discreteDerivative_eq_fourier_sum). Averaging this finite sum term by term, the monomial expectation is zero unless its index set is empty, in which case it is one (FABL.expect_monomial). Thus only the term with $S\setminus\{i\}=\varnothing$ survives. Among sets containing $i$, this forces $S=\{i\}$, and its contribution is precisely the Fourier coefficient at $\{i\}$.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.expect_monomial`.
