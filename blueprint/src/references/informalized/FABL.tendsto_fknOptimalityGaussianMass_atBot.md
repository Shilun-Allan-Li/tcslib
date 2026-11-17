<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.tendsto_fknOptimalityGaussianMass_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Mass Tends to the Lower Endpoint

**Claim.** As $q\to\infty$, the selected Gaussian mass $1/(q+2)$ tends to zero in the order topology on $(0,1)$.

**Proof.** The real-valued mass tends to zero (`tendsto_fknOptimalityGaussianMass_zero`), and every selected mass is strictly positive. These two facts imply convergence to the lower endpoint in the interval $(0,1)$: every relative neighborhood of that endpoint contains all sufficiently small positive masses. Thus the sequence tends to the interval's bottom filter.

**Key facts.** `FABL.tendsto_fknOptimalityGaussianMass_zero`.
