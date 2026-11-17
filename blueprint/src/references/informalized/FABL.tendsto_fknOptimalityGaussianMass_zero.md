<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.tendsto_fknOptimalityGaussianMass_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Gaussian mass parameter

**Claim.** For each natural number $q$, the mass parameter $m_q=1/(q+2)$ tends to $0$ as $q$ tends to infinity.

**Proof.** The natural numbers $q+2$ tend to infinity, since adding a fixed natural number preserves divergence to positive infinity. Taking reciprocals therefore gives $1/(q+2)\to 0$. This is exactly the sequence defining the Gaussian mass parameter.
