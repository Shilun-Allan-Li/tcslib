<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_half_fknOptimalityGaussianMain_lt_boundary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Main Term Below Boundary

**Claim.** For all sufficiently large integers $q$, half of $m_q\sqrt{2\log(1/m_q)}$ is strictly less than $b_q$, where $m_q$ is the prescribed Gaussian mass and $b_q$ is its Gaussian isoperimetric boundary value.

**Proof.** The Gaussian main term is positive for every $q$. The Gaussian boundary is asymptotic to this main term, so their ratio tends to $1$. It is therefore eventually greater than $1/2$. Multiplying this ratio inequality by the positive main term gives the asserted eventual strict inequality.

**Key facts.** `FABL.fknOptimalityGaussianBoundary_isEquivalent_main`, `FABL.fknOptimalityGaussianMain_pos`.
