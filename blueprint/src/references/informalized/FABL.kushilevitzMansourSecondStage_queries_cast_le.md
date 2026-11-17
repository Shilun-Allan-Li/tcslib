<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourSecondStage_queries_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-stage query bound

**Claim.** Every supported output and cost pair from the second-stage program has query count at most $640C^4/\varepsilon^2$, where $C$ is the active cap at threshold $\varepsilon/(4M)$.

**Proof.** Apply the second-stage cost alternatives. In the zero-cost case the query count is zero, so the bound follows. Otherwise, there is a nonempty active family $\mathcal F$ within the cap $C$, and the outcome lies in the support of the finite-family Fourier estimator at accuracy $\varepsilon$ and confidence $1/20$. The estimator query bound gives at most $16|\mathcal F|^3 B/\varepsilon^2$, where $B$ is the failure-bit count at the family-adjusted confidence. The one-twentieth failure-bit estimate bounds $B$ by $40|\mathcal F|$. Thus the query count is at most $640|\mathcal F|^4/\varepsilon^2$. Since $|\mathcal F|\le C$, this is at most $640C^4/\varepsilon^2$.

**Key facts.** `FABL.kushilevitzMansourSecondStage_cost_cases`, `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_cast_le`, `FABL.fourierEstimatorFailureBits_oneTwentieth_per_family_le`.
