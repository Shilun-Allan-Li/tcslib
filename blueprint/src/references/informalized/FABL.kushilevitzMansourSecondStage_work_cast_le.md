<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourSecondStage_work_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-stage work bound

**Claim.** Every supported output and cost pair from the second-stage program has local work at most $1280C^4(n+1)/\varepsilon^2$, where $C$ is the active cap at threshold $\varepsilon/(4M)$.

**Proof.** Use the second-stage cost alternatives. If the cost is zero, the work bound is immediate. In the other case, a nonempty active family $\mathcal F$ is within the cap $C$, and the outcome is supported by the finite-family Fourier estimator at accuracy $\varepsilon$ and confidence $1/20$. Its work bound is $32|\mathcal F|^3(n+1)B/\varepsilon^2$, where $B$ is the failure-bit count at the family-adjusted confidence. The one-twentieth failure-bit estimate gives $B\le40|\mathcal F|$, so the work is at most $1280|\mathcal F|^4(n+1)/\varepsilon^2$. Using $|\mathcal F|\le C$ yields the stated bound.

**Key facts.** `FABL.kushilevitzMansourSecondStage_cost_cases`, `FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_cast_le`, `FABL.fourierEstimatorFailureBits_oneTwentieth_per_family_le`.
