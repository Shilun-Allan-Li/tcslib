<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lowDegreeFourierEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact cost of the low-degree estimator

**Claim.** Every outcome in the support of the low-degree Fourier estimator’s output law has cost $(R,0,R+R(n+1))$, where $R$ is the learner’s random-example cost.

**Proof.** Apply the exact cost formula for a finite-family Fourier estimator to the family of all subsets of $[n]$ of size at most $k$. The low-degree family is nonempty, so it meets the formula’s hypothesis. Its random-example count is the family’s cardinality times the number of samples per coefficient, which is exactly $R$ by definition. The formula gives zero membership queries and work equal to that count plus that count multiplied by $n+1$; by definition, this is $R+R(n+1)$.

**Key facts.** `FABL.finiteFamilyFourierEstimatorProgram_cost_eq`, `FABL.lowDegreeFourierFamily_nonempty`.
