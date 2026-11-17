<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedFiniteFamilyFourierEstimatorProgram_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Estimator Cost Bounds

**Claim.** If $|\mathcal F|\le M$, every supported outcome of the bounded-family estimator uses at most $Mm$ random examples, uses no queries, and has work at most $Mm(n+2)$, where $m$ is its sample count.

**Proof.** The exact cost formula for every supported outcome gives random-example cost $|\mathcal F|m$, query cost zero, and work $|\mathcal F|m+|\mathcal F|m(n+1)$. Multiplying $|\mathcal F|\le M$ by the nonnegative sample count $m$ bounds the random-example cost by $Mm$. The query claim follows directly from the formula. For the work bound, the same inequality bounds each of the two work terms, giving a total at most $Mm+Mm(n+1)=Mm(n+2)$.

**Key facts.** `FABL.boundedFiniteFamilyFourierEstimatorProgram_cost_eq`.
