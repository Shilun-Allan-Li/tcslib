<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.criticalProbability_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Probability Lies in the Unit Interval

**Claim.** The critical probability of a monotone nonconstant Boolean function lies strictly between $0$ and $1$.

**Proof.** By the existence-and-uniqueness theorem, there is a unique $p$ in $(0,1)$ satisfying the defining probability equation. The critical probability is chosen to be that value, so it inherits the interval membership from the first component of the theorem’s existence statement.

**Key facts.** `FABL.existsUnique_criticalProbability`.
