<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedInfluenceQueryLearningProgram_queries_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Bound for Bounded Influence Learning

**Claim.** Every outcome in the support of the bounded-influence query-learning program has query cost at most $2^{40}(n+1)^2(B+1)^8/\epsilon^{10}$, where $B$ is its family bound.

**Proof.** The bounded-influence learning program is the Kushilevitz–Mansour program for the same accuracy parameter and with budget equal to the family bound $B$. Its supported outcomes are therefore supported outcomes of that budgeted program. The general query-cost estimate for the budgeted program bounds the query component of every such outcome by $2^{40}(n+1)^2(M+1)^8/\epsilon^{10}$ (`kushilevitzMansourProgramForBound_queries_polynomial_cast_le`). Substituting $M=B$ gives the claimed bound.

**Key facts.** `FABL.kushilevitzMansourProgramForBound_queries_polynomial_cast_le`.
