<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgramForBound_queries_polynomial_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Learner Query Bound

**Claim.** Every outcome in the support of the bounded learner has query cost at most $2^{40}(n+1)^2(M+1)^8/\varepsilon^{10}$.

**Proof.** Split according to whether $M$ is positive. If it is, the bounded learner unfolds to the ordinary Kushilevitz–Mansour program, so its support outcomes satisfy the query bound for that program (`kushilevitzMansourProgram_queries_polynomial_cast_le`). If $M$ is not positive, then $M=0$ and the bounded learner returns the empty hypothesis without making queries. Its only supported outcome therefore has query cost zero, which satisfies the nonnegative stated bound.

**Key facts.** `FABL.kushilevitzMansourProgram_queries_polynomial_cast_le`.
