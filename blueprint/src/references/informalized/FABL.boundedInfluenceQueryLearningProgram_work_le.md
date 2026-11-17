<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.boundedInfluenceQueryLearningProgram_work_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Bound for Bounded Influence Learning

**Claim.** Every outcome in the support of the bounded-influence query-learning program has work cost at most $2^{42}(n+1)^3(B+1)^8/\epsilon^{10}$, where $B$ is its family bound.

**Proof.** The bounded-influence program is the Kushilevitz–Mansour program for accuracy $\epsilon$ and budget $B$. Thus every supported outcome falls under the budgeted program's work estimate, which bounds its work component by $2^{42}(n+1)^3(M+1)^8/\epsilon^{10}$ (`kushilevitzMansourProgramForBound_work_polynomial_cast_le`). Taking $M=B$ yields the stated inequality.

**Key facts.** `FABL.kushilevitzMansourProgramForBound_work_polynomial_cast_le`.
