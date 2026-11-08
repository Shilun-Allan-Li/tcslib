<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.kushilevitzMansourProgramForBound_work_polynomial_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Learner Work Bound

**Claim.** Every outcome in the support of the bounded learner has work cost at most $2^{42}(n+1)^3(M+1)^8/\varepsilon^{10}$.

**Proof.** Split according to whether $M$ is positive. In the positive case, the bounded learner is the ordinary Kushilevitz–Mansour program, and its work bound (`kushilevitzMansourProgram_work_polynomial_cast_le`) gives the result for every supported outcome. In the other case, $M=0$, so the bounded learner returns the empty hypothesis directly. Its only supported outcome has work cost zero, which is at most the displayed bound.

**Key facts.** `FABL.kushilevitzMansourProgram_work_polynomial_cast_le`.
