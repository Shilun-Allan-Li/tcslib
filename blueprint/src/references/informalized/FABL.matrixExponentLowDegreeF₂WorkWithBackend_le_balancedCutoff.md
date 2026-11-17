<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Learner Work Bound

**Claim.** Under the stated solver certificate and parameter hypotheses, the backend polynomial learner's work on the specified sample is at most its stated coefficient times $(n+1)^c$, where $c=\lceil\omega k/(\omega+1)\rceil$.

**Proof.** Set $\ell=k-c$. The scheduled learner work bound gives work at most the specified backend coefficient for degree $\ell$ times $(n+1)^{\lceil\omega\ell\rceil}$. The solver-exponent cutoff bound says $\lceil\omega(k-c)\rceil\le c$. Since $n+1\ge1$, increasing the exponent from $\lceil\omega\ell\rceil$ to $c$ can only increase this power. Multiplying that inequality by the nonnegative coefficient and combining it with the scheduled work bound yields the claim.

**Key facts.** `FABL.scheduledLowDegreeF₂PolynomialLearnerWorkWithBackend_le_exponentEnvelope`, `FABL.matrixExponentJuntaCeilSolverExponent_le_cutoff`.
