<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.scheduledLowDegreeF₂PolynomialLearnerWorkWithBackend_le_exponentEnvelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backend Work Exponent Envelope

**Claim.** Under the backend exponent certificate, the scheduled learner's work is bounded by its stated coefficient times $(n+1)^{\lceil\omega\ell\rceil}$.

**Proof.** Set $d=\ell+1$, $r=2^\ell(\ell+b(\delta)+1)$, $B=n+1$, and $P=B^\ell$. Since $B>0$, we have $1\le P$. The monomial-count bound gives at most $dP$ variables, and the sample-count bound gives at most $rP$ samples. The learner's rows are indexed by those samples, so their number is also at most $rP$. The backend certificate therefore bounds solver work by $c(d,r,\ell)B^{\lceil\omega\ell\rceil}$. Also the learner's sample-processing cost is the sample count times the monomial count plus one; these two factors are bounded by $rP$ and $(d+1)P$, respectively. Because $\omega\ge2$, the exponent $\lceil\omega\ell\rceil$ is at least $2\ell$, so $P^2=B^{2\ell}\le B^{\lceil\omega\ell\rceil}$. Thus the processing cost is at most $r(d+1)B^{\lceil\omega\ell\rceil}$. Adding this to the solver bound yields coefficient $r(d+1)+c(d,r,\ell)$, as claimed.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`, `FABL.lowDegreeF₂LearningSampleCount_le_exponentScale`.
