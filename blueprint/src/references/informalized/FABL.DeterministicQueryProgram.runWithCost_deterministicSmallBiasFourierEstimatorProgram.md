<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicSmallBiasFourierEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic estimator run and cost

**Claim.** Running the deterministic small-bias Fourier estimator with oracle $f$ returns the sample average of $f(x)$ times the monomial indexed by $U$, together with its prescribed cost: zero random examples and membership queries, and work equal to the deterministic construction work plus the estimator work.

**Proof.** Unfolding the program, the outer computation first charges the deterministic construction work and then runs the Fourier estimator. That estimator queries the oracle at each converted sample point, uses those answers in the displayed sample average, and charges its prescribed estimator work. The two charges add componentwise, giving exactly the stated cost; these are precisely the definitions of the run, the program, the estimate, and the cost, so the equality is definitional.
