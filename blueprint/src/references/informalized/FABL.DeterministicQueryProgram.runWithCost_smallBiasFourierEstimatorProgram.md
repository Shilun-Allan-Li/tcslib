<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierEstimator.lean :: FABL.DeterministicQueryProgram.runWithCost_smallBiasFourierEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier estimator run and cost

**Claim.** Running the small-bias Fourier estimator program with oracle $f$ returns the sample average of $f(x)$ times the monomial indexed by $U$, together with its prescribed cost: zero random examples, $m$ membership queries, and $m(|U|+2)+1$ units of local work.

**Proof.** The program queries the oracle at all $m$ converted sample points. Its continuation forms the sum of each answer multiplied by the corresponding monomial and divides by $m$, which is the stated estimator. It then charges the estimator work. By definition, the batch contributes zero random examples, $m$ queries, and $m$ units of work; adding the continuation's work gives the prescribed total, with no further random examples or queries. Unfolding the run and cost definitions yields the asserted equality.
