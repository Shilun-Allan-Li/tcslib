<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Moments.lean :: BooleanAnalysis.GaussianSpace.invariance_polynomial_fourth_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment Bound by Coefficient Energy

**Claim.** For a degree-at-most-$k$ multilinear coefficient family evaluated on independent coordinates satisfying the stated fourth-order invariance moment conditions, its fourth moment is at most $9^k$ times the square of its coefficient energy.

**Proof.** Each coordinate is reasonable with parameter $9$, has finite fourth moment, and has zero first and third moments. The independent multilinear reasonability theorem (`independent_multilinear_reasonable`) therefore makes the polynomial evaluation reasonable with parameter $(\max(9,9))^k=9^k$. Its fourth-moment clause bounds the fourth moment by $9^k$ times the square of its second moment. The second-moment identity for independent centered, unit-variance coordinates (`MultilinearMoments.integral_eval_sq`) identifies that second moment with $\sum_S F(S)^2$. Substituting this identity gives the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.independent_multilinear_reasonable`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval_sq`.
