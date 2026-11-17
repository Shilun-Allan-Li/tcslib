<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.taylor_charFun_two_of_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characteristic function expansion at zero

**Claim.** For a measurable-up-to-null-set real random variable with mean zero and finite second moment $q$, its characteristic function equals $1-qt^2/2+o(t^2)$ as $t\to0$.

**Proof.** View the pushforward of the probability measure under the random variable as the law of a real random variable with finite second moment. The second-order Taylor expansion of its characteristic function at zero has constant term $1$, linear term equal to $it$ times the mean, and quadratic term equal to $-t^2/2$ times the second moment. The mean-zero assumption removes the linear term, and the second-moment identity makes the quadratic term $-qt^2/2$. The Taylor remainder is little-$o(t^2)$, giving the claimed expansion.
