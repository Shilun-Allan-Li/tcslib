<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Depth Moment Bound

**Claim.** If every failure probability $\Pr[\operatorname{DT}(f_{J\mid z})\ge k]$ is at most $(1/4)^k$, then the random-restriction average of $2^{\operatorname{DT}(f_{J\mid z})}$ is at most $2$.

**Proof.** Express the average of the exponential depth as $1+\sum_{j=0}^{n-1}2^j\Pr[\operatorname{DT}(f_{J\mid z})\ge j+1]$ using the depth-moment identity (`expect_two_pow_restrictedDecisionTreeDepth_eq_failureSum`). Apply the assumed tail bound term by term. The identity $2^j(1/4)^{j+1}=(1/4)(1/2)^j$ (`two_pow_mul_quarter_pow_succ`) then bounds the sum by $(1/4)$ times a finite geometric sum, which is at most $(1/4)2$. Hence the expectation is at most $1+1/2\le2$.

**Key facts.** `FABL.expect_two_pow_restrictedDecisionTreeDepth_eq_failureSum`, `FABL.two_pow_mul_quarter_pow_succ`.

**Caveat.** The supplied informal statement describes a different switching-lemma conclusion. This account follows the formal statement and proof source, which establish only the exponential depth moment bound.
