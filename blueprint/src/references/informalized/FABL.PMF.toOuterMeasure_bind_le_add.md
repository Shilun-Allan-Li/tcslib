<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.PMF.toOuterMeasure_bind_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Stage Bad-Event Bound

**Claim.** If the first-stage sample lands in a bad set with probability at most $\delta_1$, and outside that set the conditional second-stage probability of its bad event is at most $\delta_2$, then the two-stage sample's probability of the final bad event is at most $\delta_1+\delta_2$.

**Proof.** The outer measure of the final bad event under the bound sampling law is the sum over first-stage outcomes $a$ of their weights times the conditional outer measure of the final bad event (`PMF.toOuterMeasure_bind_apply`). Bound each conditional term by the indicator of the first bad set plus $\delta_2$. When $a$ lies in the first bad set, the conditional probability is at most $1$, since outer measure is monotone and the whole space has probability one. When $a$ lies outside it, the indicator vanishes and the assumed conditional bound gives at most $\delta_2$. Summing these pointwise bounds, distribute multiplication over addition and split the nonnegative sum. The indicator contribution is exactly the first-stage probability of the bad set; the constant contribution sums to $\delta_2$, because the first-stage probabilities total one. The result is at most $\delta_1+\delta_2$ by the assumed first-stage bound.
