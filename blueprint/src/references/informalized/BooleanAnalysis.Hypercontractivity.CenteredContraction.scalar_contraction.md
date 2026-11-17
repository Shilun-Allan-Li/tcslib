<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Reflected scalar contraction

**Claim.** For every $q\ge2$, there is a constant $c$ with $0<c\le1$ satisfying the reflected scalar contraction inequality for every real $x$, and when $q=4$ it can be chosen as $2/5$.

**Proof.** Separate the case $q=4$. Choose $c=2/5$. Since the exponent is the integer $4$, the absolute-value fourth powers are ordinary fourth powers; expanding both sides and simplifying reduces the inequality to a nonnegative polynomial expression, verified by writing it as a sum of squares. For $q\ne4$, use the generic existence theorem for scalar contraction (`scalar_contraction_generic`), which supplies a positive $c\le1$ and the required inequality for all real $x$. The condition specifying $c=2/5$ when $q=4$ holds vacuously in this second case.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_contraction_generic`.

**Caveat.** The supplied proof for $q=4$ only indicates that nonlinear arithmetic proves the polynomial inequality, without exposing its factorization or intermediate algebra; the claimed sum-of-squares verification is therefore not displayed.
