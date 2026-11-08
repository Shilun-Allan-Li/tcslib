<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_sq_sub_sq_le_three_quarters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Difference of Squares Estimate

**Claim.** If $0\le\varepsilon\le\tfrac12$, $|a|\le1$, and $|b-a|\le\varepsilon/4$, then $|b^2-a^2|\le3\varepsilon/4$.

**Proof.** First, $|2a|=2|a|\le2$. Write $b+a=(b-a)+2a$; the triangle inequality then gives $|b+a|\le|b-a|+|2a|\le\varepsilon/4+2\le3$, using $\varepsilon\le1/2$. Factor the difference of squares and take absolute values: $|b^2-a^2|=|b-a||b+a|$. The bounds on the two factors yield $|b^2-a^2|\le(\varepsilon/4)\cdot3=3\varepsilon/4$; the multiplication preserves the inequalities because the relevant factors are nonnegative.
