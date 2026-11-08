<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.one_div_learningConsequencesThreshold_sq_le_expression -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Learning Threshold Bound

**Claim.** Under the stated regime assumptions, the square of the inverse learning threshold is bounded by the displayed rational expression involving $C$, $Q$, and $\sqrt{\lceil\log_2(n+1)\rceil}+1$.

**Proof.** Set $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$, let $A$ be the degree coefficient, let $R_0=(8(C+1)(Q+1))^4$, and write $k$ for the learning degree. Then $s\ge1$, the degree estimate gives $k\le As$ (`FABL.learningConsequencesDegree_le_subsqrt`), and the influence assumption gives $t\le(C+1)s$. Also, the accuracy lower bound implies $1/(8(Q+1))\le\varepsilon/8$, and the internal error $\varepsilon/8$ is positive (`FABL.learningConsequencesInternalError_pos`).

Expanding the definition of the threshold and using positivity to invert its factors identifies the square of its reciprocal with $t^4/(\varepsilon/8)^4\cdot 9^{2k}$. Bound the numerator using $t\le(C+1)s$, bound the denominator below using $1/(8(Q+1))\le\varepsilon/8$, and bound the exponential factor using $k\le As$ and $9>1$. The resulting expression is $((C+1)s)^4(8(Q+1))^4 9^{2As}$, which rearranges to $R_0s^4 9^{2As}$. Replacing the temporary notation by its definitions gives the claimed bound.

**Key facts.** `FABL.learningConsequencesDegree_le_subsqrt`, `FABL.learningConsequencesInternalError_pos`.
