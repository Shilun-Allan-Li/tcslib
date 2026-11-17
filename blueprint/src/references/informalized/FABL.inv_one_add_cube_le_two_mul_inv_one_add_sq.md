<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.inv_one_add_cube_le_two_mul_inv_one_add_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of reciprocal polynomial tails

**Claim.** For every $t\ge0$, $(1+t^3)^{-1}\le 2(1+t^2)^{-1}$.

**Proof.** Both denominators are positive. We show $1+t^2\le2(1+t^3)$ by splitting into two ranges. If $t\le1$, then $t^2\le1$, so $1+t^2\le2\le2(1+t^3)$. If $t>1$, then $t\ge1$ and $t^3\ge t^2$, which gives $1+t^2\le1+t^3\le2(1+t^3)$. Dividing by the positive product of the denominators gives the claimed reciprocal inequality.
