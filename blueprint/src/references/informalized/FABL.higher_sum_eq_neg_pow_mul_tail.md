<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.higher_sum_eq_neg_pow_mul_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Higher Coefficient Sum and Tail Identity

**Claim.** The sum of the even-moment coefficient gaps times $t^{2l}$ over $j<l\le r$ is $-t^{2j}$ times the higher even-moment coefficient tail at $t$.

**Proof.** Expand the tail as a sum over the same indices $l$ with $j<l\le r$. Multiplying by $-t^{2j}$ moves that factor into each summand and cancels the minus sign in the tail's definition. For each such $l$, the powers combine as $t^{2j}t^{2l-2j}=t^{2l}$, since $2j+(2l-2j)=2l$. The remaining summands are exactly the stated coefficient-gap sum.
