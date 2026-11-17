<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.two_mul_exp_neg_five_halves_mul_le_four_pow_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound by an Inverse Power

**Claim.** For every positive natural number $n$, $2\exp(-5n/2)\leq 1/4^n$.

**Proof.** First establish $\exp(5/2)>8$. The estimates $8/3<\exp(1)$ and $3/2<\exp(1/2)$ imply this: squaring the first gives $64/9<\exp(2)$, and multiplying by the second gives $8<\exp(5/2)$. Raising that bound to the $n$th power gives $8^n\leq\exp(5n/2)$. Since $n\geq1$, $2n+1\leq3n$, and therefore $2^{2n+1}\leq2^{3n}=8^n\leq\exp(5n/2)$. Divide by the positive quantities $\exp(5n/2)$ and $4^n$; using $2\cdot4^n=2^{2n+1}$ yields the desired inequality.
