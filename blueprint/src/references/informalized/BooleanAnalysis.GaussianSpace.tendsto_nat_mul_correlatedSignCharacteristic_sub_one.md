<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BlockCharacteristic.lean :: BooleanAnalysis.GaussianSpace.tendsto_nat_mul_correlatedSignCharacteristic_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-order correlated sign limit

**Claim.** For all real $\rho,a,b$, as $m\to\infty$ through positive integers, $m\bigl(C_\rho(a/\sqrt m,b/\sqrt m)-1\bigr)$ converges to $-\tfrac12(a^2+b^2+2\rho ab)$.

**Proof.** Apply the cosine limit under square-root scaling to $a+b$ and multiply its sequence and limit by $(1+\rho)/2$. Apply it again to $a-b$, multiplying by $(1-\rho)/2$. The sum of these two convergent sequences converges to the sum of their limits. The addition and subtraction identities $((a+b)/\sqrt m)=(a/\sqrt m)+(b/\sqrt m)$ and $((a-b)/\sqrt m)=(a/\sqrt m)-(b/\sqrt m)$ identify the sequence with the claimed one. Finally, expanding the two weighted squares gives $\frac{1+\rho}{2}(a+b)^2+\frac{1-\rho}{2}(a-b)^2=a^2+b^2+2\rho ab$, yielding the stated limit.

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_nat_mul_cos_div_sqrt_sub_one`.
