<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BlockCharacteristic.lean :: BooleanAnalysis.GaussianSpace.tendsto_nat_mul_cos_div_sqrt_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cosine limit under square-root scaling

**Claim.** For every real $a$, the sequence $m\bigl(\cos(a/\sqrt m)-1\bigr)$ converges to $-a^2/2$ as $m\to\infty$.

**Proof.** First, $a/(2\sqrt m)$ tends to zero, since $1/\sqrt m$ tends to zero and multiplication by $a/2$ preserves convergence. Continuity of the sinc function at zero then gives $\operatorname{sinc}(a/(2\sqrt m))\to 1$, and therefore its square also tends to $1$. For positive $m$, use the identity $\cos t-1=-(t^2/2)\operatorname{sinc}(t/2)^2$ with $t=a/\sqrt m$. Multiplying by $m$ and simplifying $m(a/\sqrt m)^2=a^2$ gives $m(\cos(a/\sqrt m)-1)=-(a^2/2)\operatorname{sinc}(a/(2\sqrt m))^2$. The right-hand side converges to $-a^2/2$. Since the indices with $m>0$ form an eventual set, this establishes the limit of the full sequence.

**Key facts.** `BooleanAnalysis.GaussianSpace.cos_sub_one_eq_sinc`.
