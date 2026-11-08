<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.variational_integral_mul_le_integral_klFun_add_cgf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variational Inequality for an Exponential Moment

**Claim.** Under the stated integrability, nonnegativity, and normalization assumptions, the tilted mean $t\int fX\,d\mu$ is bounded above by the integral of the relative-entropy integrand for $f$ plus the cumulant generating function of $X$.

**Proof.** Write $c=\Lambda(t)$. The pointwise inequality $u y\leq \mathrm{klFun}(u)+e^y-1$ for $u\geq0$, applied with $u=f(x)$ and $y=tX(x)-c$, bounds $f(x)(tX(x)-c)$ by $\mathrm{klFun}(f(x))+e^{tX(x)-c}-1$. The stated integrability assumptions, together with integrability of the exponentially tilted term ($\texttt{integrable\_exp\_sub\_cgf}$), make both sides integrable, so integrating preserves the inequality. On the left, linearity of the integral and $\int f\,d\mu=1$ give $t\int fX\,d\mu-c$. On the right, the tilted exponential integrates to $1$ ($\texttt{integral\_exp\_sub\_cgf\_eq\_one}$); because $\mu$ is a probability measure, the integral of the constant $1$ is also $1$. These two terms cancel, leaving precisely $\int\mathrm{klFun}(f)\,d\mu$. Rearranging proves the claim.

**Key facts.** `CommunicationComplexity.integrable_exp_sub_cgf`, `CommunicationComplexity.mul_le_klFun_add_exp_sub_one`, `CommunicationComplexity.integral_exp_sub_cgf_eq_one`.
