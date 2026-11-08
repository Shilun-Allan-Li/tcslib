<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.half_integral_abs_sub_one_sq_le_integral_klFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An $L^1$ bound by relative entropy

**Claim.** For a probability measure and a nonnegative density $f$ of integral one, the squared $L^1$ distance of $f$ from $1$, divided by two, is at most the integral of its pointwise Kullback–Leibler function.

**Proof.** Define $s(x)=1$ when $f(x)-1\ge 0$ and $s(x)=-1$ otherwise, let $m=\int s\,d\mu$, and set $X=s-m$. The sign function is measurable and bounded, so it is integrable; hence $X$ is measurable, bounded, and has mean zero. The bounded, centered-variable sub-Gaussian estimate (Hoeffding's lemma, applied through `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) therefore gives a cumulant generating function bound. Write $L=\int |f-1|\,d\mu$. Since $\int(f-1)\,d\mu=0$ and $(f-1)s=|f-1|$ pointwise, expanding $fX=f(s-m)$ and integrating shows that $\int fX\,d\mu=L$: the terms involving $m$ vanish by centering and the normalization of $f$. The variational inequality for relative entropy, applied with $X$ and parameter $t=L$, gives $L^2\le \int\mathrm{kl}(f)\,d\mu+\operatorname{cgf}_\mu(X,L)$. The sub-Gaussian estimate bounds the last term by $L^2/2$. Rearranging yields the claimed inequality.

**Key facts.** `CommunicationComplexity.variational_integral_mul_le_integral_klFun_add_cgf`.
