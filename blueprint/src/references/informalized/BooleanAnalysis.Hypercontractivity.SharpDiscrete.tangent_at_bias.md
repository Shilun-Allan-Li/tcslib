<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.tangent_at_bias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tangent identities at normalized bias

**Claim.** For $1<p<2$, $0<\alpha<\beta$, and $\alpha^p+\beta^p=1$, setting $t=(\beta-\alpha)/(\beta+\alpha)$ and $S=(1+t)^p+(1-t)^p$ gives $S^{2/p}=4/(\alpha+\beta)^2$ and $S^{2/p-1}\big((1+t)^{p-1}-(1-t)^{p-1}\big)/t=2(\beta^{p-1}-\alpha^{p-1})/(\beta-\alpha)$.

**Proof.** Set $c=2/(\alpha+\beta)$. Since $\alpha,\beta>0$ and $\alpha<\beta$, direct algebra gives $1+t=c\beta$ and $1-t=c\alpha$. Thus $S=(c\beta)^p+(c\alpha)^p=c^p(\beta^p+\alpha^p)=c^p$, using positivity to separate powers of products and the normalization. Consequently $S^{2/p}=(c^p)^{2/p}=c^2=4/(\alpha+\beta)^2$. For the second identity, the same substitutions turn the difference in its numerator into $c^{p-1}(\beta^{p-1}-\alpha^{p-1})$, while $t=(\beta-\alpha)/ (\beta+\alpha)$. The power factor and this difference combine as $(c^p)^{2/p-1}c^{p-1}=c$; dividing by $t$ then gives $c(\beta+\alpha)(\beta^{p-1}-\alpha^{p-1})/(\beta-\alpha)=2(\beta^{p-1}-\alpha^{p-1})/(\beta-\alpha)$.
