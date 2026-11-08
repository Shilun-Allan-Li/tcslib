<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Concentration.lean :: BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_concentration_optimized_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled Optimized Moment Identity

**Claim.** For $k>0$ and $\lambda,t>0$, if $q=\lambda t^{2/k}/e$, then $\left(\frac{(\sqrt q\,\lambda^{1/q-1/2})^k}{t}\right)^q=\lambda^k\exp\!\left(-\frac{k\lambda t^{2/k}}{2e}\right)$.

**Proof.** Let $s=t(\sqrt\lambda)^k$, which is positive. The scaling identity ( `scaled_threshold_rpow`) gives $s^{2/k}=\lambda t^{2/k}$, so the optimized moment identity ( `concentration_optimized_moment`) applied at $s$ has parameter $s^{2/k}/e=q$ and yields $((\sqrt q)^k/s)^q=\exp(-kq/2)$. To relate its left side to the desired one, use $s=t(\sqrt\lambda)^k$ and the laws of real powers for positive bases: $\lambda^{1/q-1/2}=\lambda^{1/q}/\sqrt\lambda$. Consequently the base in the claim equals $\lambda^{k/q}(\sqrt q)^k/s$. Raising to $q$ contributes the factor $\lambda^k$, while the remaining factor is the left side of the optimized identity. Finally, substituting $q=\lambda t^{2/k}/e$ in $\exp(-kq/2)$ gives the claimed expression.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ConcentrationAux.scaled_threshold_rpow`, `BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_optimized_moment`.
