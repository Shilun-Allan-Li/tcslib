<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Concentration.lean :: BooleanAnalysis.Hypercontractivity.ConcentrationAux.concentration_optimized_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimized Moment Identity

**Claim.** For $k>0$ and $t>0$, set $q=t^{2/k}/e$. Then $\left(\frac{(\sqrt q)^k}{t}\right)^q=\exp\!\left(-\frac{k}{2e}t^{2/k}\right)$.

**Proof.** The quantity $q=t^{2/k}/e$ is positive. Taking logarithms, the logarithm of $q$ is $(2/k)\log t-1$. Thus the logarithm of $(\sqrt q)^k/t$ is $\frac{k}{2}\log q-\log t=-k/2$. Since this base is positive, raising it to the real power $q$ gives $\exp(q(-k/2))$. Substituting $q=t^{2/k}/e$ yields the stated exponential.
