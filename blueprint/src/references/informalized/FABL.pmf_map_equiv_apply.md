<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.pmf_map_equiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass Under a Bijection

**Claim.** For finite types $\alpha$ and $\beta$, a probability mass function $p$ on $\alpha$, an equivalence $e:\alpha\to\beta$, and $b\in\beta$, the mass at $b$ of the pushforward of $p$ along $e$ is $p(e^{-1}(b))$.

**Proof.** The pushforward mass at $b$ is the sum, over all $a\in\alpha$, of the mass $p(a)$ when $e(a)=b$, and zero otherwise. Because $e$ is a bijection, exactly one point contributes: $a=e^{-1}(b)$. The sum therefore reduces to $p(e^{-1}(b))$.
