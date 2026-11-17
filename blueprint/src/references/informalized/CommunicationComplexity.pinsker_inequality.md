<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.pinsker_inequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pinsker inequality

**Claim.** For probability measures $\mu$ and $\nu$, the extended-real Kullback–Leibler divergence satisfies $\operatorname{ofReal}(2\,\mathrm{tvDistance}(\mu,\nu)^2)\le \mathrm{klDiv}(\mu,\nu)$.

**Proof.** Split according to whether $\mu$ is absolutely continuous with respect to $\nu$. In the absolutely continuous case, the corresponding Pinsker inequality is applied directly. Otherwise, the divergence is infinite by the characterization of KL divergence for failure of absolute continuity, and every extended nonnegative real is at most infinity; this proves the inequality in that case as well.

**Key facts.** `CommunicationComplexity.pinsker_inequality_of_ac`.
