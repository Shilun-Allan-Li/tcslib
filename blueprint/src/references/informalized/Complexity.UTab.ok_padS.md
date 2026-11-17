<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_padS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity under source padding

**Claim.** If every source in a list $l$ is valid for $\rho$, then every source in the list obtained by appending enough constant false sources to reach length $m$ is valid for $\rho$.

**Proof.** Take a source in the padded list. It either belongs to the original list, in which case validity follows from the hypothesis, or to the replicated padding. Every source in that padding is constant false, hence valid by definition.
