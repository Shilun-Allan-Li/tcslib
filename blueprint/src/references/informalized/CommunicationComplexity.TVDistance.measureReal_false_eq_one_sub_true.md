<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.measureReal_false_eq_one_sub_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False-event probability

**Claim.** For a probability measure $\mu$ on $\mathrm{Bool}$, the mass of $\{\mathrm{false}\}$ is one minus the mass of $\{\mathrm{true}\}$.

**Proof.** The two Boolean values are complements, so $\{\mathrm{false}\}$ is the complement of $\{\mathrm{true}\}$. The complement formula for a finite measure gives the mass of the former as the total mass minus the mass of the latter. Since $\mu$ is a probability measure, its total mass is one, yielding the stated equality.
