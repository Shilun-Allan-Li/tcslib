<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.relativeHammingDist_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative Hamming distance under duality

**Claim.** Replacing both Boolean functions by their Boolean duals leaves their relative Hamming distance unchanged.

**Proof.** Relative Hamming distance is the uniform probability that the two functions disagree (`FABL.uniformProbability_ne_eq_relativeHammingDist`). It therefore suffices to compare the disagreement probabilities. The map sending each cube point to its coordinatewise negation is a bijection of the sign cube, so it preserves the uniform average. At a point paired with $x$ by this map, the dual functions both negate the respective outputs of $f$ and $g$ at $x$. Negation is injective on signs, so those outputs disagree exactly when $f(x)$ and $g(x)$ disagree. The disagreement indicators thus correspond under the bijection, and their uniform averages—and hence the relative Hamming distances—are equal.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`.
