<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.coNP_subset_PH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP Lies in the Polynomial Hierarchy

**Claim.** Every language over the binary alphabet whose complement belongs to the class of languages with polynomial-length existential certificates verifiable in polynomial time belongs to the polynomial hierarchy.

**Proof.** Use the identity that the first universal level of the polynomial hierarchy equals coNP (`Complexity.PiP_one`). The hierarchy contains every language in that level, by the inclusion of each universal level in the polynomial hierarchy (`Complexity.PiP_subset_PH`, applied at level $1$). Substituting the identity into this inclusion gives the claimed containment.

**Key facts.** `Complexity.PiP_one`, `Complexity.PiP_subset_PH`.
