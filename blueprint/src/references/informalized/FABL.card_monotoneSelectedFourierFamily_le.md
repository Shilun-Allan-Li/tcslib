<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_monotoneSelectedFourierFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Selected Fourier Family

**Claim.** If the cardinality of $J$ is at most the coordinate cap, then the number of subsets of $J$ of size at most the specified degree is at most the stated family bound.

**Proof.** The family is the collection of subsets of $J$ whose sizes are at most the specified degree. The bound on low-degree subsets (`FABL.card_lowDegreeSubsets_le`) says its cardinality is at most $(k+1)(|J|+1)^k$, where $k$ is that degree. Since $|J|$ is at most the coordinate cap, monotonicity of multiplication and natural-number powers bounds this by $(k+1)(\text{coordinate cap}+1)^k$. This is exactly the family bound by its definition.

**Key facts.** `FABL.card_lowDegreeSubsets_le`.
