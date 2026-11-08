<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_lowDegreeSubsets_empiricalInfluentialCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for low-degree subsets

**Claim.** The number of subsets of the empirically influential coordinates having size at most the degree determined by $t$ and $\varepsilon$ is at most the corresponding family bound.

**Proof.** For any finite coordinate set $J$ and degree $k$, the number of its subsets of size at most $k$ is at most $(k+1)(|J|+1)^k$ (`card_lowDegreeSubsets_le`). Apply this with $J$ the empirically influential coordinates and $k$ the specified degree. The cap in the definition of the family bound ensures that $|J|$ is at most the coordinate cap (`card_empiricalInfluentialCoordinates_le`). Consequently $(|J|+1)^k$ is at most the corresponding power of the cap plus one; multiplying by the nonnegative factor $k+1$ preserves the inequality. The resulting expression is exactly the family bound.

**Key facts.** `FABL.card_lowDegreeSubsets_le`, `FABL.card_empiricalInfluentialCoordinates_le`.
