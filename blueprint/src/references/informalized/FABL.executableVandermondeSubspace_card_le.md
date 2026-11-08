<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeSubspace_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vandermonde Subspace Cardinality Bound

**Claim.** The row span of the executable Vandermonde matrix has cardinality at most $2^k n^{k-1}$.

**Proof.** The matrix has $(k-1)d+1$ rows. The cardinality of a row span over $\mathbb F_2$ is at most $2$ to the number of rows (`card_matrixRowSpan_le_two_pow`). The row-count estimate (`executableVandermondeRowCount_cardBound`) bounds this power by $2^k n^{k-1}$. Chaining the two inequalities proves the claim.

**Key facts.** `FABL.card_matrixRowSpan_le_two_pow`, `FABL.executableVandermondeRowCount_cardBound`.
