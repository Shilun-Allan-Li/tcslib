<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.sum_energy_powerset_eq_sum_choose_levelEnergy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric energy over a powerset

**Claim.** For a product-symmetric function, the sum of orthogonal-component energies over nonempty subsets of $S$ equals the sum, over levels $k\leq |S|$, of $\binom{|S|}{k}$ times the energy at the first $k$ coordinates, with the level-zero energy defined to be zero.

**Proof.** First rewrite the sum over nonempty subsets as a sum over all subsets, assigning zero to the empty subset. Partition the powerset by subset cardinality; the level-$k$ part is then the sum over subsets of $S$ of size $k$. At level zero, every contribution is zero, agreeing with the defined level-zero energy. For a positive level $k$, every such subset is nonempty. Product symmetry implies that component energies depend only on the size of the indexing set (orthogonalComponent_energy_eq_of_symmetric_of_card_eq), so each term equals the energy at the first $k$ coordinates. There are exactly $\binom{|S|}{k}$ subsets of that size, and the first $k$ coordinates indeed have size $k$ when $k\leq n$ (card_firstCoordinates). Thus the level sum is the binomial coefficient times the symmetric level energy. Summing over all levels gives the identity.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_energy_eq_of_symmetric_of_card_eq`, `FABL.card_firstCoordinates`.
