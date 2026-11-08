<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_energy_eq_of_symmetric_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal-degree component energies under symmetry

**Claim.** If $f$ is invariant under coordinate permutations and $S,T$ have the same cardinality, then the squared norms of its orthogonal components at $S$ and $T$ are equal.

**Proof.** A permutation $\sigma$ of the coordinates can be chosen so that it maps $S$ to $T$, since the two sets have the same cardinality. Permuting the input of the orthogonal component of a symmetric function at $S$ gives the component at the permuted set ($\texttt{FABL.FiniteFourierBasis.permuteProductFunction_orthogonalComponent_of_symmetric}$). The product inner product is invariant under applying the same coordinate permutation to both functions ($\texttt{FABL.productInner_permuteProductFunction}$). Apply this invariance to the component at $S$ paired with itself, then replace its permuted component by the component at $T$. The resulting equality of energies gives the claim.

**Key facts.** `FABL.FiniteFourierBasis.permuteProductFunction_orthogonalComponent_of_symmetric`, `FABL.productInner_permuteProductFunction`.
