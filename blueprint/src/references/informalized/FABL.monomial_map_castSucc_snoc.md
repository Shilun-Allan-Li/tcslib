<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.monomial_map_castSucc_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial under Appending

**Claim.** Appending a sign to the vector and embedding the indexing set into the original coordinates leaves the monomial unchanged.

**Proof.** Expand the monomial as a product over the embedded set. The embedding `Fin.castSuccEmb` sends each index to its corresponding coordinate among the first $k$ positions, and `Fin.snoc` agrees with $x$ on those positions. Thus each factor in the product is the same as the corresponding factor in the monomial on $T$ at $x$, so the products agree.
