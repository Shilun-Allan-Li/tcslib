<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.list_prod_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Cube Monomials

**Claim.** For any finite list of subsets $S_1,\ldots,S_k$ and any sign vector $x$, the product of their cube monomials is the monomial indexed by the symmetric difference of all the sets.

**Proof.** Induct on the list. For the empty list, both sides are the empty product, hence $1$. For a list beginning with $S$, its product is the monomial for $S$ times the product for the remaining sets. By induction, the latter is the monomial indexed by their iterated symmetric difference. The product rule for two monomials (`monomial_mul_monomial`) identifies the result with the monomial indexed by the symmetric difference of $S$ and that remainder, exactly the list's iterated symmetric difference.

**Key facts.** `FABL.monomial_mul_monomial`.
