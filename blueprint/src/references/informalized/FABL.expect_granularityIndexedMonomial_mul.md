<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.expect_granularityIndexedMonomial_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Sign Monomials

**Claim.** For finite $I$ and subsets $S,T\subseteq I$, the uniform expectation of the product of their sign monomials is $1$ if $S=T$ and $0$ otherwise.

**Proof.** Regard each sign monomial as a real-valued character on the additive group of sign assignments. Reindexing assignments by the equivalence between additive signs and multiplicative signs identifies the expectation of the product of the two monomials with the weighted inner product of their characters. Orthogonality of characters says this inner product is $1$ when the characters agree and $0$ otherwise. The monomial-character map is injective (`FABL.granularitySignMonomialChar_injective`), so the characters agree exactly when their indexing sets agree. This gives the stated values.

**Key facts.** `FABL.granularitySignMonomialChar_injective`.
