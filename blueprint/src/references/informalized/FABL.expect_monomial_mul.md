<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.expect_monomial_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Sign Monomials

**Claim.** For subsets $S,T$ of the coordinates, the uniform average of the product of their sign monomials is $1$ if $S=T$ and $0$ otherwise.

**Proof.** Identify each sign monomial with the corresponding character of the finite additive group of sign vectors. The uniform average of the product of two such characters is their weighted inner product. Character orthogonality says this inner product is $1$ when the characters agree and $0$ otherwise (`AddChar.wInner_cWeight_eq_boole`). The characters indexed by subsets are injectively indexed (`signMonomialChar_injective`), so they agree exactly when $S=T$.

**Key facts.** `FABL.signMonomialChar_injective`.
