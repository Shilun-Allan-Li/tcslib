<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.signMonomialChar_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Sign Monomials

**Claim.** The map assigning to each subset of coordinates its sign monomial character on the sign cube is injective.

**Proof.** Suppose two subsets $S,T$ give the same character. Fix a coordinate $i$ and evaluate both characters at the sign vector that is $-1$ in coordinate $i$ and $1$ in every other coordinate. The product defining the character is then $-1$ exactly when the subset contains $i$, and is $1$ otherwise. Equality of the characters therefore implies that $i$ belongs to $S$ exactly when it belongs to $T$. Since this holds for every coordinate, the subsets are equal.
