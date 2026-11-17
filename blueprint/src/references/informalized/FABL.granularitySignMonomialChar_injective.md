<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.granularitySignMonomialChar_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Sign Characters

**Claim.** Distinct finite subsets of indices define distinct sign monomial characters.

**Proof.** Suppose two such characters, associated to $S$ and $T$, are equal. Fix an index $i$ and evaluate both characters at the sign-valued function that is $-1$ at $i$ and $1$ everywhere else. In the product defining the character, every factor is $1$ except possibly the factor at $i$, so the value is $-1$ exactly when $i$ belongs to the indexing subset, and is $1$ otherwise. Equality of the characters therefore implies $i\in S$ exactly when $i\in T$. Since this holds for every $i$, the two finite subsets are equal.
