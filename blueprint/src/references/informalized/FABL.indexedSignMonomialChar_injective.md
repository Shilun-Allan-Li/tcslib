<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.indexedSignMonomialChar_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of sign monomials

**Claim.** Distinct finite subsets of indices define distinct characters on indexed sign assignments.

**Proof.** Suppose the characters associated with finite subsets $S$ and $T$ are equal. Fix an arbitrary index $i$ and evaluate both characters at the assignment that is $-1$ at $i$ and $1$ at every other index. The resulting value is $-1$ exactly when $i$ belongs to the subset, and is $1$ otherwise. Equality of the character values therefore implies that $i$ belongs to $S$ exactly when it belongs to $T$. Since this holds for every index, $S=T$, proving injectivity.
