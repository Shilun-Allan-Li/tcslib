<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.indexedMonomial_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of an indexed sign monomial

**Claim.** The square of any real indexed monomial on a finite set of coordinates is $1$.

**Proof.** The square of a finite product is the product of the squares of its factors. Each sign value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), so each factor's square is $1$. Their product is therefore $1.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
