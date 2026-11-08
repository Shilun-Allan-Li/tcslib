<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.monomial_liftFreeFrequency_combine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial on the free coordinates

**Claim.** The monomial on the image of $S$ among the original coordinates, evaluated at the combined assignment, equals the monomial on $S$ evaluated at $y$.

**Proof.** Apply the factorization for a union of lifted free and fixed frequencies (`indexedMonomial_lift_union_combine`) with the fixed frequency set empty. The lifted union is then just the image of $S$. The factor contributed by the empty fixed set is the empty product, hence $1$. The remaining factor is the indexed monomial on $S$ evaluated at $y$, yielding the stated equality.

**Key facts.** `FABL.indexedMonomial_lift_union_combine`.
