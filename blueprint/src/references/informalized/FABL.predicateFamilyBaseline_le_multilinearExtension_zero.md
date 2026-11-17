<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.predicateFamilyBaseline_le_multilinearExtension_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Baseline and zero extension

**Claim.** For a nonempty finite family of sign predicates and any chosen member, the minimum empty-set Fourier coefficient is at most that predicate’s multilinear extension at the zero vector.

**Proof.** At the zero vector, every nonempty-set term in the multilinear extension vanishes, while the empty-set term remains unchanged. Thus the extension equals the empty-set Fourier coefficient (by `SignPredicate.multilinearExtension_zero`). The baseline is the infimum of these coefficients over the finite family, so it is at most the coefficient of the chosen member, since that member belongs to the family.

**Key facts.** `FABL.SignPredicate.multilinearExtension_zero`.
