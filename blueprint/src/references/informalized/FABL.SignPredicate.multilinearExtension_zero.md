<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignPredicate.multilinearExtension_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Extension at Zero

**Claim.** At the zero vector, the multilinear extension of a predicate equals the Fourier coefficient of its indicator at the empty set.

**Proof.** In the defining sum, every nonempty subset contributes zero: its coordinate product contains at least one factor equal to zero. The empty subset contributes its Fourier coefficient, since its empty product is $1$. Therefore the sum is precisely the coefficient indexed by the empty set.
