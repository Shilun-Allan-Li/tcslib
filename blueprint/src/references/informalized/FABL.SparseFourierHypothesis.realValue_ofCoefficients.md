<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.SparseFourierHypothesis.realValue_ofCoefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real sparse Fourier expansion

**Claim.** The real value of the hypothesis formed from a finite family and its rational coefficients equals the sparse Fourier approximation obtained by extending those coefficients by zero outside the family.

**Proof.** Fix a sign vector $x$. The real value is a sum over the family with each member tagged by its proof of membership. Reindex this tagged sum by the attached family (`Finset.attach_eq_univ`). For each tagged member, the extended coefficient agrees with its original coefficient because that member belongs to the family; consequently the summands agree. Finally, the sum over the attached family is the ordinary sum over the original family (`Finset.sum_attach`). This proves equality at every $x$, and therefore equality of the two functions.
