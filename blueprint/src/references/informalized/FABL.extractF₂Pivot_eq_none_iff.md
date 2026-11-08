<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.extractF₂Pivot_eq_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When Pivot Extraction Fails

**Claim.** Pivot extraction at a variable returns no equation exactly when every equation in the list has coefficient zero at that variable.

**Proof.** Induct on the list. The claim is immediate for the empty list. For a nonempty list, first suppose its head has coefficient $1$ at the chosen variable. Extraction succeeds immediately, and the head itself also shows that not all coefficients are zero, so both sides of the equivalence are false. Otherwise the head's coefficient is zero: over $\mathbb F_2$, a coefficient that is not $1$ must be $0$. Extraction then recurses on the tail. If that recursive search fails, the induction hypothesis says every tail coefficient is zero; together with the head coefficient this gives the condition for the whole list, and conversely that condition forces the recursive search to fail. If the recursive search succeeds, extraction also succeeds, while the recursive pivot has a nonzero coefficient at the chosen variable, so the condition that all coefficients vanish is false. Thus the equivalence holds in every case.
