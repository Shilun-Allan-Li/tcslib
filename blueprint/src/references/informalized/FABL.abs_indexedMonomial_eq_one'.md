<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_indexedMonomial_eq_one' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute value of an indexed sign monomial

**Claim.** For a finite set of indices and a sign assigned to each index, the absolute value of their product is $1$.

**Proof.** The indexed monomial has square equal to $1$ (\texttt{FABL.indexedMonomial\_sq}), so it equals either $1$ or $-1$. The absolute value of either possibility is $1$.

**Key facts.** `FABL.indexedMonomial_sq`.
