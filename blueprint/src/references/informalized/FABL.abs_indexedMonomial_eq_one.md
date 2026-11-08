<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.abs_indexedMonomial_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute value of an indexed sign monomial

**Claim.** For a finite set of indices and a sign assigned to each index, the absolute value of their product is $1$.

**Proof.** The indexed monomial has square equal to $1$ (\texttt{FABL.indexedMonomial\_sq}). A real number whose square is $1$ is either $1$ or $-1$. In either case its absolute value is $1$, as required.

**Key facts.** `FABL.indexedMonomial_sq`.
