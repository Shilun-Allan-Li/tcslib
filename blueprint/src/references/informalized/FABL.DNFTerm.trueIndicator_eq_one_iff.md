<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFTerm.trueIndicator_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True indicator characterization

**Claim.** For a DNF term $T$ and input $x$, the true indicator equals $1$ exactly when $T$ evaluates to $-1$ at $x$.

**Proof.** By definition, the true indicator is $1$ if the term evaluates to $-1$, and is $0$ otherwise. Since $0\ne 1$, the equality to $1$ holds precisely in the first case.
