<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFTerm.trueIndicator_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the true indicator

**Claim.** For every DNF term $T$ and input $x$, its true indicator is nonnegative.

**Proof.** If $T$ evaluates to $-1$ at $x$, the indicator is $1$; otherwise it is $0. Both possible values are nonnegative.
