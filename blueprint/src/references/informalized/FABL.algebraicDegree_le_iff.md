<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.algebraicDegree_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic degree bounds

**Claim.** The algebraic degree of a coefficient function is at most $r$ exactly when every subset with nonzero coefficient has cardinality at most $r$.

**Proof.** By definition, the degree is the supremum of the cardinalities of subsets in the support, where the support consists of the subsets with nonzero coefficient. The supremum of a finite set of natural numbers is at most $r$ exactly when each of its members is at most $r$. Thus the degree bound is equivalent to the stated condition on every subset with nonzero coefficient.
