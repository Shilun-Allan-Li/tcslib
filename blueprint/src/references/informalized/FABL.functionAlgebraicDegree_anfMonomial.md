<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_anfMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Boolean monomial

**Claim.** For every subset $S$ of coordinates, the Boolean monomial indexed by $S$ has algebraic degree exactly $|S|$.

**Proof.** The ANF coefficient of the monomial indexed by $S$ is $1$ at the subset $S$ and zero at every other subset (`FABL.anfCoeff_anfMonomial`). Its ANF support is therefore the singleton consisting of $S$. The degree, defined as the largest cardinality in that support, is consequently $|S|$.

**Key facts.** `FABL.anfCoeff_anfMonomial`.
