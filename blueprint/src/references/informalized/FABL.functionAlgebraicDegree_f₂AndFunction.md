<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Examples.lean :: FABL.functionAlgebraicDegree_f₂AndFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the full monomial

**Claim.** The product of all $n$ coordinates on the binary cube has algebraic degree $n$.

**Proof.** The function in question is the monomial indexed by the full coordinate set. A monomial indexed by a finite set has algebraic degree equal to that set's cardinality (`functionAlgebraicDegree_anfMonomial`). The full coordinate set has cardinality $n$, giving the result.

**Key facts.** `FABL.functionAlgebraicDegree_anfMonomial`.
