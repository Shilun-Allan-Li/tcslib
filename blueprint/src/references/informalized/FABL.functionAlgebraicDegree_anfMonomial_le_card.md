<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_anfMonomial_le_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for a Boolean monomial

**Claim.** For every subset $S$ of coordinates, the Boolean monomial indexed by $S$ has algebraic degree at most $|S|$.

**Proof.** The exact degree of this monomial is $|S|$ (`FABL.functionAlgebraicDegree_anfMonomial`). The asserted upper bound follows immediately from that equality.

**Key facts.** `FABL.functionAlgebraicDegree_anfMonomial`.
