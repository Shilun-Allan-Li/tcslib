<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd support characterization

**Claim.** For a Boolean function on the $n$-dimensional binary cube, with $n>0$, its algebraic degree equals $n$ exactly when it takes the value $1$ on an odd number of inputs.

**Proof.** The general characterization says that the degree equals the dimension precisely when either the dimension is zero or the one-support has odd cardinality (`functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd`). Since $n>0$, the zero-dimensional alternative is excluded, leaving exactly the odd-cardinality condition.

**Key facts.** `FABL.functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd`.
