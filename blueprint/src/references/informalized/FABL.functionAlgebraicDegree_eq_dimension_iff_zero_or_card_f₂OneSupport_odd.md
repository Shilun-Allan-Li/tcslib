<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top degree and odd support

**Claim.** The algebraic degree of a Boolean function on the $n$-dimensional binary cube equals $n$ if and only if either $n=0$ or the function takes the value $1$ on an odd number of inputs.

**Proof.** First consider the zero-dimensional case. Then the right-hand disjunction holds automatically, and the degree is at most the dimension (`functionAlgebraicDegree_le_dimension`), so it is zero as required. Now suppose $n\ne0$, hence $n>0$. In positive dimension, the degree equals $n$ exactly when the coefficient of the full coordinate set in the algebraic normal form is nonzero (`functionAlgebraicDegree_eq_dimension_iff_anfCoeff_univ_ne_zero`). That coefficient is the sum over all inputs of the function's values in $\mathbb F_2$; it is nonzero precisely when the number of inputs where the function equals $1$ is odd (`anfCoeff_univ_ne_zero_iff_card_f₂OneSupport_odd`). This yields the claimed disjunction.

**Key facts.** `FABL.functionAlgebraicDegree_le_dimension`, `FABL.functionAlgebraicDegree_eq_dimension_iff_anfCoeff_univ_ne_zero`, `FABL.anfCoeff_univ_ne_zero_iff_card_f₂OneSupport_odd`.
