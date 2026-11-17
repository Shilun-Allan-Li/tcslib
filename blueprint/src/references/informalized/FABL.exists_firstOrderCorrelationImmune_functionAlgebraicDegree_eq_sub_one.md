<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.exists_firstOrderCorrelationImmune_functionAlgebraicDegree_eq_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation immunity with high algebraic degree

**Claim.** For each $n\ge 3$, there is a Boolean function on the $n$-dimensional sign cube that is correlation immune of order one and whose binary encoding has algebraic degree $n-1$.

**Proof.** Take the constant-pair Boolean function. The result that this function is first-order correlation immune gives the required vanishing of its nonempty Fourier coefficients on sets of size at most one. The result computing the algebraic degree of its binary encoding gives degree $n-1$ under the hypothesis $n\ge 3$. These two facts establish both required properties for the same function.

**Key facts.** `FABL.constantPairBooleanFunction_isCorrelationImmune`, `FABL.functionAlgebraicDegree_constantPairBooleanFunction`.
