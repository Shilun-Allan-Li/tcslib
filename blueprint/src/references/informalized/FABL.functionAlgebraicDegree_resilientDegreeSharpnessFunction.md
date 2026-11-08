<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.functionAlgebraicDegree_resilientDegreeSharpnessFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharpness of the resilient degree bound

**Claim.** The encoded resilient sharpness function has algebraic degree exactly $n-k-1$.

**Proof.** The function is resilient of order $k$ (`resilientDegreeSharpnessFunction_isResilient`), so the resilient degree bound gives an upper bound of $n-k-1$ (`functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient`). For the reverse inequality, its binary encoding is the sum of the coordinate sum on the prefix $S=\operatorname{resilientSharpnessPrefix}(n,k)$ and the monomial on the complementary tail $T=\operatorname{resilientSharpnessTail}(n,k)$ (`booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction`). The tail is nonempty and disjoint from the prefix. For such disjoint sets, the coefficient of the $T$-monomial in this sum is $1$ (`anfCoeff_coordinateSum_add_anfMonomial_of_disjoint`), hence nonzero. Any set with nonzero algebraic-normal-form coefficient has size at most the function's algebraic degree (`card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero`), so the degree is at least $|T|$. The tail has size $n-k-1$ (`card_resilientSharpnessTail`), giving the matching lower bound and hence equality.

**Key facts.** `FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient`, `FABL.resilientDegreeSharpnessFunction_isResilient`, `FABL.booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction`, `FABL.anfCoeff_coordinateSum_add_anfMonomial_of_disjoint`, `FABL.card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero`, `FABL.card_resilientSharpnessTail`.
