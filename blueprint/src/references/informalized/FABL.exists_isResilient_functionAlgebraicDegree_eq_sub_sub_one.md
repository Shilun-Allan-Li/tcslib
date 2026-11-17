<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.exists_isResilient_functionAlgebraicDegree_eq_sub_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resilient functions of sharp algebraic degree

**Claim.** Whenever $k<n-1$, there exists a $k$-resilient Boolean function whose algebraic degree over $\mathbb{F}_2$ is $n-k-1$.

**Proof.** Take the function `resilientDegreeSharpnessFunction n k hk`. The result that this construction is $k$-resilient is `resilientDegreeSharpnessFunction_isResilient`; the computation of the algebraic degree of its binary encoding gives exactly $n-k-1$ by `functionAlgebraicDegree_resilientDegreeSharpnessFunction`. These two properties together establish the claimed existence.

**Key facts.** `FABL.resilientDegreeSharpnessFunction_isResilient`, `FABL.functionAlgebraicDegree_resilientDegreeSharpnessFunction`.
