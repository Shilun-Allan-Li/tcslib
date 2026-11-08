<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.functionAlgebraicDegree_encoding_eq_zero_of_eq_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Constant Boolean Function

**Claim.** A constant Boolean function on the sign cube, when encoded as a function on the binary cube, has algebraic degree zero.

**Proof.** Because the original function is constant, its encoding is the constant function with value equal to the binary encoding of that fixed sign. This value is either $0$ or $1$. In the first case the encoded function is the zero function, whose algebraic degree is zero (`functionAlgebraicDegree_zero`). In the second case it is the constant-one function, whose algebraic degree is also zero (`functionAlgebraicDegree_one`).

**Key facts.** `FABL.functionAlgebraicDegree_zero`, `FABL.functionAlgebraicDegree_one`.
