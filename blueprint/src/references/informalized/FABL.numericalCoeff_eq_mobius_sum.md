<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalCoeff_eq_mobius_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Möbius Formula for Numerical Coefficients

**Claim.** The numerical coefficient at $S$ is the alternating sum of the function's values at indicator points indexed by subsets of $S$.

**Proof.** The numerical Möbius coefficient equals the numerical coefficient function (`FABL.numericalMobiusCoeff_eq_numericalCoeff`). By the definition of the Möbius coefficient, its value at $S$ is the sum over $T\subseteq S$ of $(-1)^{|S|-|T|}\varphi(\mathbf 1_T)$. Evaluating the function equality at $S$ gives the claimed formula.

**Key facts.** `FABL.numericalMobiusCoeff_eq_numericalCoeff`.
