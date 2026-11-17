<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_expPoly_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant functions are exponential-polynomial

**Claim.** For every natural number $A$, the constant function with value $A$ is exponential-polynomial.

**Proof.** The polynomial bound with coefficient $A$ and degree $0$ is exponential-polynomial (`Complexity.expPoly_poly`). For each $n$, its value $A(n+1)^0$ equals $A$, so the constant function is pointwise bounded by that function. The downward-closure property of exponential-polynomial bounds (`Complexity.ExpPoly.of_le`) then proves the claim.

**Key facts.** `Complexity.expPoly_poly`, `Complexity.ExpPoly.of_le`.
