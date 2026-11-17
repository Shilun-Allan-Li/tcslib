<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basic.lean :: BooleanAnalysis.GaussianSpace.hermiteFunction_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-index Hermite function

**Claim.** For every natural number $n$ and every $x\in\mathbb R^n$, the Hermite function indexed by the zero multi-index has value $1$.

**Proof.** Write the Hermite function as a product of evaluations of normalized one-variable Hermite polynomials (`hermiteFunction_eq_prod`). Every coordinate index is zero, so each factor is the degree-zero normalized Hermite polynomial, the constant $1$. Their product is therefore $1$.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_eq_prod`.
