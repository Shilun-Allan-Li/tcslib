<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time All-Ones Test

**Claim.** The function sending a binary word $x$ to the one-bit word recording whether $x$ consists entirely of ones is polynomial-time computable.

**Proof.** The proof first computes the fixed-point output of the linear-time function `incFixed`, using the linear-time computation theorem (`Turing.FinTM.computesFunInTime_incFixed`). It then applies the polynomial-time test for equality with the empty word (`Complexity.a3n_poly_fixed_eq`) to that output, using closure of polynomial-time computability under composition (`Complexity.PolyTimeComputable.comp`). It remains to identify the resulting test: `incFixed x` is `none` exactly when $x$ is the all-ones word of its length (`Complexity.a3n_inc_none`), and it can never be `some []` (`Complexity.a3n_inc_nonempty`). Thus `(incFixed x).getD []` equals the empty word exactly when `incFixed x` is `none`; the composed equality test therefore returns the desired bit.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Turing.FinTM.computesFunInTime_incFixed`, `Complexity.a3n_poly_fixed_eq`, `Complexity.a3n_inc_none`, `Complexity.a3n_inc_nonempty`.
