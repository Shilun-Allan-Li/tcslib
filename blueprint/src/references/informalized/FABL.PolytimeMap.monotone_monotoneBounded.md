<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.monotone_monotoneBounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Runtime Bound

**Claim.** If a function on Boolean lists is computable in polynomial time, then the polynomial runtime bound obtained by evaluating its runtime polynomial is monotone as a function of input length.

**Proof.** The runtime bound of the modified computation is the evaluation of the original runtime polynomial. Every polynomial with natural-number coefficients is monotone on the natural numbers (polynomial_eval_monotone): writing its evaluation as a sum of terms, increasing the input weakly increases each natural-number power, and multiplication by each nonnegative coefficient preserves that inequality. Hence this runtime bound is monotone.

**Key facts.** `FABL.PolytimeMap.polynomial_eval_monotone`.
