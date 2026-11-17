<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.polynomial_eval_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Polynomial Evaluation

**Claim.** Every polynomial with natural-number coefficients is monotone on the natural numbers.

**Proof.** Let $a\le b$. The polynomial's evaluation is a finite sum of terms, one for each coefficient, of the form $c_n a^n$. For each exponent $n$, natural-number powers preserve the inequality, so $a^n\le b^n$. Multiplication by the nonnegative coefficient $c_n$ preserves it as well. Summing these termwise inequalities gives $p(a)\le p(b)$.
