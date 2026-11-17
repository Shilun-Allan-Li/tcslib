<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.expect_abs_rpow_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The One-Bit Affine Moment

**Claim.** For real $s,b$ with $|b|<1$, the uniform expectation on the one-dimensional Boolean cube of $|1+b\sigma(x_1)|^s$ is $((1+b)^s+(1-b)^s)/2$.

**Proof.** Consider the function $f(x)=1+b\,\sigma(x_1)$. Its values at the all-false and all-true points are respectively $1+b$ and $1-b$. The one-bit evaluation formulas express these values as the sum and difference of the constant and singleton Fourier coefficients (\texttt{one\_bit\_val\_false}, \texttt{one\_bit\_val\_true}); solving gives those coefficients as $1$ and $b$. The one-bit absolute-moment formula (\texttt{expect\_abs\_rpow\_one\_bit}) therefore makes the expectation the average of $|1+b|^s$ and $|1-b|^s$. Since $|b|<1$, both $1+b$ and $1-b$ are positive, so the absolute values can be removed, yielding the stated formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.one_bit_val_false`, `BooleanAnalysis.Hypercontractivity.one_bit_val_true`, `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit`.
