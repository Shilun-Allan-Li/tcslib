<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.two_pow_log_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic power inequality

**Claim.** For every natural number $n$, if $j=\lfloor\log_2 n\rfloor$ with the natural-number logarithm convention, then $2^{j^2}\le n^j$.

**Proof.** If $n=0$, the natural logarithm convention makes the claimed inequality immediate. Otherwise, the defining bound for the natural logarithm gives $2^{\mathrm{Nat.log}\,2\,n}\le n$. Raising both sides to the power $j=\mathrm{Nat.log}\,2\,n$ preserves the inequality, since both sides are natural numbers and exponentiation by a fixed natural exponent is monotone. Using $j^2=j\cdot j$ identifies the resulting left-hand side with $2^{j^2}$ and the right-hand side with $n^j$.
