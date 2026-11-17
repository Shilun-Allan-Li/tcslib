<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Repetition Budget

**Claim.** For $N\le L$, the displayed repetition-time expression is bounded by $(13+7k+a(K+1)^d+K)(L+1)^{2d+3}$.

**Proof.** Since $N\le L$, bound the iteration term by replacing $N$ with $L$ and use $K(L+1)^2+1\le (K+1)(L+1)^2$. Monotonicity of natural-number powers then gives
\[
N\bigl(a(K(L+1)^2+1)^d+2\bigr)\le a(K+1)^d(L+1)^{2d+1}+2(L+1).
\]
The remaining linear terms satisfy $2L+9+k(3L+7)+2(L+1)\le(13+7k)(L+1)$. Thus the whole expression is at most
\[
(13+7k)(L+1)+a(K+1)^d(L+1)^{2d+1}+K(L+1)^2.
\]
Because $L+1\ge1$, each of $(L+1)$, $(L+1)^{2d+1}$, and $(L+1)^2$ is at most $(L+1)^{2d+3}$. Multiply these three inequalities by their respective nonnegative coefficients and add them. Factoring out $(L+1)^{2d+3}$ gives the claimed bound.
