<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.qth_moment_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The $q$-th Moment Splits Along the Last Coordinate

**Claim.** Fix a natural number $q$ and a Boolean function $f:\{0,1\}^{n+1}\to\mathbb{R}$. Writing $g(x)=\tfrac12\bigl(f(x,0)+f(x,1)\bigr)$ for the average of $f$ over its last coordinate and $h(x)=\tfrac12\bigl(f(x,0)-f(x,1)\bigr)$ for its half-difference, both functions on $\{0,1\}^n$, the $q$-th moment of $f$ under the uniform measure on $\{0,1\}^{n+1}$ equals
\[
  \mathbb{E}\bigl[f^q\bigr] \;=\; \mathbb{E}\!\left[\frac{(g+h)^q+(g-h)^q}{2}\right],
\]
the right-hand expectation now being taken over the uniform measure on $\{0,1\}^n$.

**Proof.** The whole argument is the observation that conditioning on the last bit splits both the domain and the measure in half, together with the elementary identities $g+h=f(\cdot,0)$ and $g-h=f(\cdot,1)$.

Throughout, write $w_m = 2^{-m}$ for the uniform weight on $\{0,1\}^m$, so that for any $\varphi$ one has $\mathbb{E}[\varphi]=w_m\sum_{x}\varphi(x)$. Write $f_0(x)=f(x,0)$ and $f_1(x)=f(x,1)$ for the two restrictions of $f$ obtained by fixing its last coordinate to $0$ or $1$ (in Lean, `Fin.snoc x false` and `Fin.snoc x true`); these are functions on $\{0,1\}^n$. With this notation $g=\tfrac12(f_0+f_1)$ and $h=\tfrac12(f_0-f_1)$.

1. **Unfold the left-hand expectation and halve the weight.** By definition,
\[
  \mathbb{E}\bigl[f^q\bigr] \;=\; w_{n+1}\sum_{x\in\{0,1\}^{n+1}} f(x)^q .
\]
The weight itself halves when the dimension drops by one: $w_{n+1}=w_n/2$ (`uniformWeight_succ`). So the left-hand side is $\tfrac{w_n}{2}\sum_{x\in\{0,1\}^{n+1}} f(x)^q$.

2. **Split the sum by the value of the last coordinate.** Every point of $\{0,1\}^{n+1}$ is a point of $\{0,1\}^n$ with a final bit appended, and summing a function over the cube is the same as summing over the two choices of that final bit separately (`sum_boolCube_succ`):
\[
  \sum_{x\in\{0,1\}^{n+1}}\varphi(x)
   \;=\; \sum_{x\in\{0,1\}^{n}}\varphi(x,0)\;+\;\sum_{x\in\{0,1\}^{n}}\varphi(x,1).
\]
Applying this to $\varphi=f^q$ turns the left-hand side into
\[
  \frac{w_n}{2}\left(\sum_{x\in\{0,1\}^n} f_0(x)^q \;+\; \sum_{x\in\{0,1\}^n} f_1(x)^q\right).
\]

3. **Identify the summands on the right.** Pointwise on $\{0,1\}^n$,
\[
  g+h=\tfrac12(f_0+f_1)+\tfrac12(f_0-f_1)=f_0,
  \qquad
  g-h=\tfrac12(f_0+f_1)-\tfrac12(f_0-f_1)=f_1 .
\]
Hence $(g+h)^q=f_0^q$ and $(g-h)^q=f_1^q$ at every point, and the right-hand integrand is exactly $\tfrac12\bigl(f_0^q+f_1^q\bigr)$. (In the Lean source this cancellation is not invoked as a named lemma; the definitions of $g$ and $h$ are unfolded and the two sides are driven to a common normal form by ring normalisation, which amounts to the same computation.)

4. **Assemble the right-hand expectation.** The right-hand side is an expectation over $\{0,1\}^n$, so it carries the weight $w_n$:
\[
  \mathbb{E}\!\left[\frac{(g+h)^q+(g-h)^q}{2}\right]
   = w_n\sum_{x\in\{0,1\}^n}\frac{f_0(x)^q+f_1(x)^q}{2}
   = \frac{w_n}{2}\left(\sum_{x} f_0(x)^q+\sum_{x} f_1(x)^q\right),
\]
using linearity of the sum to pull the factor $\tfrac12$ out and to split the sum of the two $q$-th powers. This is precisely the expression reached for the left-hand side in step 2, so the two sides are equal. $\qquad\blacksquare$

**Key facts.** `BooleanAnalysis.Hypercontractivity.uniformWeight_succ`, `BooleanAnalysis.Hypercontractivity.sum_boolCube_succ`.
