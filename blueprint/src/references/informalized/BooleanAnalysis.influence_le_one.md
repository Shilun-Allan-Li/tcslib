<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.influence_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Influence of a Coordinate Is at Most One

**Claim.** For a Boolean function $f\colon\{0,1\}^n\to\mathbb{R}$ taking values in $\{-1,1\}$ and a coordinate $i$, the influence $\mathrm{Inf}_i[f]=\E\!\left[(f(x)-f(x^i))^2/4\right]$ — the uniform average over the cube of the squared discrete difference across edge $i$, rescaled by $\tfrac14$ — is bounded above by $1$. Here $x^i$ is $x$ with its $i$-th bit flipped and the expectation is uniform on $\{0,1\}^n$.

**Proof.** The argument is the obvious termwise bound: every summand in the expectation lies in $\{0,1\}$, so their uniform average cannot exceed $1$. Unwinding the definitions, the expectation is written out explicitly as a weighted sum,
\[
  \mathrm{Inf}_i[f] \;=\; 2^{-n}\sum_{x\in\{0,1\}^n}\frac{(f(x)-f(x^i))^2}{4},
\]
since the uniform weight attached to each of the points of the cube is $(2^{-1})^n = 2^{-n}$. The proof then proceeds in two mechanical steps and a final multiplication.

1. **Each summand is at most $1$.** Fix a point $x$. By hypothesis both $f(x)$ and $f(x^i)$ lie in $\{-1,1\}$, which leaves four cases. If the two values agree, then $f(x)-f(x^i)=0$ and the term $(f(x)-f(x^i))^2/4$ is $0$. If they disagree, then $f(x)-f(x^i)=\pm 2$, so its square is $4$ and the term is exactly $4/4 = 1$. In every case the summand is $\le 1$. (In fact the summand equals the indicator $\mathbf 1[f(x)\neq f(x^i)]$ of the edge being pivotal, but the proof only needs the upper bound.) Summing this inequality over all points of the cube (a termwise comparison of sums) gives
\[
  \sum_{x\in\{0,1\}^n}\frac{(f(x)-f(x^i))^2}{4}\;\le\;\sum_{x\in\{0,1\}^n} 1\;=\;\bigl|\{0,1\}^n\bigr|.
\]

2. **The cube has $2^n$ points.** The number of functions $\{1,\dots,n\}\to\{0,1\}$ is $2^n$, a routine cardinality count. Hence the right-hand side above is $2^n$, giving $\sum_x (f(x)-f(x^i))^2/4 \le 2^n$.

3. **Multiply through by the weight.** Since the weight $2^{-n}=(2^{-1})^n$ is nonnegative, multiplying the inequality of step 2 on the left preserves it:
\[
  \mathrm{Inf}_i[f] \;=\; 2^{-n}\sum_{x}\frac{(f(x)-f(x^i))^2}{4}\;\le\; 2^{-n}\cdot 2^n \;=\; 1,
\]
where the last equality is $(2^{-1})^n\cdot 2^n = (2^{-1}\cdot 2)^n = 1$. This is the claimed bound.
