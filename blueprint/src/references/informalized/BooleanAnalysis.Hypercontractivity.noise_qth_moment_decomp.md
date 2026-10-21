<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: BooleanAnalysis.Hypercontractivity.noise_qth_moment_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Moment decomposition of the noise operator across the last coordinate

**Claim.** Let $f:\{0,1\}^{n+1}\to\mathbb{R}$ be a Boolean function, let $\rho\in\mathbb{R}$, and let $q$ be a nonnegative integer. Write $A$ for the average of $f$ over its last coordinate and $D$ for its half-difference, so that $A(x)=(f(x,0)+f(x,1))/2$ and $D(x)=(f(x,0)-f(x,1))/2$ on $\{0,1\}^n$. Then the $q$-th moment of $T_\rho f$ under the uniform measure on $\{0,1\}^{n+1}$ equals the uniform expectation over $\{0,1\}^n$ of the symmetric average
\[
  \frac{\bigl(T_\rho A(x)+\rho\,T_\rho D(x)\bigr)^q+\bigl(T_\rho A(x)-\rho\,T_\rho D(x)\bigr)^q}{2},
\]
where on the right the noise operator acts on functions of $n$ variables.

**Proof.** The proof does not expand Fourier coefficients. Instead it applies a purely algebraic moment-splitting identity to the *already noised* function $g:=T_\rho f$, and then feeds in one structural fact: the noise operator interacts with the average/difference decomposition of the last coordinate in a controlled way, where the difference part picks up an extra factor of $\rho$.

For a function $g$ on $\{0,1\}^{n+1}$, write $\bar g(x)=(g(x,0)+g(x,1))/2$ and $\tilde g(x)=(g(x,0)-g(x,1))/2$ for its average and half-difference over the last coordinate, so that $g(x,0)=\bar g(x)+\tilde g(x)$ and $g(x,1)=\bar g(x)-\tilde g(x)$.

1. **The algebraic decomposition applied to $g=T_\rho f$.** The general moment-splitting identity (`qth_moment_decomp`) states that for any $g:\{0,1\}^{n+1}\to\mathbb{R}$,
\[
  \mathop{\mathbb{E}}_{x\in\{0,1\}^{n+1}}\!\bigl[g(x)^q\bigr]
  =\mathop{\mathbb{E}}_{x\in\{0,1\}^{n}}\!\left[\frac{(\bar g(x)+\tilde g(x))^q+(\bar g(x)-\tilde g(x))^q}{2}\right].
\]
This holds because the uniform average over $\{0,1\}^{n+1}$ factors as the uniform average over the first $n$ coordinates of the average over the last bit $b\in\{0,1\}$; and for fixed $x$ the inner average of $g(x,b)^q$ over $b$ is $\tfrac12\bigl(g(x,0)^q+g(x,1)^q\bigr)=\tfrac12\bigl((\bar g+\tilde g)^q+(\bar g-\tilde g)^q\bigr)$. Taking $g=T_\rho f$ gives the left-hand side we want; it remains to identify $\bar g$ and $\tilde g$ for this particular $g$.

2. **How the noise operator acts across the last coordinate.** The structural lemma (`noiseOp_snoc`) evaluates $T_\rho f$ at a point whose last coordinate is $b$: for $x\in\{0,1\}^n$ and $b\in\{0,1\}$,
\[
  (T_\rho f)(x,b)=T_\rho A(x)+\sigma(b)\,\rho\,T_\rho D(x),
  \qquad \sigma(0)=+1,\ \sigma(1)=-1,
\]
with $A=\mathrm{avg}$ and $D=\mathrm{half\text{-}difference}$ of $f$ over the last coordinate as above, and the noise operators on the right acting on functions of $n$ variables. The point is the factor $\rho$ in front of the difference term: the half-difference $D$ is the part of $f$ carried by Fourier characters that contain the last index, and the noise operator weights a character $\chi_S$ by $\rho^{|S|}$, so that extra index contributes exactly one additional factor of $\rho$.

3. **Reading off $\bar g$ and $\tilde g$.** Setting $b=0$ and $b=1$ in Step 2 gives $g(x,0)=T_\rho A(x)+\rho\,T_\rho D(x)$ and $g(x,1)=T_\rho A(x)-\rho\,T_\rho D(x)$. Hence
\[
  \bar g(x)=\frac{g(x,0)+g(x,1)}{2}=T_\rho A(x),
  \qquad
  \tilde g(x)=\frac{g(x,0)-g(x,1)}{2}=\rho\,T_\rho D(x).
\]
Equivalently, averaging over the last coordinate commutes with the noise operator, while the half-difference commutes with it up to the scalar $\rho$.

4. **Conclusion.** Substituting $\bar g=T_\rho A$ and $\tilde g=\rho\,T_\rho D$ into the identity of Step 1, the two summands become $\bar g+\tilde g=T_\rho A+\rho\,T_\rho D$ and $\bar g-\tilde g=T_\rho A-\rho\,T_\rho D$, which is exactly the claimed decomposition. $\qquad\blacksquare$

**Key facts.** `BooleanAnalysis.Hypercontractivity.qth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc`.
