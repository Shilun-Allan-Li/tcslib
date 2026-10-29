<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.two_func_hyp_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Two-function hypercontractivity on the zero-dimensional cube

**Claim.** Fix exponents $p,q\ge 1$ and an arbitrary noise parameter $\rho\in\mathbb R$. For any two real-valued functions $f,g$ on the zero-dimensional cube $\{0,1\}^0$, the inner product of $f$ with the noise-operator image $T_\rho g$ is bounded by the product of the $L^p$-norm of $f$ and the $L^q$-norm of $g$ taken under the uniform measure:
\[
\langle f, T_\rho g\rangle \;\le\; \bigl(\mathbb E\bigl[|f|^p\bigr]\bigr)^{1/p}\,\bigl(\mathbb E\bigl[|g|^q\bigr]\bigr)^{1/q}.
\]
This is the base case $d=0$ of the two-function hypercontractivity inequality.

**Proof.** The point of this base case is that in dimension zero everything degenerates: the cube is a single point, the noise operator is the identity, and the inequality collapses to the triviality $ab\le|a|\,|b|$. The proof simply makes these degeneracies explicit, in order.

1. **The cube is a single point.** The set $\{0,1\}^0$ of maps $\mathrm{Fin}\,0\to\{0,1\}$ has exactly one element — the empty function $*$ — since there are no coordinates to assign. Write $a:=f(*)$ and $b:=g(*)$ for the two values that matter. Because $\mathrm{Fin}\,0$ is empty, *any* point $x$ of the cube equals $*$; this fact is recorded once and then used throughout to replace $f$ and $g$ by the constants $a$ and $b$.

2. **Expectation is evaluation at the point.** The uniform weight is $\mathrm{uniformWeight}(0)=(1/2)^0=1$, and a sum over the cube has only the single term indexed by $*$, so $\mathbb E[h]=1\cdot h(*)=h(*)$ for every $h$. In particular $\mathbb E[|f|^p]=|a|^p$ and $\mathbb E[|g|^q]=|b|^q$, and the inner product unfolds to $\langle f,T_\rho g\rangle=\mathbb E[f\cdot T_\rho g]=f(*)\,(T_\rho g)(*)$.

3. **The noise operator acts as the identity (the key step, `h_noiseOp`).** By definition $T_\rho g(x)=\sum_{S\subseteq[0]}\rho^{|S|}\,\widehat g(S)\,\chi_S(x)$. The only subset of $[0]=\varnothing$ is $S=\varnothing$, so the sum over all subsets collapses to this single term. There $\rho^{|\varnothing|}=\rho^0=1$ and the character $\chi_\varnothing(x)=\prod_{i\in\varnothing}(\pm1)=1$ is the empty product, so $T_\rho g(x)=\widehat g(\varnothing)$. Finally the empty Fourier coefficient is just the mean: $\widehat g(\varnothing)=\langle g,\chi_\varnothing\rangle=\mathbb E[g\cdot 1]=\mathbb E[g]=g(*)$. Since every $x$ equals $*$, this gives $T_\rho g(x)=g(x)$ for all $x$; the noise parameter $\rho$ has dropped out entirely. (This is the mechanism behind hypercontractivity base cases: with no coordinates there is no high-frequency mass for $T_\rho$ to shrink.)

4. **Reduction of the norms.** Substituting step 3 into step 2, the left-hand side becomes $f(*)\,g(*)=ab$. On the right, each factor simplifies by the power law for real exponents: $\bigl(|a|^p\bigr)^{1/p}=|a|^{\,p\cdot(1/p)}=|a|^1=|a|$, using that $|a|\ge 0$ (so the exponent law applies) and that $p\cdot(1/p)=1$ because $p\ge 1>0$. Likewise the second factor is $|b|$. The goal is now exactly
\[
ab\;\le\;|a|\,|b|.
\]

5. **The elementary inequality.** This holds for all reals $a,b$ since $ab\le|ab|=|a|\,|b|$. The proof dispatches it by splitting into the four sign cases for $a$ and $b$ — in each case $|a|=\pm a$ and $|b|=\pm b$ are known constants, and the inequality is linear/quadratic bookkeeping — completing the argument.
