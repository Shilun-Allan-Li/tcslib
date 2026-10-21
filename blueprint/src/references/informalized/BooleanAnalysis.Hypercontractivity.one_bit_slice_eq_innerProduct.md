<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: BooleanAnalysis.Hypercontractivity.one_bit_slice_eq_innerProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Slice Sum Equals a One-Bit Noise Inner Product

**Claim.** Fix $n$, a real $\rho$, Boolean functions $f,g:\{0,1\}^{n+1}\to\mathbb R$, and points $x',y'\in\{0,1\}^n$. Writing $(x',b)$ for the point of $\{0,1\}^{n+1}$ obtained by appending the bit $b$ to $x'$, and $\sigma$ for the sign encoding $\sigma(0)=1$, $\sigma(1)=-1$, the weighted double sum $\tfrac12\sum_{b,b'}\tfrac{1+\rho\,\sigma(b)\sigma(b')}{2}\,f(x',b)\,g(y',b')$ equals the inner product $\langle F,\,T_\rho G\rangle$ taken on the one-dimensional cube $\{0,1\}^1$, where $F(t)=f(x',t_0)$ and $G(t)=g(y',t_0)$ are the one-bit slices through $f$ and $g$ and $T_\rho$ is the spectral noise operator. In short: the Boolean-noise weighting of a $2\times2$ table of function values is exactly the one-bit noisy inner product of its row and column slices.

**Proof.** This is a finite identity: the one-dimensional cube $\{0,1\}^1$ has only two points, and the right-hand side has only two Fourier modes, so both sides reduce to the same polynomial in four real numbers. The Lean proof makes exactly this reduction — it unfolds every definition, enumerates the two subsets of $[1]$ and the two points of the cube by hand, and matches the two resulting expressions by ring arithmetic. We follow that route.

**1. The four values.** Abbreviate the entries of the $2\times2$ table by
$$f_0=f(x',0),\quad f_1=f(x',1),\quad g_0=g(y',0),\quad g_1=g(y',1),$$
where $0$ and $1$ are the two bits appended as the last coordinate. The slice $F:\{0,1\}^1\to\mathbb R$ takes the value $f_0$ at the point whose single coordinate is $0$ and $f_1$ at the point whose coordinate is $1$; likewise $G$ takes values $g_0$ and $g_1$. Throughout, $\sigma(0)=1$ and $\sigma(1)=-1$.

**2. The left-hand side.** Expanding the double sum over the four choices of $(b,b')$ and using $\sigma(0)\sigma(0)=\sigma(1)\sigma(1)=1$ and $\sigma(0)\sigma(1)=\sigma(1)\sigma(0)=-1$, the four weights $\tfrac{1+\rho\sigma(b)\sigma(b')}{2}$ are $\tfrac{1+\rho}{2}$ on the diagonal and $\tfrac{1-\rho}{2}$ off it. Hence
\[
\text{LHS}=\frac12\cdot\frac12\Big[(1+\rho)(f_0g_0+f_1g_1)+(1-\rho)(f_0g_1+f_1g_0)\Big]
=\frac14\Big[(1+\rho)(f_0g_0+f_1g_1)+(1-\rho)(f_0g_1+f_1g_0)\Big].
\]

**3. The two Fourier modes of $G$.** The subsets of the one-element index set $[1]=\{0\}$ are exactly $\emptyset$ and $\{0\}$; this enumeration is the one explicit case split the Lean proof performs on the index side. The corresponding characters are $\chi_\emptyset\equiv 1$ and $\chi_{\{0\}}(t)=\sigma(t_0)$, which is $+1$ at the point with coordinate $0$ and $-1$ at the point with coordinate $1$. Since the inner product on $\{0,1\}^1$ carries the uniform weight $2^{-1}=\tfrac12$, the two Fourier coefficients of $G$ are
\[
\widehat G(\emptyset)=\tfrac12(g_0+g_1),\qquad
\widehat G(\{0\})=\tfrac12(g_0-g_1).
\]

**4. The noise operator applied to $G$.** By definition $T_\rho G=\sum_{S}\rho^{|S|}\widehat G(S)\chi_S$, so with only the two modes above,
\[
T_\rho G=\widehat G(\emptyset)\cdot 1+\rho\,\widehat G(\{0\})\,\chi_{\{0\}}.
\]
Evaluating at the two points of the cube gives
\[
T_\rho G\big|_{0}=\tfrac12\big[(1+\rho)g_0+(1-\rho)g_1\big],\qquad
T_\rho G\big|_{1}=\tfrac12\big[(1-\rho)g_0+(1+\rho)g_1\big].
\]

**5. The right-hand side.** The inner product on $\{0,1\}^1$ is again a uniform average over the two points, $\langle F,T_\rho G\rangle=\tfrac12\big(f_0\,T_\rho G|_0+f_1\,T_\rho G|_1\big)$. Substituting the values from Step 4,
\[
\text{RHS}=\frac12\cdot\frac12\Big[f_0\big((1+\rho)g_0+(1-\rho)g_1\big)+f_1\big((1-\rho)g_0+(1+\rho)g_1\big)\Big],
\]
which rearranges to the identical expression obtained for the LHS in Step 2. This final matching is the ring computation that closes the main goal.

**6. The bookkeeping side goals.** Splitting each two-element sum (over the subsets $\{\emptyset,\{0\}\}$ and over the two cube points) requires knowing the two elements are distinct. Distinctness of $\emptyset$ and $\{0\}$ is immediate; distinctness of the two cube points — the constant-$0$ and constant-$1$ functions on one coordinate — is checked by evaluating both at coordinate $0$, where they disagree. These are the only residual obligations, and they are purely combinatorial. $\qquad\blacksquare$
