<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 7fbbda473d03c6486194e389ee98adb205a16dd05ad1717dc337ad8e69d348f4 -->

<a id="pdf-7fbbda473d03-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# Matrix Gaussian Series & Matrix Rademacher Series

First set of matrix concentration inequalities: spectral bounds for a sum of fixed matrices, each modulated by an independent scalar random variable.

<a id="pdf-7fbbda473d03-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Definition (matrix Gaussian series).** Given a finite sequence $\{\mathbf{B}_k\}$ of fixed matrices of common dimension and a finite sequence $\{\gamma_k\}$ of independent standard normal variables, study the spectral norm of $\mathbf{Z} = \sum_k \gamma_k \mathbf{B}_k$. Captures e.g. Gaussian Wigner and Gaussian Toeplitz matrices.

A **matrix Rademacher series** replaces $\{\gamma_k\}$ by independent random signs (Rademacher variable $= \pm 1$ with equal probability); results are essentially identical.

<a id="pdf-7fbbda473d03-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
Roadmap: §matrix-gauss-rect overviews the results and their accuracy; §§gauss-matrices–toeplitz give examples; §maxqp gives a combinatorial-optimization application; §matrix-gauss-proof gives proofs; bibliographic notes conclude.

<a id="pdf-7fbbda473d03-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.95 -->
## A Norm Bound for Random Series with Matrix Coefficients

<a id="pdf-7fbbda473d03-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
For real numbers $\{b_k\}$ and independent standard normals $\{\gamma_k\}$, form $Z=\sum_k \gamma_k b_k$. The scalar Laplace transform method gives, with $v=\operatorname{Var}(Z)=\sum_k b_k^2$,
$$\Pr\{|Z|\ge t\} \le 2\exp\!\left(\frac{-t^2}{2v}\right). \tag{real-gauss}$$
This extends directly to matrices.

<a id="pdf-7fbbda473d03-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.97 -->
**Theorem (Matrix Gaussian & Rademacher Series).** Let $\{\mathbf{B}_k\}$ be fixed complex $d_1\times d_2$ matrices and $\{\gamma_k\}$ independent standard normals. Form
$$\mathbf{Z}=\sum_k \gamma_k \mathbf{B}_k. \tag{matrix-gauss-series}$$
Let the matrix variance statistic be
$$v(\mathbf{Z}) = \max\big\{\|\mathbb{E}(\mathbf{Z}\mathbf{Z}^*)\|,\ \|\mathbb{E}(\mathbf{Z}^*\mathbf{Z})\|\big\} = \max\Big\{\big\|\textstyle\sum_k \mathbf{B}_k\mathbf{B}_k^*\big\|,\ \big\|\textstyle\sum_k \mathbf{B}_k^*\mathbf{B}_k\big\|\Big\}. \tag{var}$$
Then
$$\mathbb{E}\|\mathbf{Z}\| \le \sqrt{2\,v(\mathbf{Z})\log(d_1+d_2)}, \tag{expect-rect}$$
and for all $t\ge 0$,
$$\Pr\{\|\mathbf{Z}\|\ge t\} \le (d_1+d_2)\exp\!\left(\frac{-t^2}{2v(\mathbf{Z})}\right). \tag{tail-rect}$$
The same bounds hold with $\{\gamma_k\}$ replaced by independent Rademacher variables $\{\varrho_k\}$.

<a id="pdf-7fbbda473d03-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.92 -->
$\mathbb{E}\|\mathbf{Z}\|$ is controlled by $v(\mathbf{Z})$, and $\|\mathbf{Z}\|$ has a subgaussian tail with decay rate set by $v(\mathbf{Z})$. Expression (var) follows from additivity of variance for independent sums; when the summands are Hermitian the two terms of the maximum coincide. The bound reduces to the scalar (real-gauss) when $d_1=d_2=1$; the new feature is the dimensional factor $d_1+d_2$.

<a id="pdf-7fbbda473d03-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
Figure (schematic). For a $d_1\times d_2$ matrix Gaussian series, $\Pr\{\|\mathbf{Z}\|\ge t\}\le (d_1+d_2)\exp(-t^2/(2v(\mathbf{Z})))$ gives no information below $t=\sqrt{2v(\mathbf{Z})\log(d_1+d_2)}$, which coincides with the (expect-rect) bound on $\mathbb{E}\|\mathbf{Z}\|$; beyond that level the tail decays subgaussianly with variance $\sim v(\mathbf{Z})$.

<a id="pdf-7fbbda473d03-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.92 -->
**§ Optimality of the Bounds for Matrix Gaussian Series.** Summary: the expectation bound (expect-rect) is always quite good, but the tail bound (tail-rect) is sometimes quite bad.

<a id="pdf-7fbbda473d03-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.94 -->
For a matrix Gaussian series $\mathbf{Z}$,
$$v(\mathbf{Z}) \le \mathbb{E}\|\mathbf{Z}\|^2 \le 2\,v(\mathbf{Z})\,(1+\log(d_1+d_2)). \tag{two-sided}$$
So $v(\mathbf{Z})$ is the correct scale for $\mathbb{E}\|\mathbf{Z}\|^2$.

<a id="pdf-7fbbda473d03-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
**Proof (lower bound).** By convexity of the spectral norm and Jensen's inequality,
$$\mathbb{E}\|\mathbf{Z}\|^2 = \mathbb{E}\max\{\|\mathbf{Z}\mathbf{Z}^*\|,\|\mathbf{Z}^*\mathbf{Z}\|\} \ge \max\{\|\mathbb{E}(\mathbf{Z}\mathbf{Z}^*)\|,\|\mathbb{E}(\mathbf{Z}^*\mathbf{Z})\|\} = v(\mathbf{Z}),$$
using the spectral-norm-square identity and the definition of $v(\mathbf{Z})$.

<a id="pdf-7fbbda473d03-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.95 -->
**Proof (upper bound).** By integration by parts and splitting at $E>0$,
$$\mathbb{E}\|\mathbf{Z}\|^2 = \int_0^\infty 2t\,\Pr\{\|\mathbf{Z}\|\ge t\}\,dt \le \int_0^E 2t\,dt + 2(d_1+d_2)\int_E^\infty t\,e^{-t^2/(2v(\mathbf{Z}))}dt = E^2 + 2v(\mathbf{Z})(d_1+d_2)e^{-E^2/(2v(\mathbf{Z}))},$$
bounding the probability by $1$ on $[0,E]$ and by (tail-rect) beyond. Choosing $E^2 = 2v(\mathbf{Z})\log(d_1+d_2)$ completes the proof.

<a id="pdf-7fbbda473d03-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.90 -->
Neither side of (two-sided) can be improved without more information than $v(\mathbf{Z})$: examples attain the left side ($\mathbb{E}\|\mathbf{Z}\|^2\approx v(\mathbf{Z})$, see §marcenko-pastur) and the right side ($\approx v(\mathbf{Z})\log(d_1+d_2)$, see §toeplitz) in arbitrarily large dimensions. Heuristically the $\log(d_1+d_2)$ factor appears when the coefficients $\mathbf{B}_k$ commute more, and cancellations remove it when they commute less; a simple computable criterion is an open question. Chapter intrinsic moderates but cannot remove the factor.

<a id="pdf-7fbbda473d03-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.94 -->
**Definition (weak variance).** The large-deviation behavior of $\|\mathbf{Z}\|$ is governed by
$$v_\star(\mathbf{Z}) = \sup_{\|u\|=\|w\|=1}\mathbb{E}\,|u^*\mathbf{Z}w|^2 = \sup_{\|u\|=\|w\|=1}\sum_k |u^*\mathbf{B}_k w|^2.$$
General bounds: $v_\star(\mathbf{Z}) \le v(\mathbf{Z}) \le \min\{d_1,d_2\}\cdot v_\star(\mathbf{Z})$, both saturated by examples.

<a id="pdf-7fbbda473d03-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.93 -->
The classical concentration inequality for functions of independent Gaussians [BLM13, Thm. 5.6] gives
$$\Pr\{\|\mathbf{Z}\|\ge \mathbb{E}\|\mathbf{Z}\|+t\} \le e^{-t^2/(2v_\star(\mathbf{Z}))}. \tag{gauss-concentration}$$
This bounds only deviation above the mean, not $\mathbb{E}\|\mathbf{Z}\|$. Comparing with (tail-rect) shows the tail-bound exponent is sometimes too large by a factor $\min\{d_1,d_2\}$, so Theorem (matrix-gauss-rect) can badly overestimate $\Pr\{\|\mathbf{Z}\|>t\}$ for large $t$. This is less pronounced for the matrix Chernoff and Bernstein inequalities.

<a id="pdf-7fbbda473d03-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
Matrix concentration inequalities are primarily valuable for estimating the expectation of the spectral norm (or max/min eigenvalue). Tail estimates are sometimes weak; in that case use a scalar concentration inequality to control the tails.

<a id="pdf-7fbbda473d03-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.92 -->
## Example: Some Gaussian Matrices

Tested on two well-studied Gaussian ensembles; Theorem (matrix-gauss-rect) gives reasonable but non-sharp estimates, with the advantage of applying universally. Similar conclusions for Rademacher entries.

<a id="pdf-7fbbda473d03-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.00 -->
**Gaussian Wigner matrix.** $\mathbf{W}_d$ is $d\times d$ real-symmetric with zero diagonal; the entries $\{\gamma_{jk}:1\le j<k\le d\}$ above the diagonal are independent $N(0,1)$. As a Gaussian series,
$$\mathbf{W}_d = \sum_{1\le j<k\le d}\gamma_{jk}(\mathbf{E}_{jk}+\mathbf{E}_{kj}). \tag{gauss-wigner}$$
Classical limit: $\tfrac{1}{\sqrt d}\|\mathbf{W}_d\|\to 2$ almost surely as $d\to\infty$.

**Variance computation.** Using $\mathbf{E}_{jk}\mathbf{E}_{kj}=\mathbf{E}_{jj}$ and $\mathbf{E}_{jk}\mathbf{E}_{jk}=\mathbf{0}$ (since $j<k$),
$$\sum_{1\le j<k\le d}(\mathbf{E}_{jk}+\mathbf{E}_{kj})^2 = \sum_{1\le j<k\le d}(\mathbf{E}_{jj}+\mathbf{E}_{kk}) = (d-1)\mathbf{I}_d,$$
so (terms Hermitian) $v(\mathbf{W}_d)=\|(d-1)\mathbf{I}_d\|=d-1$. Hence
$$\mathbb{E}\|\mathbf{W}_d\| \le \sqrt{2(d-1)\log(2d)}. \tag{gauss-wigner-est}$$
This overestimates $\|\mathbf{W}_d\|$ by a factor $\approx\sqrt{0.5\log d}$, but takes only two lines versus the classical moment/combinatorial argument.

<a id="pdf-7fbbda473d03-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.00 -->
**Rectangular Gaussian matrix.** $\mathbf{G}$ is $d_1\times d_2$ with independent standard normal entries $\{\gamma_{jk}\}$, expressed as the Gaussian series
$$\mathbf{G} = \sum_{j=1}^{d_1}\sum_{k=1}^{d_2}\gamma_{jk}\mathbf{E}_{jk}. \tag{mp-gauss-series}$$
(Analysis continues beyond the supplied text.)

<a id="pdf-7fbbda473d03-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
For the $d_1\times d_2$ Gaussian matrix $\mtx{G}$, a classical estimate gives, eqn (gauss-rect-true), $\Expect\norm{\mtx{G}}\le\sqrt{d_1}+\sqrt{d_2}$. This is sharp as $d_1,d_2\to\infty$ with $d_1/d_2\to$ const.

<a id="pdf-7fbbda473d03-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
**Computation.** Using the series (mp-gauss-series): $\sum_{j,k}\mathbf{E}_{jk}\mathbf{E}_{jk}^\adj=d_2\,\Id_{d_1}$ and $\sum_{j,k}\mathbf{E}_{jk}^\adj\mathbf{E}_{jk}=d_1\,\Id_{d_2}$. Hence $v(\mtx{G})=\max\{\norm{d_2\Id_{d_1}},\norm{d_1\Id_{d_2}}\}=\max\{d_1,d_2\}$. Theorem (matrix-gauss-rect) gives, eqn (gauss-rect-est), $\Expect\norm{\mtx{G}}\le\sqrt{2\max\{d_1,d_2\}\log(d_1+d_2)}$. Leading term is right since $\sqrt{d_1}+\sqrt{d_2}\le 2\sqrt{\max\{d_1,d_2\}}\le 2(\sqrt{d_1}+\sqrt{d_2})$; the log factor is spurious but small.

<a id="pdf-7fbbda473d03-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.98 -->
**Section (sec:rdm-sign-mtx).** Example: Matrices with Randomly Signed Entries.

<a id="pdf-7fbbda473d03-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.93 -->
**Setup.** Fixed $d_1\times d_2$ real matrix $\mtx{B}$, independent Rademacher family $\{\varrho_{jk}\}$, and $\mtx{B}_{\pm}=\sum_{j,k}\varrho_{jk}b_{jk}\mathbf{E}_{jk}$ (signs of entries randomly flipped). Known bound, eqn (rdm-sign-matrix-true): $\Expect\norm{\mtx{B}_{\pm}}\le \mathrm{Const}\cdot v^{1/2}\cdot\log^{1/4}\min\{d_1,d_2\}$, where, eqn (rdm-sign-matrix-var), $v=\max\{\max_j\norm{\vct{b}_{j:}}^2,\ \max_k\norm{\vct{b}_{:k}}^2\}$ ($\vct{b}_{j:}$ row $j$, $\vct{b}_{:k}$ column $k$). So the expected norm is comparable to the largest row/column $\ell_2$ norm; a matching lower bound holds in some cases.

<a id="pdf-7fbbda473d03-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.94 -->
**Computation.** $\sum_{j,k}(b_{jk}\mathbf{E}_{jk})(b_{jk}\mathbf{E}_{jk})^\adj=\mathrm{diag}(\norm{\vct{b}_{j:}}^2)$ and $\sum_{j,k}(b_{jk}\mathbf{E}_{jk})^\adj(b_{jk}\mathbf{E}_{jk})=\mathrm{diag}(\norm{\vct{b}_{:k}}^2)$. By (matrix-gauss-rect-var-calc), $v(\mtx{B}_{\pm})=\max\{\max_j\norm{\vct{b}_{j:}}^2,\max_k\norm{\vct{b}_{:k}}^2\}=v$. Theorem (matrix-gauss-rect) yields, eqn (rdm-sign-matrix-est), $\Expect\norm{\mtx{B}_{\pm}}\le\sqrt{2v(\mtx{B}_{\pm})\log(d_1+d_2)}$, matching the true bound up to the logarithmic factor and requiring far less arithmetic than the specialized combinatorial argument.

<a id="pdf-7fbbda473d03-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.98 -->
**Section (sec:toeplitz).** Example: Gaussian Toeplitz Matrices (applications in signal processing).

<a id="pdf-7fbbda473d03-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.92 -->
**Setup.** The unsymmetric $d\times d$ Gaussian Toeplitz matrix $\mtx{\Gamma}_d$ has independent standard normal entries $\{\gamma_k\}$ populating the first row and column, constant along each diagonal: entry $(i,j)$ equals $\gamma_{j-i}$, with $\gamma_0$ on the main diagonal, $\gamma_1,\dots,\gamma_{d-1}$ above and $\gamma_{-1},\dots,\gamma_{-(d-1)}$ below.

<a id="pdf-7fbbda473d03-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.94 -->
**Representation.** With $\{\gamma_k\}$ independent standard normals, eqn (gauss-toeplitz-cpt): $\mtx{\Gamma}_d=\gamma_0\Id+\sum_{k=1}^{d-1}\gamma_k\mtx{C}^k+\sum_{k=1}^{d-1}\gamma_{-k}(\mtx{C}^k)^\adj$, where $\mtx{C}\in\mathbb{M}_d$ is the shift-up operator (superdiagonal of ones). $\mtx{C}^k$ shifts up by $k$ (zeros at bottom); $(\mtx{C}^k)^\adj$ shifts down by $k$ (zeros at top).

<a id="pdf-7fbbda473d03-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.93 -->
**Computation.** $(\mtx{C}^k)(\mtx{C}^k)^\adj=\sum_{j=1}^{d-k}\mathbf{E}_{jj}$ and $(\mtx{C}^k)^\adj(\mtx{C}^k)=\sum_{j=k+1}^{d}\mathbf{E}_{jj}$; both variance terms coincide. Summing squared coefficients: $\Id+\sum_{k=1}^{d-1}[(\mtx{C}^k)(\mtx{C}^k)^\adj+(\mtx{C}^k)^\adj(\mtx{C}^k)]=\sum_{j=1}^d(1+(d-j)+(j-1))\mathbf{E}_{jj}=d\,\Id_d$. Thus $v(\mtx{\Gamma}_d)=\norm{d\Id_d}=d$, and, eqn (gauss-toeplitz-est), $\Expect\norm{\mtx{\Gamma}_d}\le\sqrt{2d\log(2d)}$. This has the right scaling; using [SV13, Thm.~1] one gets $0.8288\le \Expect\norm{\mtx{\Gamma}_d}/\sqrt{2d\log(2d)}\le 1$ as $d\to\infty$ (within 21% of optimal constant).

<a id="pdf-7fbbda473d03-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.98 -->
**Section (sec:maxqp).** Application: Rounding for the MaxQP Relaxation.

<a id="pdf-7fbbda473d03-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
Relaxation enlarges a hard constraint set to make the problem tractable, then randomized rounding maps the solution back; if rounding barely changes the objective, the rounded point is a good solution. MaxQP has a matrix decision variable, maximizing a quadratic form subject to convex quadratic constraints and a spectral norm constraint; the target solution $\mtx{B}$ is $d_1\times d_2$ with $\norm{\mtx{B}}\le 1$.

<a id="pdf-7fbbda473d03-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.93 -->
**Analysis.** The relaxation returns matrices $\{\mtx{B}_k:k=1,\dots,n\}$ satisfying, eqn (maxqp-constraint), $\sum_{k=1}^n\mtx{B}_k\mtx{B}_k^\adj\psdle\Id_{d_1}$ and $\sum_{k=1}^n\mtx{B}_k^\adj\mtx{B}_k\psdle\Id_{d_2}$. Rounding forms $\mtx{Z}=\alpha\sum_{k=1}^n\varrho_k\mtx{B}_k$ with Rademacher $\{\varrho_k\}$ and $\alpha>0$. Theorem (matrix-gauss-rect): $\Expect\norm{\mtx{Z}}\le\sqrt{2v(\mtx{Z})\log(d_1+d_2)}$ where $v(\mtx{Z})=\alpha^2\max\{\norm{\sum_k\mtx{B}_k\mtx{B}_k^\adj},\norm{\sum_k\mtx{B}_k^\adj\mtx{B}_k}\}\le\alpha^2$. Choosing $\alpha^2=1/(2\log(d_1+d_2))$ gives $\Expect\norm{\mtx{Z}}\le 1$; tail bound (matrix-gauss-tail-rect) gives high-probability control.

<a id="pdf-7fbbda473d03-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
Since $\alpha$ is small relative to $d_1,d_2,n$, scaling changes the objective little; the method yields a feasible MaxQP point whose objective is within a factor $\sqrt{2\log(d_1+d_2)}$ of the optimum.

<a id="pdf-7fbbda473d03-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.96 -->
**Section (sec:matrix-gauss-proof).** Analysis of Matrix Gaussian & Rademacher Series — proof of Theorem (matrix-gauss-rect). Subsection: Random Series with Hermitian Coefficients (Hermitian matrices are the natural setting).

<a id="pdf-7fbbda473d03-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.97 -->
**Theorem (Matrix Gaussian & Rademacher Series: Hermitian Case).** For a finite sequence $\{\mtx{A}_k\}$ of fixed $d$-dimensional Hermitian matrices and independent standard normals $\{\gamma_k\}$, set $\mtx{Y}=\sum_k\gamma_k\mtx{A}_k$. The variance statistic, eqn (matrix-gauss-sigma2), is $v(\mtx{Y})=\norm{\Expect\mtx{Y}^2}=\norm{\sum_k\mtx{A}_k^2}$. Then, eqn (matrix-gauss-upper-expect), $\Expect\lambda_{\max}(\mtx{Y})\le\sqrt{2v(\mtx{Y})\log d}$; and for all $t\ge0$, eqn (matrix-gauss-upper-tail), $\Prob{\lambda_{\max}(\mtx{Y})\ge t}\le d\exp(-t^2/(2v(\mtx{Y})))$. The same bounds hold for independent Rademacher variables.

<a id="pdf-7fbbda473d03-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.93 -->
Since $\mtx{Y}$ has zero mean, $v(\mtx{Y})$ matches the general formula (matrix-variance-herm), the coefficient expression following by additivity (indep-sum-herm). Because $-\mtx{Y}\overset{d}{=}\mtx{Y}$: eqn (matrix-gauss-lower-expect) $\Expect\lambda_{\min}(\mtx{Y})=-\Expect\lambda_{\max}(\mtx{Y})\ge-\sqrt{2v(\mtx{Y})\log d}$, and eqn (matrix-gauss-lower-tail) $\Prob{\lambda_{\min}(\mtx{Y})\le-t}\le d\exp(-t^2/(2v(\mtx{Y})))$ for $t\ge0$. Key difference from the general case: the Hermitian result bounds extreme eigenvalues (one-sided tails) rather than the norm; separating the two tails matters for matrices whose min/max eigenvalues behave differently.

<a id="pdf-7fbbda473d03-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.94 -->
**Subsection.** Proof strategy for Theorem (matrix-gauss-herm): apply the master bounds Theorem (master-ineq) for independent sums, which requires the cgf of a fixed matrix modulated by a Gaussian variable.

<a id="pdf-7fbbda473d03-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.97 -->
**Lemma (Gaussian $\times$ Matrix: Mgf and Cgf).** For fixed Hermitian $\mtx{A}$ and standard normal $\gamma$, for $\theta\in\mathbb{R}$: $\Expect e^{\gamma\theta\mtx{A}}=e^{\theta^2\mtx{A}^2/2}$ and $\log\Expect e^{\gamma\theta\mtx{A}}=\tfrac{\theta^2}{2}\mtx{A}^2$.

<a id="pdf-7fbbda473d03-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.90 -->
**Proof.** Take $\theta=1$ by absorbing $\theta$ into $\mtx{A}$. Standard normal moments: $\Expect\gamma^{2q+1}=0$ (symmetry) and $\Expect\gamma^{2q}=(2q)!/(2^q q!)$ for $q=0,1,2,\dots$; the even moments follow from an integration-by-parts recursion. [Proof continues beyond the supplied pages.]

<a id="pdf-7fbbda473d03-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Proof (continued).** The matrix mgf equals $\Expect e^{\gamma A} = I + \sum_{q=1}^\infty \frac{\Expect(\gamma^{2q})}{(2q)!}A^{2q} = I + \sum_{q=1}^\infty \frac{1}{q!}(A^2/2)^q = e^{A^2/2}$. Odd-order terms vanish under expectation in the matrix-exponential series (eqn:exp-series). The cgf is obtained as the logarithm of the mgf, using that the matrix logarithm inverts the matrix exponential (eqn:log-defn). $\square$

<a id="pdf-7fbbda473d03-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Proof (Theorem matrix-gauss-herm, Gaussian case).** For Hermitian $\{A_k\}$ of dimension $d$ and independent standard normals $\{\gamma_k\}$, set $Y = \sum_k \gamma_k A_k$.

*Expectation bound (eqn:matrix-gauss-upper-expect).* The master expectation bound (eqn:master-upper-expect, Thm matrix-master-ineq) gives
$$\Expect \lambda_{\max}(Y) \le \inf_{\theta>0}\tfrac{1}{\theta}\log\trace\exp\!\big(\sum_k \log\Expect e^{\gamma_k\theta A_k}\big).$$
Substituting the cgf from Lemma matrix-gauss-mgf gives exponent $\frac{\theta^2}{2}\sum_k A_k^2$; bounding $\trace$ by $d\,\lambda_{\max}$; applying the Spectral Mapping Theorem (Prop spectral-mapping); and identifying $v(Y)$ via eqn:matrix-gauss-sigma2 yields
$$\Expect \lambda_{\max}(Y) \le \inf_{\theta>0}\tfrac{1}{\theta}\big[\log d + \tfrac{\theta^2 v(Y)}{2}\big].$$
The infimum is attained at $\theta = \sqrt{2\,v(Y)^{-1}\log d}$, giving eqn:matrix-gauss-upper-expect.

*Tail bound (eqn:matrix-gauss-upper-tail).* The master tail bound (eqn:master-upper-tail) gives, by the same steps,
$$\Prob{\lambda_{\max}(Y)\ge t} \le d\,\inf_{\theta>0} e^{-\theta t + \theta^2 v(Y)/2}.$$
The infimum is attained at $\theta = t/v(Y)$, giving eqn:matrix-gauss-upper-tail. $\square$

<a id="pdf-7fbbda473d03-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.98 -->
## Analysis for Hermitian Rademacher Series

<a id="pdf-7fbbda473d03-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
**Lemma (Rademacher × Matrix: Mgf and Cgf).** For fixed Hermitian $A$ and a Rademacher variable $\varrho$, for all $\theta\in\mathbb{R}$:
$$\Expect e^{\varrho\theta A} \preceq e^{\theta^2 A^2/2}, \qquad \log\Expect e^{\varrho\theta A} \preceq \tfrac{\theta^2}{2}A^2.$$

<a id="pdf-7fbbda473d03-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.96 -->
**Proof.** Scalar inequality (eqn:cosh-exp): $\cosh(a) = \sum_{q\ge0}\frac{a^{2q}}{(2q)!} \le \sum_{q\ge0}\frac{a^{2q}}{2^q q!} = e^{a^2/2}$ for $a\in\mathbb{R}$, since $(2q)! \ge 2^q q!$. Taking $\theta=1$: $\Expect e^{\varrho A} = \tfrac12 e^{A} + \tfrac12 e^{-A} = \cosh(A) \preceq e^{A^2/2}$ by the Transfer Rule (eqn:transfer-rule) applied to (eqn:cosh-exp). For the cgf: $\log\Expect e^{\varrho A} = \log\cosh(A) \preceq \tfrac12 A^2$, via the Transfer Rule applied to $\log\cosh(a) \le a^2/2$ (a consequence of eqn:cosh-exp). $\square$

<a id="pdf-7fbbda473d03-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.95 -->
**Proof (Theorem matrix-gauss-herm, Rademacher case).** For Hermitian $\{A_k\}$ and independent Rademacher $\{\varrho_k\}$, set $Y = \sum_k \varrho_k A_k$. The argument matches the Gaussian case; only the inequality
$$\trace\exp\!\big(\sum_k \log\Expect e^{\varrho_k\theta A_k}\big) \le \trace\exp\!\big(\tfrac{\theta^2}{2}\sum_k A_k^2\big)$$
needs justification. It follows by inserting the semidefinite cgf bound (Lemma matrix-rad-mgf) and using monotonicity of the trace exponential in the semidefinite order (eqn:exp-trace-monotone). $\square$

<a id="pdf-7fbbda473d03-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.98 -->
## Analysis of Matrix Series with Rectangular Coefficients (sec:matrix-gauss-proof-rect)

<a id="pdf-7fbbda473d03-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
**Proof (Theorem matrix-gauss-rect).** For $d_1\times d_2$ complex $\{B_k\}$ and independent $\{\zeta_k\}$ (each standard normal or Rademacher), use the Hermitian dilation (Def herm-dilation) $\coll{H}: B \mapsto \begin{bmatrix} 0 & B \\ B^\adj & 0\end{bmatrix}$. Form $Z = \sum_k \zeta_k B_k$ and $Y = \coll{H}(Z) = \sum_k \zeta_k \coll{H}(B_k)$ (real-linearity of $\coll{H}$). Then $Y$ is a Hermitian series, analyzable by Theorem matrix-gauss-herm. Using that the dilation preserves spectral data (eqn:herm-dilation-norm), $\norm{Z} = \lambda_{\max}(\coll{H}(Z)) = \lambda_{\max}(Y)$; and by eqn:var-stat-dilation, $v(Y) = v(\coll{H}(Z)) = v(Z)$ (matching eqn:matrix-gauss-sigma2-rect / eqn:matrix-variance-rect). Applying Theorem matrix-gauss-herm yields Theorem matrix-gauss-rect. $\square$

<a id="pdf-7fbbda473d03-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.98 -->
# Notes

<a id="pdf-7fbbda473d03-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.90 -->
**Notes — Matrix Gaussian and Rademacher Series.** Theorems matrix-gauss-rect and matrix-gauss-herm first appeared in their present form in Tro11 (User-Friendly, FOCM). Oliveira (Oli10) established the mgf bounds of Lemmas matrix-gauss-mgf and matrix-rad-mgf and, improving on Ahlswede & Winter (AW02), obtained a bound similar to Theorem matrix-gauss-herm with worse constants but better dimensional dependence (depending on the number of summands). Minor improvements to the dimensional factor are discussed in the Intrinsic-dimension chapter.

<a id="pdf-7fbbda473d03-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
**Notes — Noncommutative Khintchine Inequality** (sec:nc-khintchine). Due to Lust-Piquard (LP86; follow-up LPP91). For a Hermitian Rademacher series $Y = \sum_k \varrho_k A_k$, the inequality states (eqn:nc-khintchine)
$$\Expect\trace[Y^{2q}] \le C_{2q}\,\trace\big[(\Expect Y^2)^q\big], \quad q=1,2,3,\dots,$$
with optimal constant $C_{2q} = (2q)!/(2^q q!)$ (Buc01, Buc05). An elementary proof is in MJCFT12 (Cor. 7.3). Theorem matrix-gauss-herm is the exponential-moment analog of this polynomial-moment bound, which is somewhat stronger; see Tro11 §4.

<a id="pdf-7fbbda473d03-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.90 -->
**Notes — Application to Random Matrices.** Results like Theorem matrix-gauss-herm and eqn:nc-khintchine have long been applied to random matrices. Earliest applications are in geometric functional analysis: Rudelson (Rud99), on a suggestion of Pisier, used the noncommutative Khintchine inequality for covariance estimation, spawning variants (e.g., RV07); powerful but effortful.

<a id="pdf-7fbbda473d03-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**Notes — Application to Random Matrices (continued).** Noncommutative probability theorists independently recognized the power of noncommutative moment inequalities (e.g., JX08), though that literature is technically formidable. Ahlswede & Winter (AW02) produced the first "packaged" matrix concentration inequalities (early applications in quantum information and random graph theory); Gross (Gro11) popularized them in signal processing and statistics. Optimal matrix concentration results were then reached by Oli10 and Tro11.

<a id="pdf-7fbbda473d03-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.90 -->
**Notes — Wigner and Marčenko–Pastur.** Wigner matrices arose in nuclear physics (Meh04 §1.1). Wigner (Wig55) showed the limiting spectral distribution follows the semicircle law (overviews: Tao12 §2.4; Bai & Silverstein BS10 Chap. 2). The Bai–Yin law (BY93) states that, up to scaling, the maximum eigenvalue of a Wigner matrix converges almost surely to $2$ (see Tao12 §2.3; BS10 Chap. 5). The Gaussian Wigner analysis via Theorem matrix-gauss-herm follows Tro11 §4. For rectangular Gaussian matrices, Marčenko & Pastur (MP67) established the limiting distribution of squared singular values; Bai–Yin (BY93) gives the a.s. limit of the largest singular value; the expectation bound (eqn:gauss-rect-true) appears in Davidson & Szarek (DS02), derived from Gaussian-process comparison theorems (Fernique Fer75, Gordon Gor85). Approach via Theorem matrix-gauss-rect follows Tro11 §4.

<a id="pdf-7fbbda473d03-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
**Notes — Randomly Signed Matrices.** The bound eqn:rdm-sign-matrix-true is due to Seginer (Seg00). Latała (Lat05) bounds the expected norm of a Gaussian matrix with nonuniform-variance entries; Riemer & Schütt (RS13) extended these; Bandeira & Van Handel (BV14) gave an elegant new proof of Seginer's result via a general theorem for independent-entry random matrices. The analysis here (via Theorem matrix-gauss-rect) follows Tro11 §4.

<a id="pdf-7fbbda473d03-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.90 -->
**Notes — Gaussian Toeplitz Matrices.** Bryc, Dembo & Jiang (BDJ06) found the limiting spectral distribution of a symmetric Toeplitz matrix with iid entries; Meckes (Mec07) gave the first expected-norm bound (iid entries); Sen & Virág (SV13) computed the limiting expected norm for identical second-order statistics. The analysis here (via Theorem matrix-gauss-rect) is new; the lower bound for $\Expect\norm{\Gamma_d}$ follows from Sen & Virág. No analysis is known for differing-variance entries, though it would follow from a simple modification of the argument in §toeplitz.

<a id="pdf-7fbbda473d03-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.90 -->
**Notes — Relaxation and Rounding of MaxQP.** Semidefinite relaxation and rounding for MaxQP is due to Nemirovski (Nem07), who used matrix moment calculations but missed the sharpest bound. So (So09) showed matrix moment inequalities give an optimal result and apply to robust optimization. The presentation here (via Theorem matrix-gauss-rect) is essentially equivalent to So09, with slightly better constants.
