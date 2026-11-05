<!-- generated-by: manually curated chapter-11 statement index -->
<!-- source-pdf-sha256: 8b2c50cf9621a397e8a43be5883167d7a1f33b2bb96f0683b7b0709539ec807f -->
<!-- scope: starting-slice statement index, not a full cleaned transcription or approved proofmatch run -->

<a id="pdf-8b2c50cf9621-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=1.00 -->
# Chapter 11. Gaussian space and Invariance Principles

Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
May 2021 arXiv edition, printed pp. 327–370. PDF page numbers here are one-based;
printed page number equals PDF page number plus 326.

This is a curated statement index for the initial formalization slice. The paired
`.raw.md` retains the full extraction, including exercises and notes, with unresolved
glyph/layout problems. Definitions and statements below are mathematical paraphrases;
the supplied PDF is authoritative. The index and independent model review do not
constitute an approved proofmatch comparison or a kernel proof.

<a id="pdf-8b2c50cf9621-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=1.00 -->
## 11.1. Gaussian space and the Gaussian noise operator

Notation 11.1 uses the standard Gaussian density $\phi$, cumulative distribution
$\Phi$, complementary distribution, and the product standard Gaussian law $\gamma_n$.
Definition 11.2 uses ordinary Gaussian $L^p$ spaces. TCSlib's Chapter 5 Gaussian
notation and Mathlib's `Lp`, `MemLp`, and product measures are reused.

<a id="pdf-8b2c50cf9621-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=1.00 -->
**Definition 11.5.** The bit simulation is the normalized sum
$M^{-1/2}\sum_{j=1}^M x_j$, with the vector version applied independently to blocks.
This construction is deferred pending a precise bridge to the existing cube API.

<a id="pdf-8b2c50cf9621-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=1.00 -->
**Definitions 11.6–11.12; Fact 11.7.** A correlated pair of standard Gaussian vectors
can be realized as $(g,\rho g+\sqrt{1-\rho^2}g')$ for independent $g,g'$;
the Gaussian noise operator averages a function at the second point for fixed first
point. These definitions and related OU/Mehler developments already occur in audited
external libraries and are not redeclared in the new skeleton.

<a id="pdf-8b2c50cf9621-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=1.00 -->
**Propositions 11.15–11.17.** Gaussian noise contracts $L^p$ for $1\le p\le\infty$,
smooths at correlations strictly between $-1$ and $1$, and converges to the identity
in $L^1$ as correlation tends to $1$ from below. External overlap is recorded in the
coverage ledger; equivalence of all domains/endpoints is not asserted by this index.

<a id="pdf-8b2c50cf9621-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=1.00 -->
**Theorem 11.22 and Gaussian Hypercontractivity.** Multivariate polynomials are dense
in Gaussian $L^p$ for finite $p\ge1$. The two-function Gaussian hypercontractive
inequality holds when $r,s\ge0$ and $0\le\rho\le\sqrt{rs}\le1$.
Theorem 11.23 on PDF page 8 is the one-function version. These are external reuse
targets, not new statement stubs.

<a id="pdf-8b2c50cf9621-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=1.00 -->
**Definition 11.24; Propositions 11.26–11.28; Gaussian Log-Sobolev.** The positive
number operator is $Lf=x\cdot\nabla f-\Delta f$ on a suitable operator domain.
The source relates it to noise derivatives and integration by parts, and obtains
$\tfrac12\operatorname{Ent}(f^2)\le E\|\nabla f\|^2$ on PDF page 10.
An exact operator domain and existing external APIs must be reconciled before any
new bridge statements are proposed.

<a id="pdf-8b2c50cf9621-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=1.00 -->
## 11.2. Hermite polynomials

Definitions 11.29, 11.32, 11.34 and Propositions 11.30–11.40 develop normalized
probabilists' Hermite polynomials, their product basis, expansion coefficients,
Plancherel, and diagonal noise/number operators. Mathlib already defines the
probabilists' polynomials; audited Gaussian Hilbert and OU projects cover substantial
analytic infrastructure. No duplicate Hermite definitions or basis skeletons are added.

<a id="pdf-8b2c50cf9621-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=1.00 -->
## 11.3. Borell's Isoperimetric Theorem

Borell's theorem bounds Gaussian noise stability of a $[0,1]$-valued function of
mean $\alpha$ by that of a halfspace of volume $\alpha$. Existing external statements
are reused as planned dependencies even where their proofs remain incomplete.
The new slice begins with the distinct rotation-sensitivity development.

<a id="pdf-8b2c50cf9621-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=1.00 -->
**Definition 11.42.** For a Borel set $A\subseteq\mathbb R^n$ and real angle $\delta$,
$RS_A(\delta)$ is the probability that its indicator differs on a
$\cos\delta$-correlated Gaussian pair. The pair can be represented by
$g$ and $\cos\delta\,g+\sin\delta\,g'$ with independent standard Gaussian vectors.

<a id="pdf-8b2c50cf9621-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=1.00 -->
**Theorem 11.43.** For any finite real angle sequence,
$$RS_A(\delta_1+\cdots+\delta_\ell)
\le\sum_{j=1}^{\ell}RS_A(\delta_j).$$
In particular, for a positive integer $\ell$,
$$RS_A(\delta)\le\ell RS_A(\delta/\ell).$$
The binary form is the same statement with two angles.

<a id="pdf-8b2c50cf9621-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=1.00 -->
**Corollary 11.44.** If $\gamma_n(A)=1/2$ and $\ell>0$ is an integer, then
$$RS_A(\pi/(2\ell))\ge1/(2\ell).$$
The source's calculation on PDF page 17 uses
$RS_A(\pi/2)=1/2$. More generally the independent-endpoint probability is
$RS_A(\pi/2)=2\gamma_n(A)(1-\gamma_n(A))$.

<a id="pdf-8b2c50cf9621-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=1.00 -->
**Gaussian Isoperimetric Inequality (unnumbered, §11.4).** If a halfspace has the
same Gaussian volume as a Borel set $A$, its Gaussian surface area is at most the
area of $A$. For $\alpha\in(0,1)$ this is
$U(\alpha)\le\operatorname{surf}_\gamma(A)$.

<a id="pdf-8b2c50cf9621-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=1.00 -->
## 11.4. Gaussian surface area and Bobkov's Inequality

**Definition 11.48.** Gaussian surface area is the extended nonnegative quantity
$$\operatorname{surf}_\gamma(A)=\sqrt{\pi/2}\,RS'_A(0+).$$
The right derivative can be infinite. The source also characterizes it by the
infimum of lower limits of expected gradient lengths over smooth $[0,1]$-valued
approximations to the indicator in Gaussian $L^1$, with first derivatives in $L^2$.
It identifies this relaxation with Gaussian Minkowski boundary content for suitably
regular sets. Only the rotation-limit formulation is represented in this starting
slice; the precise relaxation and regular-boundary bridges are deferred.

The new Lean definition first takes the lower limit of the nonnegative scaled
quotient and leaves existence of the full right limit as an explicit theorem stub.
The discussion on PDF page 18 explains why null modifications must preserve area.

<a id="pdf-8b2c50cf9621-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=1.00 -->
**Proposition 11.49.** A halfspace of Gaussian volume $\alpha\in(0,1)$ has
surface area $U(\alpha)=\phi(\Phi^{-1}(\alpha))$. Equivalently, the closed halfspace
$\{x:a\cdot x\le t\}$ with $\sum_i a_i^2=1$ has area $\phi(t)$.
At volume $1/2$ its area is $1/\sqrt{2\pi}$.

<a id="pdf-8b2c50cf9621-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=1.00 -->
**Theorem 11.51.** For every positive $\delta$,
$$\sqrt{\pi/2}\,RS_A(\delta)/\delta\le\operatorname{surf}_\gamma(A).$$

<a id="pdf-8b2c50cf9621-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=1.00 -->
**Theorem 11.52.** Writing $\alpha=\gamma_n(A)$,
$$2\sqrt{2/\pi}\,\alpha(1-\alpha)\le\operatorname{surf}_\gamma(A).$$
In the balanced case this is sharp.

<a id="pdf-8b2c50cf9621-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=1.00 -->
**Bobkov's Inequality (11.15).** For $f:\{-1,1\}^n\to[0,1]$,
$$U(Ef)\le E\sqrt{U(f(x))^2+\sum_i(D_if(x))^2}.$$
Here the source uses $U(0)=U(1)=0$. The new endpoint adapter reuses the existing
Chapter 5 interior profile; it does not reconstruct the Gaussian quantile.

<a id="pdf-8b2c50cf9621-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=1.00 -->
**Bobkov's Two-Point Inequality.** If $a+b,a-b\in[0,1]$, then
$$U(a)\le\tfrac12\sqrt{U(a+b)^2+b^2}
+\tfrac12\sqrt{U(a-b)^2+b^2}.$$
The stopped-walk Claim 11.54 is proof infrastructure rather than a separate new model.

<a id="pdf-8b2c50cf9621-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=1.00 -->
**Theorem 11.55.** For $f:\{-1,1\}^n\to[0,1]$, the quantity
$$E\sqrt{U(T_\rho f)^2+\sum_i(D_iT_\rho f)^2}$$
is increasing in $\rho\in[0,1]$.

<a id="pdf-8b2c50cf9621-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=1.00 -->
## 11.5. The Berry–Esseen Theorem

The scalar Berry–Esseen development is an external reuse target, including the
user-identified ProbabilityApproximation library. Mathlib distance and mollifier APIs
are also reused. No generic Berry–Esseen, interval-distance, or mollifier definitions
are added here. Exact remaining scalar-test-function adapters are deferred.

<a id="pdf-8b2c50cf9621-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=1.00 -->
## 11.6. The Invariance Principle

**Definition 11.63; Remark 11.64.** For a formal multilinear polynomial
$F(x)=\sum_S\widehat F(S)\prod_{i\in S}x_i$, define
$\operatorname{Var}(F)=\sum_{S\ne\varnothing}\widehat F(S)^2$ and
$\operatorname{Inf}_i(F)=\sum_{S\ni i}\widehat F(S)^2$.
On independent mean-zero, variance-one inputs these are the usual variance and
coordinate influences. Existing TCSlib polynomial evaluation and cube coefficient
identities supply these quantities; no replacement definitions are introduced.

<a id="pdf-8b2c50cf9621-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=1.00 -->
**Hypothesis 11.65.** Each coordinate satisfies
$$E[z_i]=0,\qquad E[z_i^2]=1,\qquad E[z_i^3]=0,\qquad E[z_i^4]\le9.$$
The last condition is 9-reasonability because the second moment is one.

<a id="pdf-8b2c50cf9621-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=1.00 -->
**Basic Invariance Principle (unnumbered), equation (11.29).** Let $F$ have
multilinear degree at most $k$. Let $x$ and $y$ each be sequences of independent
random variables satisfying Hypothesis 11.65. For $\psi\in C^4(\mathbb R)$ with
$\|\psi^{(4)}\|_\infty\le C$,
$$|E\psi(F(x))-E\psi(F(y))|
\le (C/12)9^k\sum_i\operatorname{Inf}_i(F)^2.$$
Separate probability spaces may be coupled independently without changing either
expectation. The arbitrary-law C4 theorem is distinct from the externally available
C3 Boolean-to-Gaussian theorem.

<a id="pdf-8b2c50cf9621-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=1.00 -->
**Corollary 11.67.** In the setting of the Basic Invariance Principle, if
$\operatorname{Var}(F)\le1$ and every influence is at most $\epsilon$, then
$$|E\psi(F(x))-E\psi(F(y))|\le(C/12)k9^k\epsilon.$$

<a id="pdf-8b2c50cf9621-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=1.00 -->
**Corollary 11.68.** With the same input, variance, and influence hypotheses,
for a $c$-Lipschitz test the error is at most
$$Kc\,2^k\epsilon^{1/4},$$
where $K$ is a universal constant independent of dimension, degree, laws,
polynomial, test, and Lipschitz constant.

<a id="pdf-8b2c50cf9621-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->
**Corollaries 11.69–11.70; Carbery–Wright; Theorem 11.71.** The chapter continues
with noise-smoothed/no-notables invariance, Lévy bounds, Gaussian polynomial
anticoncentration, and CDF bounds. These are deferred pending exact representation
and overlap checks; they are not counted as formalized by the three new invariance stubs.

<a id="pdf-8b2c50cf9621-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->
## 11.7. Highlight: Majority Is Stablest Theorem

Existing TCSlib and external Majority Is Stablest statements are excluded from new
skeletons. The Max-Cut discussion and Theorems 11.72–11.74 require existing complexity
models to be audited before integration. The quantitative general-volume theorem
(11.39) on PDF page 42 is deferred; a fresh weaker MIS statement is not substituted.

The coverage ledger records exact external commits, local reuse names, remaining
integration work, and the bounded nature of the duplication search.
