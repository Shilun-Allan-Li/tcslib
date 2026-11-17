<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: ffbe9c7b3306c5d5cf14b26b0e17943c1ca5d4a3c2fa7e215e985e16441e915d -->

<a id="pdf-ffbe9c7b3306-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=1.00 -->
Contents listing; these pages contain no mathematical statements or proofs.

<a id="pdf-ffbe9c7b3306-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=1.00 -->
Prefaces begin on printed page ix; notation begins on xiii.

<a id="pdf-ffbe9c7b3306-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=1.00 -->
Chapter 1 (printed pp. 19–33): Boolean-function analysis, multilinear Fourier representations, the parity basis and its orthonormality, Fourier identities, densities and convolution, approximate linearity and BLR testing, then exercises.

<a id="pdf-ffbe9c7b3306-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=1.00 -->
Chapter 2 (printed pp. 43–61): social choice, coordinate influences and derivatives, total influence, noise stability, Arrow’s theorem, then exercises.

<a id="pdf-ffbe9c7b3306-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=1.00 -->
Chapter 3 begins on printed p. 69; §§3.1–3.3 cover concentration of the Fourier spectrum at low degrees, subspaces and decision trees, and restrictions.

<a id="pdf-ffbe9c7b3306-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=1.00 -->
Sections 3.4–3.6 (printed pp. 78–85) cover learning, the Goldreich–Levin algorithm, and exercises.

<a id="pdf-ffbe9c7b3306-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=1.00 -->
Chapter 4 (printed pp. 93–107): DNFs, Tribes, random restrictions, Håstad’s switching lemma and DNF Fourier spectra, LMN results for constant-depth circuits, then exercises.

<a id="pdf-ffbe9c7b3306-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=1.00 -->
Chapter 5 (printed pp. 113–134): linear and polynomial threshold functions, Majority and the central limit theorem, Majority’s Fourier coefficients, degree-one Fourier weight, Peres’s theorem and uniform noise stability, then exercises.

<a id="pdf-ffbe9c7b3306-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=1.00 -->
Chapter 6 (printed pp. 143–163): pseudorandomness and \(\mathbb F_2\)-polynomials; constructions, learning and testing applications, and exercises.

<a id="pdf-ffbe9c7b3306-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=1.00 -->
Chapter 7 (printed pp. 173–195): dictator tests, probabilistically checkable proofs of proximity, constraint satisfaction and complexity, Håstad’s hardness results, then exercises.

<a id="pdf-ffbe9c7b3306-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=1.00 -->
Chapter 8 begins on printed p. 207; §§8.1–8.2 concern Fourier bases on product spaces and extensions of Fourier identities.

<a id="pdf-ffbe9c7b3306-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=1.00 -->
Contents: remaining topics in Chapter 8 and Chapters 9–11.

<a id="pdf-ffbe9c7b3306-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=1.00 -->
§§8.3–8.7 cover orthogonal decomposition, biased measures, Abelian groups, and randomized decision trees. Chapter 9 introduces hypercontractivity, low-degree bounds, noise sensitivity, applications, and KKL. Chapter 10 develops hypercontractivity for uniform bits and general random variables, randomization/symmetrization, and sharp thresholds. Chapter 11 treats Gaussian noise, Hermite polynomials, Borell isoperimetry, Gaussian surface area, Bobkov’s inequality, Berry–Esseen, invariance, and Majority Is Stablest.

<a id="pdf-ffbe9c7b3306-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=1.00 -->
Prefaces to the revised and original editions.

<a id="pdf-ffbe9c7b3306-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=1.00 -->
Context for the May 2021 revision.

<a id="pdf-ffbe9c7b3306-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=1.00 -->
The revision corrects over 100 minor errors while preserving numbered items; its mathematical coverage remains essentially that of 2014.

<a id="pdf-ffbe9c7b3306-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=1.00 -->
Subject and scope of the textbook.

<a id="pdf-ffbe9c7b3306-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=1.00 -->
The book studies maps $f:\{0,1\}^n\to\{0,1\}$ through Fourier expansions and analytic methods, developing foundations and applications across theoretical computer science and mathematics.

<a id="pdf-ffbe9c7b3306-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=1.00 -->
Notation for vector operations, Boolean logic, Fourier analysis, sets, and multi-indices.

<a id="pdf-ffbe9c7b3306-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
**Definitions.** The symbol $\circ$ denotes entrywise vector multiplication; $\nabla f(x)=(D_1f(x),\ldots,D_nf(x))$.

<a id="pdf-ffbe9c7b3306-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.97 -->
**Definitions.** $\neg,\oplus,\vee,\wedge$ denote NOT, XOR, OR, and AND. $S\ni i$ means $i\in S$. Symmetric difference is $S\triangle T=\{i:i\text{ belongs to exactly one of }S,T\}$.

<a id="pdf-ffbe9c7b3306-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=1.00 -->
**Definition.** \(\|\widehat f\|_p=\bigl(\sum_{\gamma\in\widehat{\mathbb F}_2^n}|\widehat f(\gamma)|^p\bigr)^{1/p}\).

<a id="pdf-ffbe9c7b3306-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=1.00 -->
**Definitions.** $*$ denotes convolution; $[z^k]F(z)$ extracts the coefficient of $z^k$ from $F$.

<a id="pdf-ffbe9c7b3306-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=1.00 -->
**Definitions.** $1_A$ is the $0$–$1$ indicator of a set $A$, $1_B$ the indicator random variable of an event $B$, and $2^A$ the power set of $A$.

<a id="pdf-ffbe9c7b3306-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.99 -->
**Definitions.** For a multi-index $\alpha$, $\#\alpha$ counts its nonzero components and $|\alpha|=\sum_i\alpha_i$.

<a id="pdf-ffbe9c7b3306-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=1.00 -->
**Definitions.** $\mathrm{AND}_n$ is true exactly when all $n$ inputs are true; $A^\perp=\{\gamma:\gamma\cdot x=0\text{ for every }x\in A\}$; $\mathrm{Aut}(f)$ is the automorphism group of the Boolean function $f$.

<a id="pdf-ffbe9c7b3306-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=1.00 -->
**Definition.** On input \(x\in\{-1,1\}^{d\times M}\), \(\mathrm{BitsToGaussians}_M^d\) outputs \(z\in\mathbb R^d\), equal to \(1/\sqrt M\) times the column-wise sum of \(x\). If \(d\) is omitted, it is taken to be 1.

<a id="pdf-ffbe9c7b3306-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.99 -->
**Definitions.** \(\mathbb C\) denotes the complex numbers. For a bit \(b\in\mathbb F_2\), \(\chi(b)=(-1)^b\). For sign inputs, \(\chi_S(x)=\prod_{i\in S}x_i\); for binary inputs, \(\chi_S(x)=(-1)^{\sum_{i\in S}x_i}\).

<a id="pdf-ffbe9c7b3306-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.98 -->
**Definition.** For a subspace $H$ of an $n$-dimensional ambient space, $\operatorname{codim}H=n-\dim H$.

<a id="pdf-ffbe9c7b3306-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=1.00 -->
**Definition.** \(\operatorname{Cov}[f,g]=\mathbb E[fg]-\mathbb E[f]\mathbb E[g]\).

<a id="pdf-ffbe9c7b3306-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.99 -->
**Definition.** $D_if(x)=\frac{f(x^{(i\mapsto1)})-f(x^{(i\mapsto-1)})}{2}$.

<a id="pdf-ffbe9c7b3306-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.98 -->
**Definition.** $d_{\chi^2}(\phi,1)$ denotes the chi-squared distance between the distribution with density $\phi$ and the uniform distribution.

<a id="pdf-ffbe9c7b3306-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.97 -->
**Definitions.** $\deg(f)$ is the least $k$ for which $f$ is a real linear combination of $k$-juntas. For Boolean-valued $f$, $\deg_2(f)$ is the degree of its $\mathbb F_2$-polynomial representation.

<a id="pdf-ffbe9c7b3306-p014-b008"></a>
<!-- pdf-source: page=14; block=8; confidence=1.00 -->
**Definition.** $\Delta(x,y)=\#\{i:x_i\ne y_i\}$.

<a id="pdf-ffbe9c7b3306-p014-b009"></a>
<!-- pdf-source: page=14; block=9; confidence=0.99 -->
**Definitions.** Under input distribution $\pi$, $\Delta^{(\pi)}(f)$ is the minimum expected query count of a decision tree computing $f$. For randomized $T$, $\Delta^{(\pi)}(T)$ is its expected query count and $\delta_i^{(\pi)}(T)$ its probability of querying $i$. The revealment is $\delta^{(\pi)}(f)=\min_{T\text{ computes }f}\max_i\delta_i^{(\pi)}(T)$.

<a id="pdf-ffbe9c7b3306-p014-b010"></a>
<!-- pdf-source: page=14; block=10; confidence=0.99 -->
**Definition.** For $f:\mathbb F_2^n\to\mathbb F_2$, $\Delta_yf(x)=f(x+y)-f(x)$.

<a id="pdf-ffbe9c7b3306-p014-b011"></a>
<!-- pdf-source: page=14; block=11; confidence=1.00 -->
**Definition.** $\operatorname{dist}(g,h)$ is the fraction of inputs where $g$ and $h$ differ.

<a id="pdf-ffbe9c7b3306-p014-b012"></a>
<!-- pdf-source: page=14; block=12; confidence=1.00 -->
**Definitions.** $\mathrm{DNFsize}(f)$ and $\mathrm{DNFwidth}(f)$ minimize DNF size and width over formulas computing $f$. $\mathrm{DT}(f)$ and $\mathrm{DTsize}(f)$ similarly minimize decision-tree depth and size.

<a id="pdf-ffbe9c7b3306-p014-b013"></a>
<!-- pdf-source: page=14; block=13; confidence=1.00 -->
**Definition.** $d_{\mathrm{TV}}(\phi,\psi)$ is the total variation distance between the distributions with densities $\phi$ and $\psi$.

<a id="pdf-ffbe9c7b3306-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=1.00 -->
**Definitions.** $\mathrm E_if(x)=\mathbb E_{x_i}[f(x_1,\ldots,x_n)]$ averages coordinate $i$ while holding the others fixed; $\mathrm E_I$ averages the coordinates in $I$.

<a id="pdf-ffbe9c7b3306-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=1.00 -->
**Definition.** For nonnegative $f$ on a probability space, $\operatorname{Ent}[f]=\mathbb E[f\ln f]-\mathbb E[f]\ln\mathbb E[f]$.

<a id="pdf-ffbe9c7b3306-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=1.00 -->
**Definition.** \(\mathbb E_{\pi_p}[\cdot]\) abbreviates \(\mathbb E_{x\sim\pi_p^{\otimes n}}[\cdot]\).

<a id="pdf-ffbe9c7b3306-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=1.00 -->
**Definition.** For sign-valued functions on $m$ and $n$ bits, $(f\oplus g)(x,y)=f(x)g(y)$ on $m+n$ bits.

<a id="pdf-ffbe9c7b3306-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
**Definitions.** For $f:\{-1,1\}^m\to\{-1,1\}$ and $g:\{-1,1\}^n\to\{-1,1\}$, $(f\otimes g)(x^{(1)},\ldots,x^{(m)})=f(g(x^{(1)}),\ldots,g(x^{(m)}))$. For $n$-bit $f$, $f^{\otimes1}=f$ and $f^{\otimes(d+1)}=f\otimes f^{\otimes d}$, with domain $\{-1,1\}^{n^d}$ at iteration $d$.

<a id="pdf-ffbe9c7b3306-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=1.00 -->
**Definitions.** $f^{*n}$ is the convolution of $n$ copies of $f$; the Boolean dual is $f^\dagger(x)=-f(-x)$.

<a id="pdf-ffbe9c7b3306-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.98 -->
**Definitions.** For $f$ on $\mathbb F_2^n$ and $z\in\mathbb F_2^n$, $f^{+z}(x)=f(x+z)$; $f_H^{+z}=(f^{+z})_H$.

<a id="pdf-ffbe9c7b3306-p015-b008"></a>
<!-- pdf-source: page=15; block=8; confidence=0.96 -->
**Definitions.** $\mathbb F_2$ is the field with two elements. $\widehat{\mathbb F}_2^n$ denotes the group or vector space indexing Fourier characters for functions on $\mathbb F_2^n$.

<a id="pdf-ffbe9c7b3306-p015-b009"></a>
<!-- pdf-source: page=15; block=9; confidence=1.00 -->
**Definition.** $f^{\mathrm{even}}(x)=(f(x)+f(-x))/2$.

<a id="pdf-ffbe9c7b3306-p015-b010"></a>
<!-- pdf-source: page=15; block=10; confidence=1.00 -->
**Definition.** $\langle f,g\rangle=\mathbb E_x[f(x)g(x)]$.

<a id="pdf-ffbe9c7b3306-p015-b011"></a>
<!-- pdf-source: page=15; block=11; confidence=0.99 -->
**Definitions.** $f_H$ is the restriction of $f$ to a subspace $H\le\mathbb F_2^n$; $\widehat f(i)$ abbreviates $\widehat f(\{i\})$.

<a id="pdf-ffbe9c7b3306-p015-b012"></a>
<!-- pdf-source: page=15; block=12; confidence=0.99 -->
**Definition.** $f^{\subseteq J}$ averages $f$ over coordinates outside $J$, leaving a function of $x_J$. On the sign cube, $f^{\subseteq J}=\sum_{S\subseteq J}\widehat f(S)\chi_S$.

<a id="pdf-ffbe9c7b3306-p015-b013"></a>
<!-- pdf-source: page=15; block=13; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p015-b014"></a>
<!-- pdf-source: page=15; block=14; confidence=1.00 -->
**Definitions.** $f^{=k}=\sum_{|S|=k}\widehat f(S)\chi_S$ and $f^{\le k}=\sum_{|S|\le k}\widehat f(S)\chi_S$.

<a id="pdf-ffbe9c7b3306-p015-b015"></a>
<!-- pdf-source: page=15; block=15; confidence=1.00 -->
**Definition.** $f^{\mathrm{odd}}(x)=(f(x)-f(-x))/2$.

<a id="pdf-ffbe9c7b3306-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=1.00 -->
Notation glossary, continued.

<a id="pdf-ffbe9c7b3306-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.96 -->
**Definitions.** For prime \(p\) and positive integer \(\ell\), \(\mathbb F_{p^\ell}\) is the field with \(p^\ell\) elements. For \(S\subseteq J\subseteq[n]\), \(\widehat{f_{J\mid z}}(S)\) denotes the indicated restricted Fourier coefficient. The randomization is \(\widetilde f(r,x)=\sum_S r^S f^{=S}(x)\).

<a id="pdf-ffbe9c7b3306-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.97 -->
**Definitions.** \(\gamma^+(\partial A)\) denotes Gaussian Minkowski boundary content. \(G(v,p)\) denotes the Erdős–Rényi graph law \(\pi_p^{\otimes\binom v2}\).

<a id="pdf-ffbe9c7b3306-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=1.00 -->
**Definitions.** The probabilists’ Hermite polynomials are defined by \(\exp(tz-t^2/2)=\sum_{j=0}^{\infty}H_j(z)t^j/j!\). Their normalized versions are \(h_j=H_j/\sqrt{j!}\); for \(\alpha\in\mathbb N^n\), \(h_\alpha(z)=\prod_{j=1}^n h_{\alpha_j}(z_j)\).

<a id="pdf-ffbe9c7b3306-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.98 -->
**Definitions.** \(\operatorname{Inf}_i[f]\) is the influence of coordinate \(i\); \(\operatorname{Inf}^{(\rho)}_i[f]=\operatorname{Stab}_\rho[D_i f]\). For Boolean-valued \(f\), coalitional influence is \(\widetilde{\operatorname{Inf}}_J[f]=\Pr_{z\sim\{-1,1\}^{\bar J}}[f_{J\mid z}\text{ is nonconstant}]\). Its \(b\)-directed variant is \(\widetilde{\operatorname{Inf}}_J^b[f]=\Pr_z[f_{J\mid z}\not\equiv-b]-\Pr[f=b]\).

<a id="pdf-ffbe9c7b3306-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.99 -->
**Definitions.** \(\overline J=[n]\setminus J\). The cube space \(L^2(\{-1,1\}^n)\) uses \(\pi_{1/2}^{\otimes n}\). For a finite abelian group \(G\), \(L^2(G^n)\) has inner product \(\langle f,g\rangle=\mathbb E_{x\sim G^n}[f(x)\overline{g(x)}]\). On \((\Omega,\pi)\), the real square-integrable space has \(\langle f,g\rangle=\mathbb E_\pi[fg]\).

<a id="pdf-ffbe9c7b3306-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=1.00 -->
**Definitions.** For standard Gaussians with \(\mathbb E[z_1z_2]=\rho\), \(\Lambda_\rho(\alpha,\beta)=\Pr[z_1\le\Phi^{-1}(\alpha),\ z_2\le\Phi^{-1}(\beta)]\), and \(\Lambda_\rho(\alpha)=\Lambda_\rho(\alpha,\alpha)\).

<a id="pdf-ffbe9c7b3306-p016-b008"></a>
<!-- pdf-source: page=16; block=8; confidence=1.00 -->
**Definitions.** On the cube, \(L_i f=f-E_i f\) and \(Lf=\sum_{i=1}^nL_i f\); on Gaussian space, L denotes the Ornstein–Uhlenbeck operator. The conventions are \(\ln x=\log_e x\), \(\log x=\log_2 x\), and \(\operatorname{Maj}_n\) for n-bit majority.

<a id="pdf-ffbe9c7b3306-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=1.00 -->
Notation glossary, continued.

<a id="pdf-ffbe9c7b3306-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=1.00 -->
**Definitions.** \(\operatorname{MaxInf}[f]=\max_i\operatorname{Inf}_i[f]\); \([n]=\{1,2,3,\ldots,n\}\). The following entries denote \(\mathbb N=\{0,1,2,\ldots\}\), \(\mathbb N^+=\{1,2,3,\ldots\}\), and \(\mathbb N_{<m}=\{0,1,\ldots,m-1\}\), respectively.

<a id="pdf-ffbe9c7b3306-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=1.00 -->
**Definitions.** For a bit string x, \(N_\rho(x)\) is the law of a string ρ-correlated with x. For \(z\in\mathbb R^n\), \(N_\rho(z)\) is the law of \(\rho z+\sqrt{1-\rho^2}\,g\), with \(g\sim N(0,1)^n\). Noise sensitivity satisfies \(\operatorname{NS}_\delta[f]=(1-\operatorname{Stab}_{1-2\delta}[f])/2\).

<a id="pdf-ffbe9c7b3306-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=1.00 -->
**Definitions.** \(N(0,1)\) is the standard Gaussian law, and \(N(0,1)^d=N(0,I_{d\times d})\) has independent standard coordinates. For \(\mu\in\mathbb R^d\) and positive semidefinite \(\Sigma\in\mathbb R^{d\times d}\), \(N(\mu,\Sigma)\) has mean μ and covariance Σ. \(\operatorname{OR}_n\) is false precisely when every input is false.

<a id="pdf-ffbe9c7b3306-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=1.00 -->
**Definitions.** \(\phi(z)=\frac1{\sqrt{2\pi}}e^{-z^2/2}\), \(\Phi(t)=\int_{-\infty}^t\phi(z)\,dz\), and \(\overline\Phi(t)=\int_t^\infty\phi(z)\,dz\).

<a id="pdf-ffbe9c7b3306-p017-b006"></a>
<!-- pdf-source: page=17; block=6; confidence=0.99 -->
**Definitions.** The uniform density on A is \(\varphi_A=1_A/\mathbb E[1_A]\). Given \(\phi_0,\ldots,\phi_{m-1}\) and multi-index α, \(\phi_\alpha=\prod_{i=1}^n\phi_{\alpha_i}\). A law π on Ω induces the product law \(\pi^{\otimes n}\) on \(\Omega^n\).

<a id="pdf-ffbe9c7b3306-p017-b007"></a>
<!-- pdf-source: page=17; block=7; confidence=0.99 -->
**Definitions.** \(\pi_{1/2}\) is uniform on \(\{-1,1\}\); \(\pi_p(-1)=p\) and \(\pi_p(1)=1-p\). The notation \(\Pr_{\pi_p}[\cdot]\) abbreviates sampling from \(\pi_p^{\otimes n}\). Two further entries denote \(\mathbb R\) and \(\mathbb R_{\ge0}\).

<a id="pdf-ffbe9c7b3306-p017-b008"></a>
<!-- pdf-source: page=17; block=8; confidence=0.99 -->
**Definitions.** \(\operatorname{RDT}(f)\) is zero-error randomized decision-tree complexity. Rotation sensitivity is \(\operatorname{RS}_A(\delta)=\Pr[1_A(z)\ne1_A(z')]\) for a \(\cos\delta\)-correlated Gaussian pair. Pointwise sensitivity \(\operatorname{sens}_f(x)\) counts pivotal coordinates at x.

<a id="pdf-ffbe9c7b3306-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=1.00 -->
Notation glossary, continued.

<a id="pdf-ffbe9c7b3306-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=1.00 -->
**Definitions.** \(\operatorname{sgn}(t)=1\) for \(t\ge0\), and −1 otherwise. \(S_n\) is the permutation group of [n]. The conventions are \(\operatorname{sparsity}(f)=\Pr_x[f(x)\ne0]\) and \(\operatorname{sparsity}(\widehat f)=|\operatorname{supp}(\widehat f)|\).

<a id="pdf-ffbe9c7b3306-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=1.00 -->
**Definitions.** \(\operatorname{Stab}_\rho[f]=\mathbb E[f(x)f(y)]\) for a ρ-correlated pair. For a multi-index α, \(\operatorname{supp}(\alpha)=\{i:\alpha_i\ne0\}\); for a function f, \(\operatorname{supp}(f)=\{x:f(x)\ne0\}\).

<a id="pdf-ffbe9c7b3306-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=1.00 -->
**Definitions.** \(T_\rho f(x)=\mathbb E_{y\sim N_\rho(x)}[f(y)]\). Coordinate noise is \(T^i_\rho f=\rho f+(1-\rho)E_i f\); for \(r\in\mathbb R^n\), \(T_r=T^1_{r_1}T^2_{r_2}\cdots T^n_{r_n}\).

<a id="pdf-ffbe9c7b3306-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=1.00 -->
**Definitions.** The Gaussian isoperimetric function is \(U=\phi\circ\Phi^{-1}\). Gaussian noise acts by \(U_\rho f(z)=\mathbb E_{z'\sim N_\rho(z)}[f(z')]\).

<a id="pdf-ffbe9c7b3306-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=1.00 -->
**Definitions.** \(\operatorname{Var}[f]=\mathbb E[f^2]-(\mathbb E[f])^2\). The operator \(\operatorname{Var}_i f(x)\) takes variance over coordinate \(x_i\), holding the other coordinates fixed. Gaussian volume is \(\operatorname{vol}_\gamma(A)=\Pr_{z\sim N(0,1)^n}[z\in A]\).

<a id="pdf-ffbe9c7b3306-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.99 -->
**Definitions.** \(W^k[f]\) and \(W^{>k}[f]\) denote Fourier weight at degree k and above degree k. The string \(x^{(i\mapsto b)}\) replaces coordinate i by b; \(x^{\oplus i}\) negates coordinate i.

<a id="pdf-ffbe9c7b3306-p018-b008"></a>
<!-- pdf-source: page=18; block=8; confidence=0.99 -->
**Definitions.** \(x\sim\varphi\) means sampling with density φ. Write \(x^S=\prod_{i\in S}x_i\), including \(x^\varnothing=1\). The notations \(x\sim A\) and \(x\sim\{-1,1\}^n\) mean uniform sampling.

<a id="pdf-ffbe9c7b3306-p018-b009"></a>
<!-- pdf-source: page=18; block=9; confidence=0.99 -->
**Definitions.** For \(J\subseteq[n]\), \(\bar J=[n]\setminus J\). The notation \((y,z)\), for \(y\in\{-1,1\}^J\) and \(z\in\{-1,1\}^{\bar J}\), denotes the corresponding string in \(\{-1,1\}^n\). \(\mathbb Z_m\) is the additive group of integers modulo \(m\); \(\widehat{\mathbb Z}_m^n\) indexes Fourier characters of functions on \(\mathbb Z_m^n\).

<a id="pdf-ffbe9c7b3306-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=1.00 -->
Introduces Fourier expansions as real multilinear polynomial representations, with applications to the Blum–Luby–Rubinfeld linearity test.

<a id="pdf-ffbe9c7b3306-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=1.00 -->
Introduces Boolean functions and their interpretations.

<a id="pdf-ffbe9c7b3306-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=1.00 -->
**Definition.** A Boolean function is a map $f:\{0,1\}^n\to\{0,1\}$. Examples include circuit outputs, graph properties on $\binom v2$ edge indicators, and set systems $\mathcal F\subseteq\mathcal P([n])$, represented by $f(X)=1\iff X\in\mathcal F$.

<a id="pdf-ffbe9c7b3306-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=1.00 -->
Other interpretations include code indicators, concepts with binary attributes, and two-candidate voting rules. Bits may be truth values, elements of $\mathbb F_2$, or real numbers; the usual convention here is $f:\{-1,1\}^n\to\{-1,1\}$.

<a id="pdf-ffbe9c7b3306-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=1.00 -->
**Definition.** The Hamming cube is $\{-1,1\}^n$. For strings $x,y$, their Hamming distance is $\Delta(x,y)=\#\{i:x_i\ne y_i\}$, where $x_i$ denotes coordinate $i$.

<a id="pdf-ffbe9c7b3306-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=1.00 -->
Fourier methods are useful when a Boolean-function problem involves Hamming distance together with counting or uniform probability on the cube.

<a id="pdf-ffbe9c7b3306-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=1.00 -->
Studies polynomial representations of functions on the Boolean cube.

<a id="pdf-ffbe9c7b3306-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=1.00 -->
**Definition.** The Fourier expansion represents $f:\{-1,1\}^n\to\{-1,1\}$ by a real multilinear polynomial: each variable has exponent at most one.

<a id="pdf-ffbe9c7b3306-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.99 -->
The function $\max_2$ equals $-1$ only at $(-1,-1)$ and has expansion $\max_2(x_1,x_2)=\tfrac12+\tfrac12x_1+\tfrac12x_2-\tfrac12x_1x_2$. The three-bit majority function returns the more frequent sign and satisfies
$$\operatorname{Maj}_3(x_1,x_2,x_3)=\tfrac12x_1+\tfrac12x_2+\tfrac12x_3-\tfrac12x_1x_2x_3.\tag{1.1}$$

<a id="pdf-ffbe9c7b3306-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.99 -->
**Proof.** For $a\in\{-1,1\}^n$, define
$$1_{\{a\}}(x)=\prod_{i=1}^n\frac{1+a_ix_i}{2}.\tag{1.2}$$
On the cube this is $1$ at $a$ and $0$ elsewhere, giving the multilinear representation
$$f(x)=\sum_{a\in\{-1,1\}^n}f(a)1_{\{a\}}(x).$$

<a id="pdf-ffbe9c7b3306-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=1.00 -->
**Proof step.** Substituting the four values of $\max_2$ gives
$$\begin{aligned}
\max_2(x)&=\frac{(1+x_1)(1+x_2)+(1-x_1)(1+x_2)+(1+x_1)(1-x_2)-(1-x_1)(1-x_2)}4\\
&=\tfrac12+\tfrac12x_1+\tfrac12x_2-\tfrac12x_1x_2.
\end{aligned}\tag{1.3}$$

<a id="pdf-ffbe9c7b3306-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=1.00 -->
The same interpolation applies to every $f:\{-1,1\}^n\to\mathbb R$ and produces a multilinear polynomial. More generally, polynomial expressions on the cube can be reduced using $x_i^2=1$.

<a id="pdf-ffbe9c7b3306-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.99 -->
**Definition (notation).** For S ⊆ [n], set x^S = ∏_{i∈S} x_i, with x^∅ = 1. Write f̂(S) for the coefficient of x^S in the multilinear representation of f : {−1,1}^n → ℝ.

<a id="pdf-ffbe9c7b3306-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=1.00 -->
**Theorem 1.1.** Every f : {−1,1}^n → ℝ has a unique multilinear expansion

f(x) = ∑_{S⊆[n]} f̂(S)x^S. (1.4)

This is its Fourier expansion; f̂(S) are its Fourier coefficients, collectively its Fourier spectrum.

<a id="pdf-ffbe9c7b3306-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.99 -->
For max₂, the coefficients on ∅, {1}, and {2} equal 1/2, while the coefficient on {1,2} equals −1/2. For Maj₃, each singleton coefficient equals 1/2, the coefficient on {1,2,3} equals −1/2, and all remaining coefficients vanish.

<a id="pdf-ffbe9c7b3306-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.99 -->
**Definition (notation).** On the sign cube, χ_S(x) = ∏_{i∈S} x_i, so f(x) = ∑_{S⊆[n]} f̂(S)χ_S(x). For the bit cube 𝔽₂^n, use χ : 𝔽₂ → ℝ given by χ(0) = 1 and χ(1) = −1, equivalently χ(b) = (−1)^b. Under this encoding, max₂ represents logical AND.

<a id="pdf-ffbe9c7b3306-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=1.00 -->
**Definition 1.2.** For S ⊆ [n], define χ_S : 𝔽₂^n → ℝ by

χ_S(x) = ∏_{i∈S} χ(x_i) = (−1)^{∑_{i∈S} x_i}.

These characters satisfy χ_S(x+y) = χ_S(x)χ_S(y). (1.5)

<a id="pdf-ffbe9c7b3306-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=1.00 -->
For f : 𝔽₂^n → ℝ, write f(x) = ∑_{S⊆[n]} f̂(S)χ_S(x). Subsets S may also be identified with their indicator vectors γ ∈ 𝔽₂^n.

<a id="pdf-ffbe9c7b3306-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=1.00 -->
## 1.3. The orthonormal basis of parity functions

<a id="pdf-ffbe9c7b3306-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=1.00 -->
Each χ_S : {−1,1}^n → {−1,1} computes XOR on the coordinates in S. The Fourier identity

f = ∑_{S⊆[n]} f̂(S)χ_S (1.6)

expresses functions in the real vector space V = {f : {−1,1}^n → ℝ} as linear combinations of parities. Evaluation identifies V with ℝ^{2^n}.

<a id="pdf-ffbe9c7b3306-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.99 -->
Equation (1.7) illustrates the evaluation-vector identity corresponding to max₂ = (1/2)χ_∅ + (1/2)χ_{\{1\}} + (1/2)χ_{\{2\}} − (1/2)χ_{\{1,2\}}.

<a id="pdf-ffbe9c7b3306-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=1.00 -->
**Proof (uniqueness in Theorem 1.1).** Equation (1.6) makes the parity functions a spanning set of V. Their number is 2^n = dim V, so they form a basis; Fourier coefficients are therefore unique.

<a id="pdf-ffbe9c7b3306-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=1.00 -->
**Definition 1.3.** For real functions on the sign cube, define

⟨f,g⟩ = 2^{−n}∑_{x∈{−1,1}^n} f(x)g(x) = E[f(x)g(x)]. (1.8)

Set ‖f‖₂ = √⟨f,f⟩ and, more generally, ‖f‖_p = (E[|f(x)|^p])^{1/p}. Every {−1,1}-valued function has squared norm 1.

<a id="pdf-ffbe9c7b3306-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=1.00 -->
**Notation 1.4.** The notation x ∼ {−1,1}^n means uniform sampling, equivalently independent coordinates taking each sign with probability 1/2. Random variables appear in boldface; probabilities and expectations use this distribution unless specified otherwise. Expectations may be abbreviated E_x[f(x)g(x)], E[f(x)g(x)], or E[fg].

<a id="pdf-ffbe9c7b3306-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=1.00 -->
**Theorem 1.5.** The 2^n parity functions form an orthonormal basis of V: ⟨χ_S,χ_T⟩ = 1 when S = T and 0 otherwise.

<a id="pdf-ffbe9c7b3306-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=1.00 -->
**Proof (reduction).** Since ⟨χ_S,χ_T⟩ = E[χ_S(x)χ_T(x)], the product identity in Fact 1.6 and expectation formula in Fact 1.7 yield the asserted inner products.

<a id="pdf-ffbe9c7b3306-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=1.00 -->
**Fact 1.6.** For x ∈ {−1,1}^n, χ_S(x)χ_T(x) = χ_{S△T}(x), where △ denotes symmetric difference.

<a id="pdf-ffbe9c7b3306-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=1.00 -->
**Proof.** Regrouping the coordinate products gives

χ_S(x)χ_T(x) = (∏_{i∈S△T} x_i)(∏_{i∈S∩T} x_i²) = ∏_{i∈S△T} x_i,

because x_i² = 1.

<a id="pdf-ffbe9c7b3306-p024-b007"></a>
<!-- pdf-source: page=24; block=7; confidence=1.00 -->
**Fact 1.7.** For uniform x on the sign cube, E[χ_S(x)] = E[∏_{i∈S} x_i] equals 1 if S = ∅ and 0 otherwise.

<a id="pdf-ffbe9c7b3306-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=1.00 -->
**Proof (continued).** For uniform independent signs, \(\mathbb E[\chi_\varnothing]=1\). If \(S\ne\varnothing\), independence gives \(\mathbb E[\chi_S(x)]=\prod_{i\in S}\mathbb E[x_i]=0\), since each sign has mean zero.

<a id="pdf-ffbe9c7b3306-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=1.00 -->
## 1.4. Basic Fourier formulas

<a id="pdf-ffbe9c7b3306-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=1.00 -->
The parities \((\chi_S)_{S\subseteq[n]}\) form an orthonormal basis for real functions on \(\{-1,1\}^n\); the \(2^n\) Fourier coefficients are the coordinates in this basis.

<a id="pdf-ffbe9c7b3306-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=1.00 -->
**Proposition 1.8.** For \(f:\{-1,1\}^n\to\mathbb R\) and \(S\subseteq[n]\),
\[\widehat f(S)=\langle f,\chi_S\rangle=\mathbb E_x[f(x)\chi_S(x)],\]
where \(x\) is uniform on the cube.

<a id="pdf-ffbe9c7b3306-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=1.00 -->
**Proof.** Expanding \(f\), using linearity, and applying parity orthonormality (Theorem 1.5) yields
\[\langle f,\chi_S\rangle=\sum_{T\subseteq[n]}\widehat f(T)\langle\chi_T,\chi_S\rangle=\widehat f(S).\tag{1.9}\]
This identity can alternatively define the coefficients.

<a id="pdf-ffbe9c7b3306-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=1.00 -->
**Parseval’s Theorem.** For \(f:\{-1,1\}^n\to\mathbb R\),
\[\langle f,f\rangle=\mathbb E_x[f(x)^2]=\sum_{S\subseteq[n]}\widehat f(S)^2.\]
If \(f\) takes values in \(\{-1,1\}\), this sum equals \(1\).

<a id="pdf-ffbe9c7b3306-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=1.00 -->
The expansions
\[\max_2(x)=\tfrac12+\tfrac12x_1+\tfrac12x_2-\tfrac12x_1x_2,\qquad \operatorname{Maj}_3(x)=\tfrac12x_1+\tfrac12x_2+\tfrac12x_3-\tfrac12x_1x_2x_3\]
each have four nonzero coefficients of squared magnitude \(1/4\), giving total weight \(1\).

<a id="pdf-ffbe9c7b3306-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=1.00 -->
**Plancherel’s Theorem.** For \(f,g:\{-1,1\}^n\to\mathbb R\),
\[\langle f,g\rangle=\mathbb E_x[f(x)g(x)]=\sum_{S\subseteq[n]}\widehat f(S)\widehat g(S).\]

<a id="pdf-ffbe9c7b3306-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=1.00 -->
**Proof.** Expanding both functions and using bilinearity gives
\[\langle f,g\rangle=\sum_{S,T\subseteq[n]}\widehat f(S)\widehat g(T)\langle\chi_S,\chi_T\rangle=\sum_{S\subseteq[n]}\widehat f(S)\widehat g(S),\]
since orthonormality removes the terms with \(S\ne T\).

<a id="pdf-ffbe9c7b3306-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=1.00 -->
**Proposition 1.9.** For \(f,g:\{-1,1\}^n\to\{-1,1\}\),
\[\langle f,g\rangle=\Pr_x[f(x)=g(x)]-\Pr_x[f(x)\ne g(x)]=1-2\operatorname{dist}(f,g).\]
Indeed, \(fg\) equals \(1\) on agreement and \(-1\) on disagreement.

<a id="pdf-ffbe9c7b3306-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=1.00 -->
**Definition 1.10.** The relative Hamming distance between Boolean-valued \(f,g\) is
\[\operatorname{dist}(f,g)=\Pr_{x\text{ uniform}}[f(x)\ne g(x)].\]

<a id="pdf-ffbe9c7b3306-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=1.00 -->
**Definition 1.11.** The mean of a real cube function \(f\) is \(\mathbb E[f]\); mean zero defines an unbiased or balanced function. For Boolean-valued \(f\),
\[\mathbb E[f]=\Pr[f=1]-\Pr[f=-1],\]
so balance means that exactly half the inputs have value \(1\).

<a id="pdf-ffbe9c7b3306-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=1.00 -->
**Fact 1.12.** Every real cube function satisfies \(\mathbb E[f]=\widehat f(\varnothing)\). Hence a Boolean function is balanced exactly when its constant Fourier coefficient vanishes.

<a id="pdf-ffbe9c7b3306-p026-b007"></a>
<!-- pdf-source: page=26; block=7; confidence=1.00 -->
**Proof.** Proposition 1.8 with \(S=\varnothing\) gives \(\mathbb E[f]=\langle f,1\rangle=\widehat f(\varnothing)\).

<a id="pdf-ffbe9c7b3306-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=1.00 -->
**Proposition 1.13.** For \(f:\{-1,1\}^n\to\mathbb R\),
\[\operatorname{Var}[f]=\langle f-\mathbb E[f],f-\mathbb E[f]\rangle=\mathbb E[f^2]-\mathbb E[f]^2=\sum_{\varnothing\ne S\subseteq[n]}\widehat f(S)^2.\]

<a id="pdf-ffbe9c7b3306-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=1.00 -->
**Proof.** Subtract the constant coefficient’s square from Parseval’s identity, using Fact 1.12.

<a id="pdf-ffbe9c7b3306-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=1.00 -->
**Fact 1.14.** For Boolean-valued \(f\),
\[\operatorname{Var}[f]=1-\mathbb E[f]^2=4\Pr[f(x)=1]\Pr[f(x)=-1]\in[0,1].\]
Balanced functions have variance \(1\), and constant functions have variance \(0\).

<a id="pdf-ffbe9c7b3306-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=1.00 -->
**Proposition 1.15.** Let \(f:\{-1,1\}^n\to\{-1,1\}\) and put \(\epsilon=\min\{\operatorname{dist}(f,1),\operatorname{dist}(f,-1)\}\). Then \(2\epsilon\le\operatorname{Var}[f]\le4\epsilon\).

<a id="pdf-ffbe9c7b3306-p027-b005"></a>
<!-- pdf-source: page=27; block=5; confidence=1.00 -->
**Proposition 1.16.** For \(f,g:\{-1,1\}^n\to\mathbb R\),
\[\operatorname{Cov}[f,g]=\langle f-\mathbb E[f],g-\mathbb E[g]\rangle=\mathbb E[fg]-\mathbb E[f]\mathbb E[g]=\sum_{\varnothing\ne S\subseteq[n]}\widehat f(S)\widehat g(S).\]
The Fourier identity follows by using Plancherel in the variance argument.

<a id="pdf-ffbe9c7b3306-p027-b006"></a>
<!-- pdf-source: page=27; block=6; confidence=1.00 -->
**Definition 1.17.** The Fourier weight of \(f:\{-1,1\}^n\to\mathbb R\) at \(S\subseteq[n]\) is \(\widehat f(S)^2\).

<a id="pdf-ffbe9c7b3306-p027-b007"></a>
<!-- pdf-source: page=27; block=7; confidence=1.00 -->
Variance is the total Fourier weight on nonempty sets (Proposition 1.13). For Boolean-valued functions, Parseval normalizes all weights to sum to \(1\), defining a probability law on subsets of \([n]\).

<a id="pdf-ffbe9c7b3306-p027-b008"></a>
<!-- pdf-source: page=27; block=8; confidence=1.00 -->
**Definition 1.18.** For Boolean-valued \(f\), its spectral sample distribution \(\mathcal S_f\) assigns probability \(\widehat f(S)^2\) to each \(S\subseteq[n]\). A sampled subset is denoted \(S\sim\mathcal S_f\).

<a id="pdf-ffbe9c7b3306-p027-b009"></a>
<!-- pdf-source: page=27; block=9; confidence=1.00 -->
For \(\max_2\), the spectral sample is uniform over all four subsets of \([2]\). For \(\operatorname{Maj}_3\), it is uniform over the four odd-cardinality subsets of \([3]\).

<a id="pdf-ffbe9c7b3306-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.99 -->
Fourier weights may be viewed on the inclusion lattice of subsets of $[n]$; Figure 1.1 illustrates $\operatorname{Maj}_3$ with weights $0$ and $1/4$. Subset size is the degree of the corresponding monomial.

<a id="pdf-ffbe9c7b3306-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.99 -->
**Definition 1.19.** For $f:\{-1,1\}^n\to\mathbb R$ and $0\le k\le n$, define
$$W^k[f]=\sum_{|S|=k}\widehat f(S)^2.$$
For Boolean-valued $f$, this equals $\Pr_{S\sim\mathcal S_f}[|S|=k]$. The degree-$k$ component is $f^{=k}=\sum_{|S|=k}\widehat f(S)\chi_S$, and Parseval gives $W^k[f]=\|f^{=k}\|_2^2$. Related notation includes $W^{>k}[f]=\sum_{|S|>k}\widehat f(S)^2$ and $f^{\le k}=\sum_{|S|\le k}\widehat f(S)\chi_S$.

<a id="pdf-ffbe9c7b3306-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=1.00 -->
## 1.5. Probability densities and convolution

<a id="pdf-ffbe9c7b3306-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.99 -->
This section uses $\mathbb F_2^n$ for the Hamming cube and studies probability densities as real-valued functions on it.

<a id="pdf-ffbe9c7b3306-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=1.00 -->
**Definition 1.20.** A probability density on $\mathbb F_2^n$ is a function $\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}$ with uniform expectation $\mathbb E[\varphi]=1$. Sampling $Y\sim\varphi$ means $\Pr[Y=y]=2^{-n}\varphi(y)$ for every $y$.

<a id="pdf-ffbe9c7b3306-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=1.00 -->
**Fact 1.21.** For a density $\varphi$ and $g:\mathbb F_2^n\to\mathbb R$,
$$\mathbb E_{Y\sim\varphi}[g(Y)]=\langle\varphi,g\rangle=\mathbb E_{x\text{ uniform}}[\varphi(x)g(x)].$$

<a id="pdf-ffbe9c7b3306-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=1.00 -->
The constant density $1$ induces the uniform distribution on the cube.

<a id="pdf-ffbe9c7b3306-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=1.00 -->
**Definition 1.22.** For $A\subseteq\mathbb F_2^n$, its indicator $1_A$ equals $1$ on $A$ and $0$ elsewhere. If $A\ne\varnothing$, its uniform-distribution density is
$$\varphi_A=\frac{1_A}{\mathbb E[1_A]}.$$
Sampling from this density is denoted $Y\sim A$.

<a id="pdf-ffbe9c7b3306-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=1.00 -->
For the singleton containing the zero vector, $\varphi_{\{0\}}(0)=2^n$ and $\varphi_{\{0\}}(y)=0$ for $y\ne0$.

<a id="pdf-ffbe9c7b3306-p029-b006"></a>
<!-- pdf-source: page=29; block=6; confidence=1.00 -->
**Fact 1.23.** The origin density has $\widehat{\varphi_{\{0\}}}(S)=1$ for every $S\subseteq[n]$, hence
$$\varphi_{\{0\}}(y)=\sum_{S\subseteq[n]}\chi_S(y).$$

<a id="pdf-ffbe9c7b3306-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=1.00 -->
**Definition 1.24.** For $f,g:\mathbb F_2^n\to\mathbb R$, define
$$(f*g)(x)=\mathbb E_y[f(y)g(x-y)]=\mathbb E_y[f(x-y)g(y)],$$
with uniform $y$. Since addition and subtraction coincide, either $x-y$ may be replaced by $x+y$. On $\{-1,1\}^n$, the corresponding operation uses coordinatewise multiplication $x\circ y$.

<a id="pdf-ffbe9c7b3306-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=1.00 -->
Convolution satisfies $f*(g*h)=(f*g)*h$ and $f*g=g*f$; verification is assigned to Exercise 1.25.

<a id="pdf-ffbe9c7b3306-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=1.00 -->
**Proposition 1.25.** For a density $\varphi$ and real-valued $g$,
$$(\varphi*g)(x)=\mathbb E_{Y\sim\varphi}[g(x-Y)]=\mathbb E_{Y\sim\varphi}[g(x+Y)].$$
In particular, $(\varphi*g)(0)=\mathbb E_{Y\sim\varphi}[g(Y)]$.

<a id="pdf-ffbe9c7b3306-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=1.00 -->
**Proposition 1.26.** For densities $\varphi,\psi$, their convolution is a density representing $Y+Z$, where $Y\sim\varphi$ and $Z\sim\psi$ are independent.

<a id="pdf-ffbe9c7b3306-p030-b005"></a>
<!-- pdf-source: page=30; block=5; confidence=1.00 -->
**Theorem 1.27.** For $f,g:\mathbb F_2^n\to\mathbb R$ and every $S\subseteq[n]$,
$$\widehat{f*g}(S)=\widehat f(S)\widehat g(S).$$

<a id="pdf-ffbe9c7b3306-p030-b006"></a>
<!-- pdf-source: page=30; block=6; confidence=1.00 -->
**Proof.** Expand the Fourier coefficient and convolution, then substitute $z=x-y$ in the uniform double average:
$$\widehat{f*g}(S)=\mathbb E_{x,y}[f(y)g(x-y)\chi_S(x)]=\mathbb E_{y,z}[f(y)g(z)\chi_S(y+z)].$$
Identity (1.5), $\chi_S(y+z)=\chi_S(y)\chi_S(z)$, and independence factor this into $\mathbb E_y[f(y)\chi_S(y)]\mathbb E_z[g(z)\chi_S(z)]=\widehat f(S)\widehat g(S)$.

<a id="pdf-ffbe9c7b3306-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=1.00 -->
Section 1.6 studies approximate linearity and the BLR linearity test.

<a id="pdf-ffbe9c7b3306-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.99 -->
**Definition 1.28.** A function \(f:\mathbb F_2^n\to\mathbb F_2\) is linear if it satisfies either equivalent condition: \(f(x+y)=f(x)+f(y)\) for every \(x,y\), or \(f(x)=a\cdot x=\sum_{i\in S}x_i\) for some \(a\in\mathbb F_2^n\), equivalently some \(S\subseteq[n]\). Under sign encoding, these are exactly the \(2^n\) characters \(\chi_S\).

<a id="pdf-ffbe9c7b3306-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.99 -->
Two approximate conditions are compared: additivity holds for almost all pairs \((x,y)\), and agreement with one linear function holds for almost all inputs. Approximate agreement readily implies approximate additivity; the section proves the converse. Property testing seeks such approximate guarantees using few queries to an unknown function.

<a id="pdf-ffbe9c7b3306-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.99 -->
**Definition 1.29.** Boolean functions \(f,g\) are \(\epsilon\)-close when \(\operatorname{dist}(f,g)\le\epsilon\), and \(\epsilon\)-far otherwise. For a nonempty property \(\mathcal P\), define \(\operatorname{dist}(f,\mathcal P)=\min_{g\in\mathcal P}\operatorname{dist}(f,g)\); closeness to \(\mathcal P\) means closeness to at least one member.

<a id="pdf-ffbe9c7b3306-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.99 -->
Approximate linearity means \(\epsilon\)-closeness to some function \(x\mapsto\sum_{i\in S}x_i\). Blum, Luby, and Rubinfeld [BLR90] established that frequent additivity implies this form of closeness.

<a id="pdf-ffbe9c7b3306-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=1.00 -->
**BLR Test.** For \(f:\mathbb F_2^n\to\mathbb F_2\), sample independent uniform \(x,y\), query \(f(x),f(y),f(x+y)\), and accept exactly when \(f(x)+f(y)=f(x+y)\).

<a id="pdf-ffbe9c7b3306-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=1.00 -->
**Theorem 1.30.** If the BLR Test accepts \(f:\mathbb F_2^n\to\mathbb F_2\) with probability \(1-\epsilon\), then \(f\) is \(\epsilon\)-close to a linear function.

<a id="pdf-ffbe9c7b3306-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=1.00 -->
**Proof.** Encode outputs as signs, making acceptance equivalent to \(f(x)f(y)f(x+y)=1\). Its indicator is \(\tfrac12+\tfrac12f(x)f(y)f(x+y)\). Thus, using convolution, Plancherel, and Theorem 1.27,
\[
1-\epsilon=\tfrac12+\tfrac12\mathbb E_x[f(x)(f*f)(x)]
=\tfrac12+\tfrac12\sum_{S\subseteq[n]}\widehat f(S)\widehat{f*f}(S)
=\tfrac12+\tfrac12\sum_{S\subseteq[n]}\widehat f(S)^3.\tag{1.10}
\]
Parseval then gives
\[
1-2\epsilon=\sum_S\widehat f(S)^3
\le\bigl(\max_S\widehat f(S)\bigr)\sum_S\widehat f(S)^2
=\max_S\widehat f(S).
\]

<a id="pdf-ffbe9c7b3306-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=1.00 -->
**Proof (conclusion).** Proposition 1.9 gives \(\widehat f(S)=\langle f,\chi_S\rangle=1-2\operatorname{dist}(f,\chi_S)\). A maximizing \(S^*\) therefore satisfies \(1-2\epsilon\le1-2\operatorname{dist}(f,\chi_{S^*})\), proving the required closeness.

<a id="pdf-ffbe9c7b3306-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.99 -->
Exercise 1.28 gives a sharp small-\(\epsilon\) improvement to roughly \(\epsilon/3\)-closeness. BLR uses three queries without identifying the nearby character; identification requires at least \(n\) queries (Exercise 1.27), while two queries suffice to recover its value probabilistically at any chosen input.

<a id="pdf-ffbe9c7b3306-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=1.00 -->
**Proposition 1.31.** If \(f:\mathbb F_2^n\to\{\pm1\}\) is \(\epsilon\)-close to \(\chi_S\), then for every fixed \(x\), sampling uniform \(y\) and returning \(f(y)f(x+y)\) yields \(\chi_S(x)\) with probability at least \(1-2\epsilon\). This guarantee holds separately for every \(x\), rather than only for most inputs.

<a id="pdf-ffbe9c7b3306-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=1.00 -->
**Proof.** Both \(y\) and \(x+y\) are uniform, so each queried value disagrees with its character value with probability at most \(\epsilon\). The union bound limits any disagreement to probability \(2\epsilon\). Otherwise,
\[
f(y)f(x+y)=\chi_S(y)\chi_S(x+y)=\chi_S(x).
\]

<a id="pdf-ffbe9c7b3306-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=1.00 -->
Section 1.7 begins the exercises and notes.

<a id="pdf-ffbe9c7b3306-p033-b006"></a>
<!-- pdf-source: page=33; block=6; confidence=0.99 -->
**Exercise 1.1 (visible parts).** Compute Fourier expansions for: (a) \(\min_2\), the two-bit OR in sign notation; (b) \(\min_3\) and \(\max_3\); (c) the singleton indicator \(\mathbf1_{\{a\}}:\mathbb F_2^n\to\{0,1\}\); (d) the singleton density \(\varphi_{\{a\}}\); and (e) the density \(\varphi_{\{a,a+e_i\}}\), where \(e_i\) is the \(i\)-th coordinate vector.

<a id="pdf-ffbe9c7b3306-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.98 -->
**Definition (1.1(f)).** The density on $\{-1,1\}^n$ of the product distribution whose coordinates each have mean $\rho\in[-1,1]$.

<a id="pdf-ffbe9c7b3306-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.99 -->
**Definition (1.1(g)).** $\mathrm{IP}_{2n}:\mathbb F_2^{2n}\to\{-1,1\}$ is given by $\mathrm{IP}_{2n}(x,y)=(-1)^{x\cdot y}$.

<a id="pdf-ffbe9c7b3306-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=1.00 -->
**Definitions (1.1(h–i)).** For $x\in\{-1,1\}^n$, $\mathrm{Equ}_n(x)=\mathbf1\{x_1=\cdots=x_n\}$ and $\mathrm{NAE}_n(x)=\mathbf1\{x_1,\ldots,x_n\text{ are not all equal}\}$.

<a id="pdf-ffbe9c7b3306-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=1.00 -->
**Definition (1.1(j)).** $\mathrm{Sel}:\{-1,1\}^3\to\{-1,1\}$ returns $x_2$ when $x_1=-1$ and $x_3$ when $x_1=1$.

<a id="pdf-ffbe9c7b3306-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.99 -->
**Definitions (1.1(k–l)).** On $\mathbb F_2^3$, $\mathrm{mod}_3$ indicates that the number of ones is divisible by $3$, while $\mathrm{OXR}(x)=x_1\lor(x_2\oplus x_3)$; both take values in $\{0,1\}$.

<a id="pdf-ffbe9c7b3306-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=1.00 -->
**Definition (1.1(m)).** $\mathrm{Sort}_4:\{-1,1\}^4\to\{-1,1\}$ equals $-1$ exactly when the coordinates are nondecreasing or nonincreasing.

<a id="pdf-ffbe9c7b3306-p034-b007"></a>
<!-- pdf-source: page=34; block=7; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p034-b008"></a>
<!-- pdf-source: page=34; block=8; confidence=1.00 -->
**Definition (1.1(o)).** The listed functions include $\mathrm{Maj}_5:\{-1,1\}^5\to\{-1,1\}$ and $\mathrm{Maj}_7:\{-1,1\}^7\to\{-1,1\}$.

<a id="pdf-ffbe9c7b3306-p034-b009"></a>
<!-- pdf-source: page=34; block=9; confidence=0.97 -->
**Definition (1.1(p)).** The complete quadratic function is \(\mathrm{CQ}_n:\mathbb F_2^n\to\{-1,1\}\), defined by \(\mathrm{CQ}_n(x)=\chi(\sum_{1\le i<j\le n}x_ix_j)\).

<a id="pdf-ffbe9c7b3306-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=1.00 -->
### 1.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=1.00 -->
**Exercise 1.2.** Count the functions $f:\{-1,1\}^n\to\{-1,1\}$ having exactly one nonzero Fourier coefficient.

<a id="pdf-ffbe9c7b3306-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.99 -->
**Exercise 1.3.** For $n>1$, a function $f:\mathbb F_2^n\to\{0,1\}$ with an odd number of inputs satisfying $f(x)=1$ has no zero Fourier coefficients.

<a id="pdf-ffbe9c7b3306-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=0.99 -->
**Exercise 1.4.** Extend $f:\{-1,1\}^n\to\mathbb R$ to $F:\mathbb R^n\to\mathbb R$ by $F(x)=\sum_{S\subseteq[n]}\widehat f(S)x^S$. For $\mu\in[-1,1]^n$, prove $F(\mu)=\mathbb E[f(y)]$ when the $y_i\in\{-1,1\}$ are independent with $\mathbb E[y_i]=\mu_i$.

<a id="pdf-ffbe9c7b3306-p035-b005"></a>
<!-- pdf-source: page=35; block=5; confidence=0.99 -->
**Exercise 1.5.** Prove that a $\{-1,1\}$-valued function has at most one Fourier coefficient of magnitude greater than $1/2$. Determine whether this extends to real-valued functions with $\|f\|_2=1$.

<a id="pdf-ffbe9c7b3306-p035-b006"></a>
<!-- pdf-source: page=35; block=6; confidence=1.00 -->
**Exercise 1.6.** Derive uniqueness of the Fourier expansion from Parseval's theorem.

<a id="pdf-ffbe9c7b3306-p035-b007"></a>
<!-- pdf-source: page=35; block=7; confidence=1.00 -->
**Exercise 1.7.** If the values $f(x)$ are independent uniform signs, prove for every $S\subseteq[n]$ that $\mathbb E[\widehat f(S)]=0$ and $\operatorname{Var}(\widehat f(S))=2^{-n}$. Hint: Parseval.

<a id="pdf-ffbe9c7b3306-p035-b008"></a>
<!-- pdf-source: page=35; block=8; confidence=0.99 -->
**Definitions (1.8).** For real-valued cube functions, set $f^\dagger(x)=-f(-x)$, $f^{\mathrm{odd}}(x)=(f(x)-f(-x))/2$, and $f^{\mathrm{even}}(x)=(f(x)+f(-x))/2$. Oddness means $f(-x)=-f(x)$, equivalently $f=f^\dagger$; evenness means $f(-x)=f(x)$.

<a id="pdf-ffbe9c7b3306-p035-b009"></a>
<!-- pdf-source: page=35; block=9; confidence=1.00 -->
**Exercise 1.8(a–c).** Express $\widehat{f^\dagger}(S)$ using $\widehat f(S)$. Verify $f=f^{\mathrm{odd}}+f^{\mathrm{even}}$ and that oddness/evenness is equivalent to equality with the corresponding part. Prove $f^{\mathrm{odd}}=\sum_{|S|\text{ odd}}\widehat f(S)\chi_S$ and $f^{\mathrm{even}}=\sum_{|S|\text{ even}}\widehat f(S)\chi_S$.

<a id="pdf-ffbe9c7b3306-p035-b010"></a>
<!-- pdf-source: page=35; block=10; confidence=0.99 -->
**Exercise 1.9(a).** Encoding False and True as $0,1\in\mathbb R$, use interpolation to represent every Boolean function by a real multilinear polynomial mapping $\{0,1\}^n$ into $\{0,1\}$:
$$q(x)=\sum_{S\subseteq[n]}c_S\prod_{i\in S}x_i.\tag{1.11}$$

<a id="pdf-ffbe9c7b3306-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.99 -->
**Exercise 1.9(b–d).** Prove uniqueness of (1.11) and $c_S\in\mathbb Z\cap[-2^n,2^n]$. For uniqueness, evaluate a nonzero polynomial on the indicator of an inclusion-minimal set with nonzero coefficient. If $p$ represents the same Boolean function with False/True encoded as $1,-1$, prove
$$q(x)=\frac12-\frac12p(1-2x_1,\ldots,1-2x_n).$$

<a id="pdf-ffbe9c7b3306-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.99 -->
**Definition (1.10).** For a nonzero real-valued cube function, $\deg(f)=\max\{|S|:\widehat f(S)\ne0\}$, the degree of its multilinear Fourier polynomial.

<a id="pdf-ffbe9c7b3306-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.99 -->
**Exercise 1.10(a–c).** Prove $\deg(f)=\deg(a+bf)$ for real $a,b$ with $b\ne0$ and $a+bf\not\equiv0$. Prove $\deg(f)\le k$ exactly when $f$ is a real linear combination of functions each depending on at most $k$ coordinates. Identify which functions of Exercise 1.1 satisfy $\deg(f)<n$.

<a id="pdf-ffbe9c7b3306-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.99 -->
**Exercise 1.11.** For sign-valued $f$ of degree $k\ge1$, prove that its $\{0,1\}$ representation $q$ also has degree $k$. Using 1.9(c–d), show $\widehat f(S)\in2^{1-k}\mathbb Z$ for all $S$, then establish $\sum_{S\subseteq[n]}|\widehat f(S)|\le2^{k-1}$.

<a id="pdf-ffbe9c7b3306-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.99 -->
**Definition (1.12).** A Hadamard matrix is a square real matrix with sign entries and mutually orthogonal rows. The Walsh–Hadamard matrices satisfy $H_1=[1]$ and
$$H_{2^{n+1}}=\begin{pmatrix}H_{2^n}&H_{2^n}\\H_{2^n}&-H_{2^n}\end{pmatrix}.$$

<a id="pdf-ffbe9c7b3306-p036-b006"></a>
<!-- pdf-source: page=36; block=6; confidence=0.98 -->
**Exercise 1.12(a–c).** Index rows and columns of \(H_{2^n}\) by integers \(0,\ldots,2^n-1\), identified with binary vectors in least-significant-bit-first order. Prove \((H_{2^n})_{\gamma,x}=(-1)^{\gamma\cdot x}\) and \(\widehat f=2^{-n}H_{2^n}f\). Give an algorithm computing \(H_{2^n}f\) using \(n2^n\) additions and subtractions.

<a id="pdf-ffbe9c7b3306-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.99 -->
The algorithm is the Fast Walsh–Hadamard Transform. Part (d) asks to show that taking the Fourier transform is an involution in the normalization of part (b): \(\widehat{\widehat f}=2^{-n}f\).

<a id="pdf-ffbe9c7b3306-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.99 -->
**Exercise 1.13.** For $f:\{-1,1\}^n\to\mathbb R$ and $0<p\le q<\infty$, prove $\|f\|_p\le\|f\|_q$ using Jensen with $t\mapsto t^{q/p}$. Extend to $q=\infty$, where $\|f\|_\infty=\max_x|f(x)|$.

<a id="pdf-ffbe9c7b3306-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=1.00 -->
Compute the means and variances of the functions in Exercise 1.1.

<a id="pdf-ffbe9c7b3306-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.99 -->
**Exercise 1.15.** If $g$ is obtained from $f:\{-1,1\}^n\to\mathbb R$ by fixing coordinates $K\subseteq[n]$ to $z\in\{-1,1\}^K$, prove $\mathbb E[g]=\sum_{T\subseteq K}\widehat f(T)z^T$.

<a id="pdf-ffbe9c7b3306-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=1.00 -->
**Exercise 1.16.** For Boolean-valued $f$, prove $\operatorname{Var}[f]=4\operatorname{dist}(f,1)\operatorname{dist}(f,-1)$ and derive Proposition 1.15.

<a id="pdf-ffbe9c7b3306-p037-b006"></a>
<!-- pdf-source: page=37; block=6; confidence=1.00 -->
**Exercise 1.17.** For a $\{-1,1\}$-valued random variable $F$ with mean $\mu$ and independent copy $F'$, prove
$$\operatorname{Var}[F]=\mathbb E[(F-\mu)^2]=\tfrac12\mathbb E[(F-F')^2]=2\Pr[F\ne F']=\mathbb E[|F-\mu|].$$
The first two equalities also hold without the Boolean-valued assumption.

<a id="pdf-ffbe9c7b3306-p037-b007"></a>
<!-- pdf-source: page=37; block=7; confidence=0.99 -->
**Exercise 1.18.** Prove orthogonality of homogeneous Fourier components: $\langle f^{=k},f^{=\ell}\rangle=W^k[f]$ when $k=\ell$, and $0$ otherwise.

<a id="pdf-ffbe9c7b3306-p037-b008"></a>
<!-- pdf-source: page=37; block=8; confidence=0.99 -->
**Exercise 1.19.** For Boolean-valued $f$: (a) prove $W^1[f]=1$ implies $f=\pm\chi_S$ for some singleton $S$; (b) prove $W^{\le1}[f]=1$ implies dependence on at most one coordinate; (c) determine whether $W^{\le2}[f]=1$ forces dependence on at most two or at most three coordinates, and examine the stronger assumption $W^2[f]=1$.

<a id="pdf-ffbe9c7b3306-p037-b009"></a>
<!-- pdf-source: page=37; block=9; confidence=0.97 -->
**Exercise 1.20.** If $f=f^{=1}$ is real-valued on the cube, prove $\operatorname{Var}[f^2]=2\sum_{i\ne j}\widehat f(i)^2\widehat f(j)^2$.

<a id="pdf-ffbe9c7b3306-p037-b010"></a>
<!-- pdf-source: page=37; block=10; confidence=1.00 -->
**Exercise 1.21.** Prove that a Boolean-valued function cannot have exactly two nonzero Fourier coefficients; investigate whether exactly three are possible.

<a id="pdf-ffbe9c7b3306-p037-b011"></a>
<!-- pdf-source: page=37; block=11; confidence=1.00 -->
Verify Propositions 1.25 and 1.26.

<a id="pdf-ffbe9c7b3306-p037-b012"></a>
<!-- pdf-source: page=37; block=12; confidence=0.99 -->
**Exercise 1.23(a).** For probability densities $\varphi,\psi$ on $\mathbb F_2^n$, define
$$d_{\mathrm{TV}}(\varphi,\psi)=\max_{A\subseteq\mathbb F_2^n}|\Pr_{y\sim\varphi}[y\in A]-\Pr_{y\sim\psi}[y\in A]|.$$
The requested norm identity continues on the next page.

<a id="pdf-ffbe9c7b3306-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->
**Exercise 1.23(a), continued.** Prove $d_{\mathrm{TV}}(\varphi,\psi)=\tfrac12\|\varphi-\psi\|_1$.

<a id="pdf-ffbe9c7b3306-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->
**Exercise 1.23(b).** For independent $y,y'\sim\varphi$, prove the collision probability is $\Pr[y=y']=\|\varphi\|_2^2/2^n$.

<a id="pdf-ffbe9c7b3306-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.98 -->
**Exercise 1.23(c).** For full-support \(\psi\), define \(d_{\chi^2}(\varphi,\psi)=\mathbb E_{y\sim\psi}[(\varphi(y)/\psi(y)-1)^2]\). Show that the \(\chi^2\)-distance of \(\varphi\) from uniform is \(\operatorname{Var}[\varphi]\).

<a id="pdf-ffbe9c7b3306-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.99 -->
**Exercise 1.23(d).** Prove $d_{\mathrm{TV}}(\varphi,\mathrm{uniform})\le\tfrac12\sqrt{\operatorname{Var}[\varphi]}$.

<a id="pdf-ffbe9c7b3306-p038-b005"></a>
<!-- pdf-source: page=38; block=5; confidence=1.00 -->
**Exercise 1.24.** If $A\subseteq\{-1,1\}^n$ has volume $\delta=\mathbb E[1_A]$ and the probability density $\varphi$ vanishes outside $A$, prove $\|\varphi\|_2^2\ge1/\delta$. Equality holds for the uniform density $\varphi_A$ on $A$.

<a id="pdf-ffbe9c7b3306-p038-b006"></a>
<!-- pdf-source: page=38; block=6; confidence=1.00 -->
**Exercise 1.25.** Prove associativity and commutativity of convolution directly from its definition.

<a id="pdf-ffbe9c7b3306-p038-b007"></a>
<!-- pdf-source: page=38; block=7; confidence=1.00 -->
Verify the equivalence of conditions (1) and (2) in Definition 1.28.

<a id="pdf-ffbe9c7b3306-p038-b008"></a>
<!-- pdf-source: page=38; block=8; confidence=0.99 -->
**Exercise 1.27.** Show that identifying an unknown linear function $f:\mathbb F_2^n\to\mathbb F_2$ through queries requires and can be achieved with $n$ queries.

<a id="pdf-ffbe9c7b3306-p038-b009"></a>
<!-- pdf-source: page=38; block=9; confidence=0.99 -->
**Exercise 1.28.** If $f:\mathbb F_2^n\to\{-1,1\}$ satisfies $\operatorname{dist}(f,\chi_{S^*})=\delta$, (a) use the union bound to prove $|\widehat f(S)|\le2\delta$ for every $S\ne S^*$; (b) derive BLR rejection probability at least $3\delta-10\delta^2+8\delta^3$; (c) show no universal lower bound $c\delta-O(\delta^2)$ is possible for $c>3$.

<a id="pdf-ffbe9c7b3306-p038-b010"></a>
<!-- pdf-source: page=38; block=10; confidence=0.99 -->
**Exercise 1.29(a).** An affine map $f:\mathbb F_2^n\to\mathbb F_2$ has form $f(x)=a\cdot x+b$. Prove this is equivalent to $f(x)+f(y)+f(z)=f(x+y+z)$ for all $x,y,z$.

<a id="pdf-ffbe9c7b3306-p038-b011"></a>
<!-- pdf-source: page=38; block=11; confidence=0.99 -->
**Exercise 1.29(b).** For real-valued $f$ on $\mathbb F_2^n$ and independent uniform $x,y,z$, prove
$$\mathbb E[f(x)f(y)f(z)f(x+y+z)]=\sum_S\widehat f(S)^4.$$

<a id="pdf-ffbe9c7b3306-p038-b012"></a>
<!-- pdf-source: page=38; block=12; confidence=0.98 -->
Give a 4-query test for \(f:\mathbb F_2^n\to\mathbb F_2\) such that acceptance probability at least \(1-\varepsilon\) implies \(f\) is \(\varepsilon\)-close to affine. All four query inputs should be uniform on \(\mathbb F_2^n\), though they need not be independent. Give an alternative where the fourth query is not random.

<a id="pdf-ffbe9c7b3306-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=1.00 -->
**Exercise 1.29(d), hint.** Establish that $f$ is affine exactly when $f(x)+f(y)+f(0)=f(x+y)$ for every $x,y\in\mathbb F_2^n$.

<a id="pdf-ffbe9c7b3306-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=1.00 -->
**Exercise 1.30.** For $\pi\in S_n$, set $(x^\pi)_i=x_{\pi(i)}$ and $f^\pi(x)=f(x^\pi)$. Boolean functions $g,h$ are permutation-isomorphic when $g=h^\pi$ for some $\pi$; define $\operatorname{Aut}(f)=\{\pi:f^\pi=f\}$. Part (a) asks to prove $\widehat{f^\pi}(S)=\widehat f(\pi^{-1}(S))$.

<a id="pdf-ffbe9c7b3306-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.99 -->
**Canonical-form construction.** List $(\widehat f(S))_{|S|=k}$ in lexicographic order of the $k$-subsets. Starting with $P_0=S_n$, retain in $P_k$ those $\pi\in P_{k-1}$ maximizing $(\widehat{f^\pi}(S))_{|S|=k}$ lexicographically, for $k=1,\ldots,n$. Define $\operatorname{can}(f)=f^\pi$ for any $\pi\in P_n$.

<a id="pdf-ffbe9c7b3306-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.99 -->
**Exercise 1.30(b–d).** Prove the construction is independent of the choice in $P_n$, produces a function isomorphic to $f$, and gives identical canonical forms for isomorphic functions. If the singleton coefficients $\widehat f(\{i\})$ are pairwise distinct, show the canonical form can be computed from the truth table in $\widetilde O(2^n)$ time.

<a id="pdf-ffbe9c7b3306-p039-b005"></a>
<!-- pdf-source: page=39; block=5; confidence=1.00 -->
Extend the exercise to isomorphism allowing independent coordinate sign changes: $g(x)=h(\pm x_{\pi(1)},\ldots,\pm x_{\pi(n)})$.

<a id="pdf-ffbe9c7b3306-p039-b006"></a>
<!-- pdf-source: page=39; block=6; confidence=0.98 -->
The notes connect Boolean Fourier analysis to Walsh's dyadic, $\{-1,1\}$-valued orthonormal basis of $L^2([0,1])$ [Wal23]. In Paley's ordering [Pal32], $w_n(x)=\prod_{i\ge0}r_i(x)^{n_i}$, where $n=\sum_{i\ge0}n_i2^i$, $r_i(x)=(-1)^{x_i}$, and non-dyadic $x=\sum_{i\ge0}x_i2^{-(i+1)}$.

<a id="pdf-ffbe9c7b3306-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.99 -->
Paley [Pal32] studied $L^p$ norms of truncated Walsh series; Vilenkin [Vil47] and Fine [Fin49] interpreted Walsh functions as group characters. Bonami [Bon68] and Kiener [Kie69] treated coordinates symmetrically, organizing $\chi_S$ by $|S|$ rather than $\max(S)$. Bonami also established Boolean-cube hypercontractivity (Chapter 9).

<a id="pdf-ffbe9c7b3306-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.99 -->
Boolean switching-function analysis originated in the 1930s. Muller [Mul54b] used Fourier coefficients to classify functions $f:\{0,1\}^4\to\{0,1\}$ under equivalences; Ninomiya [Nin58] and Golomb [Gol59] developed classification under isomorphisms, with Golomb connecting it to Walsh series (Exercise 1.30). Kahn–Kalai–Linial [KKL88] renewed its role in theoretical computer science.

<a id="pdf-ffbe9c7b3306-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.99 -->
Theorem 1.30 uses the analytic proof of Bellare–Coppersmith–Håstad–Kiwi–Sudan [BCH+96] for the Blum–Luby–Rubinfeld linearity test [BLR90], whose original analysis was combinatorial.

<a id="pdf-ffbe9c7b3306-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.99 -->
The analytic argument has antecedents in Roth [Rot53] for a cyclic group. Bellare et al. also strengthened the results of Theorem 1.30 and Exercise 1.28; Kaufman–Litsyn–Xie [KLX10] provided further improvements.

<a id="pdf-ffbe9c7b3306-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.99 -->
Exercise 1.1 attributes sortedness to Ambainis [Amb03, LLS06] and the hemi-icosahedron function to Kushilevitz [NW95]. The fast Fourier-transform algorithm in Exercise 1.12 is attributed to Lechner [Lec63].

<a id="pdf-ffbe9c7b3306-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=1.00 -->
Introduces influences and noise stability through voting rules, concluding with Kalai’s Fourier proof of Arrow’s theorem.

<a id="pdf-ffbe9c7b3306-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=1.00 -->
Social choice concerns aggregating individual preferences into a collective decision.

<a id="pdf-ffbe9c7b3306-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=1.00 -->
A map $f:\{-1,1\}^n\to\{-1,1\}$ models a two-candidate election: coordinates encode votes and the output selects the winner.

<a id="pdf-ffbe9c7b3306-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=1.00 -->
**Definition 2.1.** For odd $n$, $\operatorname{Maj}_n(x)=\operatorname{sgn}(\sum_{i=1}^n x_i)$. For even $n$, a majority function must agree with this sign whenever the sum is nonzero; ties are unrestricted.

<a id="pdf-ffbe9c7b3306-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=1.00 -->
**Definition 2.2.** With $-1$ encoding True, $\operatorname{AND}_n(x)$ is $-1$ exactly when every coordinate is $-1$, and otherwise $+1$. Likewise, $\operatorname{OR}_n(x)$ is $+1$ exactly when every coordinate is $+1$, and otherwise $-1$.

<a id="pdf-ffbe9c7b3306-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=1.00 -->
**Definition 2.3.** The $i$th dictator is the coordinate projection $\chi_i(x)=x_i$, with $\chi_i$ abbreviating $\chi_{\{i\}}$.

<a id="pdf-ffbe9c7b3306-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=1.00 -->
**Definition 2.4.** A function \(f:\{-1,1\}^n\to\{-1,1\}\) is a \(k\)-junta if it depends on at most \(k\) input coordinates; that is, \(f(x)=g(x_{i_1},\ldots,x_{i_k})\) for some \(g:\{-1,1\}^k\to\{-1,1\}\) and \(i_1,\ldots,i_k\in[n]\).

<a id="pdf-ffbe9c7b3306-p044-b004"></a>
<!-- pdf-source: page=44; block=4; confidence=1.00 -->
There are $2n+2$ Boolean $1$-juntas: the $n$ dictators, their $n$ negations, and the two constant functions.

<a id="pdf-ffbe9c7b3306-p044-b005"></a>
<!-- pdf-source: page=44; block=5; confidence=1.00 -->
**Definition 2.5.** A function \(f:\{-1,1\}^n\to\{-1,1\}\) is a weighted majority, or linear threshold function, if \(f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)\) for some real \(a_0,a_1,\ldots,a_n\).

<a id="pdf-ffbe9c7b3306-p044-b006"></a>
<!-- pdf-source: page=44; block=6; confidence=1.00 -->
Exercise 2.2 identifies majority, AND, OR, dictators, and constants as linear threshold functions.

<a id="pdf-ffbe9c7b3306-p044-b007"></a>
<!-- pdf-source: page=44; block=7; confidence=1.00 -->
**Definition 2.6.** Depth-$d$ recursive majority $\operatorname{Maj}_n^{\otimes d}$ acts on $n^d$ bits. Set $\operatorname{Maj}_n^{\otimes1}=\operatorname{Maj}_n$ and, for blocks $x^{(i)}\in\{-1,1\}^{n^d}$, define
$$\operatorname{Maj}_n^{\otimes(d+1)}(x^{(1)},\ldots,x^{(n)})=\operatorname{Maj}_n\bigl(\operatorname{Maj}_n^{\otimes d}(x^{(1)}),\ldots,\operatorname{Maj}_n^{\otimes d}(x^{(n)})\bigr).$$

<a id="pdf-ffbe9c7b3306-p045-b001"></a>
<!-- pdf-source: page=45; block=1; confidence=1.00 -->
**Definition 2.7.** For $s$ blocks of width $w$, define
$$\operatorname{Tribes}_{w,s}(x^{(1)},\ldots,x^{(s)})=\operatorname{OR}_s\bigl(\operatorname{AND}_w(x^{(1)}),\ldots,\operatorname{AND}_w(x^{(s)})\bigr),\qquad x^{(i)}\in\{-1,1\}^w.$$
Thus the output is True exactly when some block consists entirely of True votes.

<a id="pdf-ffbe9c7b3306-p045-b002"></a>
<!-- pdf-source: page=45; block=2; confidence=0.99 -->
**Definition 2.8.** A Boolean function is monotone if \(f(x)\le f(y)\) whenever \(x\le y\) coordinatewise; odd if \(f(-x)=-f(x)\); unanimous if \(f(1,\ldots,1)=1\) and \(f(-1,\ldots,-1)=-1\); and symmetric if \(f(x^\pi)=f(x)\) for all \(\pi\in S_n\), equivalently, it depends only on the number of 1s in \(x\). Monotonicity, oddness, and symmetry also apply to real-valued functions on the cube.

<a id="pdf-ffbe9c7b3306-p045-b003"></a>
<!-- pdf-source: page=45; block=3; confidence=1.00 -->
**Example 2.9.** Odd-arity majority has all four properties in Definition 2.8; May’s theorem (Exercise 2.3) characterizes it by monotonicity, oddness, and symmetry. Dictators and recursive majorities are monotone, odd, and unanimous. AND and OR are monotone, unanimous, and symmetric, but fail oddness. Tribes are monotone and unanimous, with a weaker symmetry described next.

<a id="pdf-ffbe9c7b3306-p045-b004"></a>
<!-- pdf-source: page=45; block=4; confidence=1.00 -->
**Definition 2.10.** A Boolean function is transitive-symmetric if, for every $i,i'\in[n]$, some permutation $\pi\in S_n$ satisfies $\pi(i)=i'$ and $f(x^\pi)=f(x)$ for every input $x$. Thus its coordinate-permutation symmetries act transitively on coordinates.

<a id="pdf-ffbe9c7b3306-p045-b005"></a>
<!-- pdf-source: page=45; block=5; confidence=1.00 -->
Under uniform votes, unbiasedness (Chapter 1.4) means the two outputs each have probability $1/2$.

<a id="pdf-ffbe9c7b3306-p045-b006"></a>
<!-- pdf-source: page=45; block=6; confidence=1.00 -->
**Definition 2.11.** Impartial culture models voters’ preferences as independent and uniformly distributed.

<a id="pdf-ffbe9c7b3306-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=1.00 -->
## 2.2. Influences and derivatives

<a id="pdf-ffbe9c7b3306-p046-b002"></a>
<!-- pdf-source: page=46; block=2; confidence=1.00 -->
**Definition 2.12.** Coordinate i is pivotal for f:{−1,1}ⁿ→{−1,1} at x when f(x)≠f(x^{⊕i}), where x^{⊕i} reverses only the ith bit.

<a id="pdf-ffbe9c7b3306-p046-b003"></a>
<!-- pdf-source: page=46; block=3; confidence=1.00 -->
**Definition 2.13.** The influence of coordinate i is its pivotality probability under uniform input:
\[\operatorname{Inf}_i[f]=\Pr_{x\sim\{-1,1\}^n}[f(x)\ne f(x^{\oplus i})].\]

<a id="pdf-ffbe9c7b3306-p046-b004"></a>
<!-- pdf-source: page=46; block=4; confidence=1.00 -->
**Fact 2.14.** For Boolean-valued f, Infᵢ[f] is the proportion of dimension-i cube edges that cross between opposite function values. Such edges have endpoints x and x^{⊕i}.

<a id="pdf-ffbe9c7b3306-p046-b005"></a>
<!-- pdf-source: page=46; block=5; confidence=1.00 -->
**Example 2.15.** Dictators χᵢ and their negatives have influence 1 at i and 0 elsewhere; constants have all influences 0. For every i, Infᵢ[ORₙ]=Infᵢ[ANDₙ]=2^{1−n}. In particular, the two inputs pivotal for coordinate 1 of ORₙ are (−1,1,…,1) and (1,1,…,1). Figure 2.1 shows two boundary edges per dimension for Maj₃.

<a id="pdf-ffbe9c7b3306-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=0.98 -->
For majority in higher dimensions, \(\operatorname{Inf}_i[\operatorname{Maj}_n]\) is the probability that among \(n-1\) random bits exactly half are 1; for large odd \(n\), this is roughly \(\sqrt{2/\pi}/\sqrt n\).

<a id="pdf-ffbe9c7b3306-p047-b002"></a>
<!-- pdf-source: page=47; block=2; confidence=1.00 -->
**Definition 2.16.** The discrete derivative is \(D_i f(x)=\frac{f(x^{(i\mapsto1)})-f(x^{(i\mapsto-1)})}{2}\). It does not depend on \(x_i\), and \(D_i(f+g)=D_if+D_ig\).

<a id="pdf-ffbe9c7b3306-p047-b003"></a>
<!-- pdf-source: page=47; block=3; confidence=1.00 -->
For Boolean-valued f,
\[D_i f(x)=\begin{cases}0,&i\text{ is not pivotal at }x,\\ \pm1,&i\text{ is pivotal at }x.\end{cases}\tag{2.1}\]
Thus (Dᵢf)² indicates pivotality and Infᵢ[f]=E[(Dᵢf)²].

<a id="pdf-ffbe9c7b3306-p047-b004"></a>
<!-- pdf-source: page=47; block=4; confidence=0.99 -->
**Definition 2.17.** Extend influence to real-valued cube functions by
\[\operatorname{Inf}_i[f]=\mathbb E_x[(D_i f(x))^2]=\|D_i f\|_2^2,\]
with uniform expectation.

<a id="pdf-ffbe9c7b3306-p047-b005"></a>
<!-- pdf-source: page=47; block=5; confidence=0.99 -->
**Definition 2.18.** Coordinate i is relevant for real-valued f iff Infᵢ[f]>0, equivalently f(x^{(i↦1)})≠f(x^{(i↦−1)}) for some x.

<a id="pdf-ffbe9c7b3306-p047-b006"></a>
<!-- pdf-source: page=47; block=6; confidence=0.99 -->
A real-valued cube function is monotone exactly when Dᵢf(x)≥0 for every coordinate i and input x.

<a id="pdf-ffbe9c7b3306-p047-b007"></a>
<!-- pdf-source: page=47; block=7; confidence=1.00 -->
**Proposition 2.19.** For the multilinear Fourier expansion f(x)=∑_{S⊆[n]} f̂(S)x^S,
\[D_i f(x)=\sum_{\substack{S\subseteq[n]\\i\in S}}\widehat f(S)x^{S\setminus\{i\}}.\tag{2.2}\]

<a id="pdf-ffbe9c7b3306-p047-b008"></a>
<!-- pdf-source: page=47; block=8; confidence=1.00 -->
**Proof.** Apply linearity to the monomial identity Dᵢx^S=x^{S∖{i}} when i∈S and Dᵢx^S=0 otherwise.

<a id="pdf-ffbe9c7b3306-p048-b001"></a>
<!-- pdf-source: page=48; block=1; confidence=0.99 -->
**Theorem 2.20.** For real-valued f on the cube and i∈[n],
\[\operatorname{Inf}_i[f]=\sum_{S\ni i}\widehat f(S)^2.\]
This follows by applying Parseval to (2.2).

<a id="pdf-ffbe9c7b3306-p048-b002"></a>
<!-- pdf-source: page=48; block=2; confidence=1.00 -->
**Proposition 2.21.** If f:{−1,1}ⁿ→{−1,1} is monotone, then Infᵢ[f]=f̂(i), with f̂(i) denoting f̂({i}).

<a id="pdf-ffbe9c7b3306-p048-b003"></a>
<!-- pdf-source: page=48; block=3; confidence=1.00 -->
**Proof.** Monotonicity makes Dᵢf the pivotality indicator in (2.1). Consequently
\[\operatorname{Inf}_i[f]=\mathbb E[D_i f]=\widehat{D_i f}(\varnothing)=\widehat f(i),\]
where the last identity uses Proposition 2.19.

<a id="pdf-ffbe9c7b3306-p048-b004"></a>
<!-- pdf-source: page=48; block=4; confidence=1.00 -->
**Proposition 2.22.** Every monotone, transitive-symmetric Boolean-valued f satisfies Infᵢ[f]≤1/√n for all i∈[n].

<a id="pdf-ffbe9c7b3306-p048-b005"></a>
<!-- pdf-source: page=48; block=5; confidence=1.00 -->
**Proof.** Transitive symmetry makes all singleton Fourier coefficients equal (Exercise 1.30(a)); Proposition 2.21 identifies them with influences. Parseval gives
\[1=\sum_S\widehat f(S)^2\ge\sum_{i=1}^n\widehat f(i)^2=n\widehat f(1)^2,\]
so every influence is at most 1/√n.

<a id="pdf-ffbe9c7b3306-p048-b006"></a>
<!-- pdf-source: page=48; block=6; confidence=1.00 -->
Proposition 2.58 and Exercise 2.24 sharpen this bound. Coordinate expectation operators are introduced for extension beyond the sign cube.

<a id="pdf-ffbe9c7b3306-p048-b007"></a>
<!-- pdf-source: page=48; block=7; confidence=0.99 -->
**Definition 2.23.** The linear coordinate expectation operator averages only the ith input bit:
\[E_i f(x)=\mathbb E_{b\sim\{-1,1\}}[f(x^{(i\mapsto b)})].\]
It extracts the component independent of coordinate i; the subsequent properties are assigned to Exercise 2.15.

<a id="pdf-ffbe9c7b3306-p049-b001"></a>
<!-- pdf-source: page=49; block=1; confidence=0.99 -->
**Proposition 2.24.** For real-valued functions on the cube,
\[
\mathrm E_i f(x)=\frac{f(x^{(i\mapsto1)})+f(x^{(i\mapsto-1)})}{2}
=\sum_{S:\,i\notin S}\widehat f(S)x^S,
\qquad f=x_iD_i f+\mathrm E_i f.
\]
Both \(D_i f\) and \(\mathrm E_i f\) are independent of \(x_i\), enabling induction on dimension.

<a id="pdf-ffbe9c7b3306-p049-b002"></a>
<!-- pdf-source: page=49; block=2; confidence=1.00 -->
**Definition 2.25.** The coordinate Laplacian is \(L_i f=f-\mathrm E_i f\); the opposite sign convention also occurs.

<a id="pdf-ffbe9c7b3306-p049-b003"></a>
<!-- pdf-source: page=49; block=3; confidence=1.00 -->
**Proposition 2.26.** For real-valued \(f\),
\[
L_i f(x)=\frac{f(x)-f(x^{\oplus i})}{2}
=x_iD_i f(x)=\sum_{S:\,i\in S}\widehat f(S)x^S,
\]
\[
\langle f,L_i f\rangle=\langle L_i f,L_i f\rangle=\operatorname{Inf}_i[f].
\]
Verification is assigned in Exercise 2.16.

<a id="pdf-ffbe9c7b3306-p049-b004"></a>
<!-- pdf-source: page=49; block=4; confidence=1.00 -->
## 2.3. Total influence

<a id="pdf-ffbe9c7b3306-p049-b005"></a>
<!-- pdf-source: page=49; block=5; confidence=0.99 -->
**Definition 2.27.** For \(f:\{-1,1\}^n\to\mathbb R\), total influence is
\[
\mathbf I[f]=\sum_{i=1}^n\operatorname{Inf}_i[f].
\]

<a id="pdf-ffbe9c7b3306-p049-b006"></a>
<!-- pdf-source: page=49; block=6; confidence=1.00 -->
**Proposition 2.28.** For Boolean-valued \(f\),
\[
\mathbf I[f]=\mathbb E_x[\operatorname{sens}_f(x)],
\]
where \(\operatorname{sens}_f(x)\) counts coordinates pivotal at \(x\). Thus total influence is average sensitivity.

<a id="pdf-ffbe9c7b3306-p050-b001"></a>
<!-- pdf-source: page=50; block=1; confidence=1.00 -->
**Proof.** Write each pivotal probability as an expected indicator and interchange the finite sum with expectation:
\[
\mathbf I[f]=\sum_i\Pr_x[f(x)\ne f(x^{\oplus i})]
=\mathbb E_x\!\left[\sum_i\mathbf1_{f(x)\ne f(x^{\oplus i})}\right]
=\mathbb E_x[\operatorname{sens}_f(x)].
\]

<a id="pdf-ffbe9c7b3306-p050-b002"></a>
<!-- pdf-source: page=50; block=2; confidence=1.00 -->
**Fact 2.29.** For Boolean-valued \(f\), the proportion of cube edges crossing between its two values is \(\mathbf I[f]/n\), by Fact 2.14.

<a id="pdf-ffbe9c7b3306-p050-b003"></a>
<!-- pdf-source: page=50; block=3; confidence=0.99 -->
**Example 2.30.** Boolean total influence lies in \([0,n]\): constants attain \(0\), parity and its negation attain \(n\), dictators and their negations have influence \(1\), and \(\mathrm{OR}_n,\mathrm{AND}_n\) have influence \(n2^{1-n}\). Majority has influence asymptotic to \(\sqrt{2/\pi}\sqrt n\).

<a id="pdf-ffbe9c7b3306-p050-b004"></a>
<!-- pdf-source: page=50; block=4; confidence=1.00 -->
**Proposition 2.31.** If Boolean-valued \(f\) is monotone, Proposition 2.21 gives
\[
\mathbf I[f]=\sum_{i=1}^n\widehat f(\{i\}).
\]

<a id="pdf-ffbe9c7b3306-p050-b005"></a>
<!-- pdf-source: page=50; block=5; confidence=1.00 -->
**Proposition 2.32.** For a two-candidate Boolean voting rule \(f\), let \(w(x)\) count votes agreeing with \(f(x)\). Under uniform votes,
\[
\mathbb E[w]=\frac n2+\frac12\sum_{i=1}^n\widehat f(\{i\}).
\]

<a id="pdf-ffbe9c7b3306-p050-b006"></a>
<!-- pdf-source: page=50; block=6; confidence=1.00 -->
**Proof.** The Fourier coefficient formula yields
\[
\sum_i\widehat f(\{i\})=\sum_i\mathbb E_x[f(x)x_i]
=\mathbb E_x[f(x)(x_1+\cdots+x_n)].\tag{2.3}
\]
The integrand is the winning vote count minus the losing count, hence \(2w(x)-n\); rearranging proves the formula.

<a id="pdf-ffbe9c7b3306-p051-b001"></a>
<!-- pdf-source: page=51; block=1; confidence=0.98 -->
**Theorem 2.33.** Among Boolean-valued functions, \(\sum_i\widehat f(\{i\})\) is maximized precisely by majority rules. Consequently, every monotone Boolean-valued \(f\) satisfies
\[
\mathbf I[f]\le\mathbf I[\mathrm{Maj}_n]
=\sqrt{\frac2\pi}\sqrt n+O(n^{-1/2}).
\]

<a id="pdf-ffbe9c7b3306-p051-b002"></a>
<!-- pdf-source: page=51; block=2; confidence=1.00 -->
**Proof.** Equation (2.3) gives
\[
\sum_i\widehat f(\{i\})=\mathbb E_x\!\left[f(x)\sum_i x_i\right]
\le\mathbb E_x\!\left[\left|\sum_i x_i\right|\right].
\]
Equality requires exactly \(f(x)=\operatorname{sgn}(\sum_i x_i)\) on inputs with nonzero vote sum; tied inputs are unrestricted. Proposition 2.31 and Exercise 2.22 supply the influence bound and asymptotic.

<a id="pdf-ffbe9c7b3306-p051-b003"></a>
<!-- pdf-source: page=51; block=3; confidence=1.00 -->
For real-valued cube functions,
\[
\mathbf I[f]=\sum_i\operatorname{Inf}_i[f]
=\sum_i\mathbb E_x[(D_i f(x))^2]
=\mathbb E_x\!\left[\sum_i(D_i f(x))^2\right].\tag{2.4}
\]

<a id="pdf-ffbe9c7b3306-p051-b004"></a>
<!-- pdf-source: page=51; block=4; confidence=0.99 -->
**Definition 2.34.** The discrete gradient of \(f:\{-1,1\}^n\to\mathbb R\) is
\[
\nabla f(x)=(D_1f(x),\ldots,D_nf(x))\in\mathbb R^n.
\]
For Boolean-valued \(f\), \(\|\nabla f(x)\|_2^2=\operatorname{sens}_f(x)\).

<a id="pdf-ffbe9c7b3306-p051-b005"></a>
<!-- pdf-source: page=51; block=5; confidence=1.00 -->
**Proposition 2.35.** Equation (2.4) implies, for real-valued \(f\),
\[
\mathbf I[f]=\mathbb E_x[\|\nabla f(x)\|_2^2].
\]

<a id="pdf-ffbe9c7b3306-p051-b006"></a>
<!-- pdf-source: page=51; block=6; confidence=0.99 -->
**Definition 2.36.** The linear Laplacian on real-valued cube functions is \(L=\sum_{i=1}^nL_i\).

<a id="pdf-ffbe9c7b3306-p051-b007"></a>
<!-- pdf-source: page=51; block=7; confidence=1.00 -->
**Proposition 2.37 (portion supplied).** For real-valued \(f\),
\[
Lf(x)=\frac n2\left(f(x)-\operatorname{avg}_{i\in[n]}f(x^{\oplus i})\right),
\qquad Lf=\sum_{S\subseteq[n]}|S|\widehat f(S)\chi_S.
\]
For Boolean-valued \(f\), additionally \(Lf(x)=f(x)\operatorname{sens}_f(x)\). Verification is assigned in Exercise 2.17.

<a id="pdf-ffbe9c7b3306-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.99 -->
The identity $\langle f,Lf\rangle=I[f]$ relates total influence to the Laplacian.

<a id="pdf-ffbe9c7b3306-p052-b002"></a>
<!-- pdf-source: page=52; block=2; confidence=0.99 -->
**Theorem 2.38.** For $f:\{-1,1\}^n\to\mathbb R$,
$$I[f]=\sum_{S\subseteq[n]}|S|\widehat f(S)^2=\sum_{k=0}^n kW^k[f].\tag{2.5}$$
For Boolean-valued $f$, this also equals $\mathbb E_{S\sim\mathcal S_f}|S|$.

<a id="pdf-ffbe9c7b3306-p052-b003"></a>
<!-- pdf-source: page=52; block=3; confidence=1.00 -->
**Proof.** Summing Theorem 2.20 over coordinates counts $\widehat f(S)^2$ exactly $|S|$ times.

<a id="pdf-ffbe9c7b3306-p052-b004"></a>
<!-- pdf-source: page=52; block=4; confidence=0.99 -->
**Poincaré Inequality.** Every real-valued cube function satisfies $\operatorname{Var}[f]\le I[f]$. Equality holds precisely when its Fourier support has degrees at most one, equivalently $W^{\le1}[f]=\mathbb E[f^2]$. For $\{-1,1\}$-valued functions, equality occurs exactly for $f=\pm1$ or $f=\pm\chi_i$.

<a id="pdf-ffbe9c7b3306-p052-b005"></a>
<!-- pdf-source: page=52; block=5; confidence=1.00 -->
**Proof.** Compare $\operatorname{Var}[f]=\sum_{k>0}W^k[f]$ from Proposition 1.13 with (2.5). The Boolean equality classification uses Exercise 1.19.

<a id="pdf-ffbe9c7b3306-p052-b006"></a>
<!-- pdf-source: page=52; block=6; confidence=0.98 -->
For a set $A$ of cube measure $\alpha$, its $\{-1,1\}$-valued indicator has variance $4\alpha(1-\alpha)$ and influence equal to $n$ times its fractional edge boundary. Poincaré therefore gives the dictator boundary bound at $\alpha=1/2$, but is not sharp for other nontrivial measures.

<a id="pdf-ffbe9c7b3306-p052-b007"></a>
<!-- pdf-source: page=52; block=7; confidence=0.99 -->
**Theorem 2.39.** If $f:\{-1,1\}^n\to\{-1,1\}$ and $\alpha=\min\{\Pr[f=1],\Pr[f=-1]\}$, then
$$2\alpha\log(1/\alpha)\le I[f].$$
This edge-isoperimetric bound is optimal when $\alpha=2^{-i}$.

<a id="pdf-ffbe9c7b3306-p052-b008"></a>
<!-- pdf-source: page=52; block=8; confidence=1.00 -->
The influence bound expresses the cube's small-set expansion: small sets have relatively large boundaries.

<a id="pdf-ffbe9c7b3306-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=1.00 -->
## 2.4. Noise stability

<a id="pdf-ffbe9c7b3306-p053-b002"></a>
<!-- pdf-source: page=53; block=2; confidence=1.00 -->
For uniform independent votes $x$, independently retain each vote with probability $\rho$ and otherwise replace it by a uniform bit; noise stability describes agreement between the original and recorded election outcomes.

<a id="pdf-ffbe9c7b3306-p053-b003"></a>
<!-- pdf-source: page=53; block=3; confidence=1.00 -->
**Definition 2.40.** For fixed $x$, write $y\sim N_\rho(x)$ when coordinates are independently chosen with
$$\Pr[y_i=x_i]=(1+\rho)/2,\qquad\Pr[y_i=-x_i]=(1-\rho)/2,$$
where $\rho\in[-1,1]$. For $\rho\ge0$, this is equivalent to retaining $x_i$ with probability $\rho$ and otherwise resampling uniformly. Such $y$ is $\rho$-correlated to $x$.

<a id="pdf-ffbe9c7b3306-p053-b004"></a>
<!-- pdf-source: page=53; block=4; confidence=1.00 -->
**Definition 2.41.** A $\rho$-correlated pair is sampled by taking uniform $x$ and then $y\sim N_\rho(x)$. Its law is symmetric in $x,y$; equivalently, coordinate pairs are independent and satisfy $\mathbb E[x_i]=\mathbb E[y_i]=0$ and $\mathbb E[x_iy_i]=\rho$.

<a id="pdf-ffbe9c7b3306-p053-b005"></a>
<!-- pdf-source: page=53; block=5; confidence=1.00 -->
**Definition 2.42.** For real-valued $f$ and $\rho\in[-1,1]$, define
$$\operatorname{Stab}_\rho[f]=\mathbb E_{(x,y)\ \rho\text{-correlated}}[f(x)f(y)].$$
For Boolean-valued $f$, this equals $\Pr[f(x)=f(y)]-\Pr[f(x)\ne f(y)]=2\Pr[f(x)=f(y)]-1$.

<a id="pdf-ffbe9c7b3306-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=1.00 -->
The noisy voting model preserves the outcome with probability $(1+\operatorname{Stab}_\rho[f])/2$.

<a id="pdf-ffbe9c7b3306-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=1.00 -->
**Definition 2.43.** For Boolean-valued $f$ and $\delta\in[0,1]$, noise sensitivity $\operatorname{NS}_\delta[f]$ is the probability of an output change when each coordinate of uniform $x$ is independently flipped with probability $\delta$. Thus
$$\operatorname{NS}_\delta[f]=\tfrac12-\tfrac12\operatorname{Stab}_{1-2\delta}[f].$$

<a id="pdf-ffbe9c7b3306-p054-b003"></a>
<!-- pdf-source: page=54; block=3; confidence=1.00 -->
**Example 2.44.** Constants $\pm1$ have stability $1$; dictators satisfy $\operatorname{Stab}_\rho[\chi_i]=\rho$ and $\operatorname{NS}_\delta[\chi_i]=\delta$. More generally, $\operatorname{Stab}_\rho[\chi_S]=\rho^{|S|}$.

<a id="pdf-ffbe9c7b3306-p054-b004"></a>
<!-- pdf-source: page=54; block=4; confidence=1.00 -->
**Proof.** Independence of the coordinate pairs gives
$$\mathbb E[x_Sy_S]=\mathbb E\prod_{i\in S}(x_iy_i)=\prod_{i\in S}\mathbb E[x_iy_i]=\rho^{|S|}.$$

<a id="pdf-ffbe9c7b3306-p054-b005"></a>
<!-- pdf-source: page=54; block=5; confidence=1.00 -->
**Theorem 2.45.** For $\rho\in[-1,1]$,
$$\lim_{\substack{n\to\infty\\n\text{ odd}}}\operatorname{Stab}_\rho[\operatorname{Maj}_n]=\frac2\pi\arcsin\rho=1-\frac2\pi\arccos\rho.$$
Equivalently, for $\delta\in[0,1]$,
$$\lim_{\substack{n\to\infty\\n\text{ odd}}}\operatorname{NS}_\delta[\operatorname{Maj}_n]=\frac1\pi\arccos(1-2\delta).$$

<a id="pdf-ffbe9c7b3306-p054-b006"></a>
<!-- pdf-source: page=54; block=6; confidence=1.00 -->
From $\cos z=1-z^2/2+O(z^4)$, obtain $\arccos(1-2\delta)=2\sqrt\delta+O(\delta^{3/2})$. Consequently, as $\delta\to0$,
$$\lim_{\substack{n\to\infty\\n\text{ odd}}}\operatorname{NS}_\delta[\operatorname{Maj}_n]=\frac2\pi\sqrt\delta+O(\delta^{3/2}).$$

<a id="pdf-ffbe9c7b3306-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=1.00 -->
## 2.4. Noise stability

<a id="pdf-ffbe9c7b3306-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=1.00 -->
**Definition 2.46.** For \(\rho\in[-1,1]\), the noise operator on real-valued functions is \(T_\rho f(x)=\mathbb E_{y\sim N_\rho(x)}[f(y)]\).

<a id="pdf-ffbe9c7b3306-p055-b003"></a>
<!-- pdf-source: page=55; block=3; confidence=1.00 -->
**Proposition 2.47.** The noise operator multiplies degree-\(k\) Fourier components by \(\rho^k\):
\[
T_\rho f=\sum_{S\subseteq[n]}\rho^{|S|}\widehat f(S)\chi_S
=\sum_{k=0}^n\rho^k f^{=k}.
\]

<a id="pdf-ffbe9c7b3306-p055-b004"></a>
<!-- pdf-source: page=55; block=4; confidence=1.00 -->
**Proof.** By linearity, check characters. Independence of the noisy coordinates and \(\mathbb E[y_i]=\rho x_i\) give
\[
T_\rho\chi_S(x)=\mathbb E\!\left[\prod_{i\in S}y_i\right]
=\prod_{i\in S}(\rho x_i)=\rho^{|S|}\chi_S(x).
\]

<a id="pdf-ffbe9c7b3306-p055-b005"></a>
<!-- pdf-source: page=55; block=5; confidence=1.00 -->
**Derivation.** Conditioning on uniform \(x\) yields
\[
\operatorname{Stab}_\rho[f]
=\mathbb E_{x,y\sim N_\rho(x)}[f(x)f(y)]
=\mathbb E_x\!\left[f(x)\mathbb E_{y\sim N_\rho(x)}f(y)\right].
\]

<a id="pdf-ffbe9c7b3306-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=1.00 -->
**Fact 2.48.** \(\operatorname{Stab}_\rho[f]=\langle f,T_\rho f\rangle\).

<a id="pdf-ffbe9c7b3306-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.99 -->
**Theorem 2.49.** For real-valued cube functions,
\[
\operatorname{Stab}_\rho[f]
=\sum_{S\subseteq[n]}\rho^{|S|}\widehat f(S)^2
=\sum_{k=0}^n\rho^k W^k[f].
\]
For Boolean-valued \(f\), this implies
\[
\operatorname{Stab}_\rho[f]=\mathbb E_{S\sim\mathcal S_f}[\rho^{|S|}]\tag{2.6}
\]
and
\[
\operatorname{NS}_\delta[f]
=\frac12\sum_{k=0}^n\bigl(1-(1-2\delta)^k\bigr)W^k[f].\tag{2.7}
\]

<a id="pdf-ffbe9c7b3306-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=1.00 -->
**Proof.** Apply Plancherel to Fact 2.48 and the Fourier multipliers in Proposition 2.47.

<a id="pdf-ffbe9c7b3306-p056-b004"></a>
<!-- pdf-source: page=56; block=4; confidence=1.00 -->
**Proposition 2.50.** If \(0<\rho<1\) and Boolean-valued \(f\) is unbiased, then \(\operatorname{Stab}_\rho[f]\le\rho\). Equality holds exactly when \(f=\pm\chi_i\) for some \(i\in[n]\).

<a id="pdf-ffbe9c7b3306-p056-b005"></a>
<!-- pdf-source: page=56; block=5; confidence=1.00 -->
**Proof.** Unbiasedness removes \(W^0[f]\). Since \(\rho^k<\rho\) for \(k>1\), equality requires all Fourier weight in degree one; Exercise 1.19(a) identifies such Boolean functions as \(\pm\chi_i\).

<a id="pdf-ffbe9c7b3306-p056-b006"></a>
<!-- pdf-source: page=56; block=6; confidence=1.00 -->
The Fourier formula makes \(\operatorname{Stab}_\rho[f]\) a polynomial with nonnegative coefficients, hence nondecreasing on \([0,1]\).

<a id="pdf-ffbe9c7b3306-p056-b007"></a>
<!-- pdf-source: page=56; block=7; confidence=1.00 -->
**Proposition 2.51.** For real-valued cube functions,
\[
\left.\frac{d}{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=0}=W^1[f],
\qquad
\left.\frac{d}{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=1}=I[f].
\]
For Boolean-valued \(f\), \(\operatorname{NS}_\delta[f]\) is nondecreasing on \([0,1/2]\), and the second identity equivalently states
\[
\left.\frac{d}{d\delta}\operatorname{NS}_\delta[f]\right|_{\delta=0}=I[f].
\]

<a id="pdf-ffbe9c7b3306-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.99 -->
**Definition 2.52.** For real-valued \(f\), \(\rho\in[0,1]\), and \(i\in[n]\), define
\[
\operatorname{Inf}^{(\rho)}_i[f]
=\operatorname{Stab}_\rho[D_i f]
=\sum_{S\ni i}\rho^{|S|-1}\widehat f(S)^2,
\qquad
I^{(\rho)}[f]=\sum_{i=1}^n\operatorname{Inf}^{(\rho)}_i[f],
\]
using \(0^0=1\).

<a id="pdf-ffbe9c7b3306-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=1.00 -->
**Fact 2.53.**
\[
I^{(\rho)}[f]=\frac{d}{d\rho}\operatorname{Stab}_\rho[f]
=\sum_{k=1}^n k\rho^{k-1}W^k[f].
\]

<a id="pdf-ffbe9c7b3306-p057-b003"></a>
<!-- pdf-source: page=57; block=3; confidence=1.00 -->
As \(\rho\) runs from \(0\) to \(1\), \(\operatorname{Inf}^{(\rho)}_i[f]\) increases from \(\widehat f(\{i\})^2\) to \(\operatorname{Inf}_i[f]\).

<a id="pdf-ffbe9c7b3306-p057-b004"></a>
<!-- pdf-source: page=57; block=4; confidence=1.00 -->
**Proposition 2.54.** Suppose \(\operatorname{Var}[f]\le1\). Given \(0<\delta,\varepsilon\le1\), let \(J=\{i\in[n]:\operatorname{Inf}^{(1-\delta)}_i[f]\ge\varepsilon\}\). Then \(|J|\le1/(\delta\varepsilon)\).

<a id="pdf-ffbe9c7b3306-p057-b005"></a>
<!-- pdf-source: page=57; block=5; confidence=0.99 -->
**Proof.** Since \(|J|\le I^{(1-\delta)}[f]/\varepsilon\), bound the latter total influence by \(1/\delta\). Compare Fact 2.53 termwise with \(\operatorname{Var}[f]=\sum_{k\ge1}W^k[f]\le1\), using
\[
k(1-\delta)^{k-1}\le1/\delta\qquad(k\ge1),
\]
as supplied by Exercise 2.45.

<a id="pdf-ffbe9c7b3306-p057-b006"></a>
<!-- pdf-source: page=57; block=6; confidence=1.00 -->
The bound on notable coordinates fails for ordinary influences: parity \(\chi_{[n]}\) has influence \(1\) in every coordinate.

<a id="pdf-ffbe9c7b3306-p057-b007"></a>
<!-- pdf-source: page=57; block=7; confidence=1.00 -->
## 2.5. Highlight: Arrow’s Theorem

<a id="pdf-ffbe9c7b3306-p057-b008"></a>
<!-- pdf-source: page=57; block=8; confidence=1.00 -->
The section introduces aggregation of \(n\) voters’ rankings of three candidates \(a,b,c\) into a winning candidate.

<a id="pdf-ffbe9c7b3306-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=1.00 -->
**Condorcet election setup.** Apply the same rule $f:\{-1,1\}^n\to\{-1,1\}$ to pairwise vote vectors $x,y,z$ for $a$ versus $b$, $b$ versus $c$, and $c$ versus $a$. Each voter's strict ranking gives one of the six nonconstant triples $(x_i,y_i,z_i)$, exactly those satisfying $\mathrm{NAE}_3$. The collective pairwise outcome is $(f(x),f(y),f(z))$.

<a id="pdf-ffbe9c7b3306-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=1.00 -->
**Definition 2.55.** A Condorcet winner is a candidate that defeats every other candidate in its pairwise elections under $f$.

<a id="pdf-ffbe9c7b3306-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=1.00 -->
A three-candidate election has no Condorcet winner exactly when $(f(x),f(y),f(z))$ is all $+1$ or all $-1$, producing a preference cycle. Majority can produce such a cycle even though each voter's ranking is transitive.

<a id="pdf-ffbe9c7b3306-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=1.00 -->
**Arrow's Theorem.** If a unanimous rule $f:\{-1,1\}^n\to\{-1,1\}$ always yields a Condorcet winner in three-candidate elections, then $f$ is a dictatorship.

<a id="pdf-ffbe9c7b3306-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=1.00 -->
**Impartial culture.** Voters independently select uniformly from the six strict rankings of three candidates; Kalai's proof analyzes the resulting winner probability.

<a id="pdf-ffbe9c7b3306-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=1.00 -->
**Theorem 2.56.** Under impartial culture, a three-candidate Condorcet election using $f:\{-1,1\}^n\to\{-1,1\}$ has winner probability
$$\Pr[\exists\text{ Condorcet winner}]=\frac34-\frac34\operatorname{Stab}_{-1/3}[f].$$

<a id="pdf-ffbe9c7b3306-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=1.00 -->
**Proof.** The triples $(x_i,y_i,z_i)$ are independent and uniform over $\mathrm{NAE}_3^{-1}(1)$, so
$$\Pr[\exists\text{ winner}]=\mathbb E[\mathrm{NAE}_3(f(x),f(y),f(z))].\tag{2.8}$$
Using
$$\mathrm{NAE}_3(w)=\frac34-\frac14(w_1w_2+w_1w_3+w_2w_3),$$
(2.8) equals $\frac34-\frac14(\mathbb E[f(x)f(y)]+\mathbb E[f(x)f(z)]+\mathbb E[f(y)f(z)])$. Each pair of vote vectors has independent coordinate pairs with unbiased marginals and correlation $\frac26-\frac46=-\frac13$. Thus each expectation is $\operatorname{Stab}_{-1/3}[f]$.

<a id="pdf-ffbe9c7b3306-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=1.00 -->
**Proof of Arrow's Theorem.** An always-existing winner implies
$$1=\frac34-\frac34\sum_{k=0}^n(-1/3)^kW^k[f].$$
Since $(-1/3)^k\ge-1/3$, with equality only at $k=1$, all Fourier weight must lie at degree one: $W^1[f]=1$. Exercise 1.19(a) then gives $f=\pm\chi_i$; unanimity excludes the negative sign.

<a id="pdf-ffbe9c7b3306-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=1.00 -->
Combining Theorem 2.56 with Theorem 2.45 gives the limiting winner probability for majority.

<a id="pdf-ffbe9c7b3306-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=1.00 -->
**Guilbaud's Formula.** For three-candidate Condorcet elections using $\mathrm{Maj}_n$, the winner probability converges as $n\to\infty$ to
$$\frac{3}{2\pi}\arccos(-1/3)\approx91.2\%.$$

<a id="pdf-ffbe9c7b3306-p060-b002"></a>
<!-- pdf-source: page=60; block=2; confidence=0.99 -->
**Theorem 2.57.** If all singleton Fourier coefficients $\widehat f(i)$ are equal, then the three-candidate Condorcet winner probability is at most
$$\frac79+\frac{4}{9\pi}+o_n(1)\approx91.9\%.$$

<a id="pdf-ffbe9c7b3306-p060-b003"></a>
<!-- pdf-source: page=60; block=3; confidence=1.00 -->
Equal singleton coefficients hold for transitive-symmetric rules and for monotone rules with equal influences. Later sections relax this hypothesis (§5.4) and sharpen the bound to majority's limiting value (§11.7). Theorem 2.57 follows from Proposition 2.58 and Corollary 2.59.

<a id="pdf-ffbe9c7b3306-p060-b004"></a>
<!-- pdf-source: page=60; block=4; confidence=1.00 -->
**Proposition 2.58.** If $f:\{-1,1\}^n\to\{-1,1\}$ has equal singleton Fourier coefficients, then
$$W^1[f]\le\frac2\pi+o_n(1).$$
The source identifies this as Exercise 2.24.

<a id="pdf-ffbe9c7b3306-p060-b005"></a>
<!-- pdf-source: page=60; block=5; confidence=1.00 -->
**Corollary 2.59.** For any rule $f:\{-1,1\}^n\to\{-1,1\}$, the three-candidate Condorcet winner probability is at most
$$\frac79+\frac29W^1[f].$$

<a id="pdf-ffbe9c7b3306-p060-b006"></a>
<!-- pdf-source: page=60; block=6; confidence=1.00 -->
**Proof.** Expand Theorem 2.56 by Fourier degree and discard the nonpositive even-degree contributions:
$$\begin{aligned}
\Pr[\exists\text{ winner}]&=\frac34-\frac34\left(W^0[f]-\frac13W^1[f]+\frac19W^2[f]-\frac1{27}W^3[f]+\cdots\right)\\
&\le\frac34+\frac14W^1[f]+\frac1{36}W^3[f]+\frac1{324}W^5[f]+\cdots\\
&\le\frac34+\frac14W^1[f]+\frac1{36}\sum_{\substack{k\ge3\\k\text{ odd}}}W^k[f]\\
&\le\frac34+\frac14W^1[f]+\frac1{36}(1-W^1[f])
=\frac79+\frac29W^1[f].
\end{aligned}$$

<a id="pdf-ffbe9c7b3306-p060-b007"></a>
<!-- pdf-source: page=60; block=7; confidence=0.99 -->
**Corollary 2.60.** If the three-candidate Condorcet winner probability for $f:\{-1,1\}^n\to\{-1,1\}$ is $1-\epsilon$, then $f$ is $O(\epsilon)$-close to $\pm\chi_i$ for some $i\in[n]$.

<a id="pdf-ffbe9c7b3306-p060-b008"></a>
<!-- pdf-source: page=60; block=8; confidence=1.00 -->
**Proof.** Corollary 2.59 implies $W^1[f]\ge1-\frac92\epsilon$; the FKN theorem then gives $O(\epsilon)$-closeness to a dictator or its negation.

<a id="pdf-ffbe9c7b3306-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=1.00 -->
**FKN Theorem.** If Boolean-valued $f$ on $\{-1,1\}^n$ satisfies $W^1[f]\ge 1-\delta$, then $f$ is $O(\delta)$-close to some $\pm\chi_i$.

<a id="pdf-ffbe9c7b3306-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=1.00 -->
The proof is deferred to §9.1; §5.4 improves the closeness bound to $\delta/4+O(\delta^2\log(2/\delta))$.

<a id="pdf-ffbe9c7b3306-p061-b003"></a>
<!-- pdf-source: page=61; block=3; confidence=1.00 -->
## 2.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p061-b004"></a>
<!-- pdf-source: page=61; block=4; confidence=1.00 -->
**Exercise 2.1.** Classify the functions of Exercise 1.1 by oddness, transitive symmetry, and symmetry.

<a id="pdf-ffbe9c7b3306-p061-b005"></a>
<!-- pdf-source: page=61; block=5; confidence=1.00 -->
**Exercise 2.2.** Prove that majority, AND, OR, $\pm\chi_i$, and $\pm1$ are linear threshold functions.

<a id="pdf-ffbe9c7b3306-p061-b006"></a>
<!-- pdf-source: page=61; block=6; confidence=1.00 -->
**Exercise 2.3 (May’s theorem).** (a) A Boolean function is symmetric and monotone exactly when it has a weighted-majority representation with every input weight equal to $1$. (b) Adding oddness forces $n$ odd and $f=\operatorname{Maj}_n$.

<a id="pdf-ffbe9c7b3306-p061-b007"></a>
<!-- pdf-source: page=61; block=7; confidence=0.99 -->
**Exercise 2.4.** Define a Hamming ball by $A=\{x:\Delta(x,z)<r\}$ for a center $z$ and real radius $r$. Prove that its Boolean indicator is precisely a threshold function $\operatorname{sgn}(a_0+\sum_i a_ix_i)$ admitting $|a_1|=\cdots=|a_n|$.

<a id="pdf-ffbe9c7b3306-p061-b008"></a>
<!-- pdf-source: page=61; block=8; confidence=0.98 -->
**Exercise 2.5.** A Boolean function is unate in coordinate \(i\) if it is monotone or antimonotone in that coordinate. (a) Show \(|\widehat f(i)|\le\operatorname{Inf}_i[f]\), with equality exactly when \(f\) is unate in coordinate \(i\). (b) Show that the second statement of Theorem 2.33 holds for every unate \(f\).

<a id="pdf-ffbe9c7b3306-p061-b009"></a>
<!-- pdf-source: page=61; block=9; confidence=1.00 -->
**Exercise 2.6.** Prove that every linear threshold function is unate.

<a id="pdf-ffbe9c7b3306-p061-b010"></a>
<!-- pdf-source: page=61; block=10; confidence=1.00 -->
**Exercise 2.7.** Calculate $\operatorname{Inf}_1[f]$ for each function from Exercise 1.1.

<a id="pdf-ffbe9c7b3306-p061-b011"></a>
<!-- pdf-source: page=61; block=11; confidence=1.00 -->
**Exercise 2.8.** For Boolean $f$, prove $\operatorname{Inf}_i[f]\le\operatorname{Var}[f]$ without Fourier identities. Suggested intermediate bound: $\operatorname{Inf}_i[f]\le2\min\{\Pr[f=-1],\Pr[f=1]\}$.

<a id="pdf-ffbe9c7b3306-p061-b012"></a>
<!-- pdf-source: page=61; block=12; confidence=1.00 -->
**Exercise 2.9.** Compute all six influences of $f:\{0,1\}^6\to\{-1,1\}$ given by $f(x)=\operatorname{sgn}(-58+31x_1+31x_2+28x_3+21x_4+2x_5+2x_6)$.

<a id="pdf-ffbe9c7b3306-p061-b013"></a>
<!-- pdf-source: page=61; block=13; confidence=1.00 -->
**Exercise 2.10.** Coordinate $i$ is $b$-pivotal at $x$ when $f(x)=b$ and $f(x^{\oplus i})\ne b$. Prove $\Pr_x[i\text{ is }b\text{-pivotal}]=\tfrac12\operatorname{Inf}_i[f]$ and hence $\mathbf I[f]=2\mathbb E_x[\#\{b\text{-pivotal coordinates at }x\}]$.

<a id="pdf-ffbe9c7b3306-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=1.00 -->
**Exercise 2.11.** For Boolean $f$, $\widehat f(S)\ne0$ implies that every $i\in S$ is a relevant coordinate.

<a id="pdf-ffbe9c7b3306-p062-b002"></a>
<!-- pdf-source: page=62; block=2; confidence=1.00 -->
**Exercise 2.12.** For a random Boolean function sampled as in Exercise 1.7, calculate $\mathbb E[\operatorname{Inf}_1[f]]$ and $\mathbb E[\mathbf I[f]]$.

<a id="pdf-ffbe9c7b3306-p062-b003"></a>
<!-- pdf-source: page=62; block=3; confidence=1.00 -->
**Exercise 2.13.** Let \(n=w2^w\) and \(f=\operatorname{Tribes}_{w,2^w}\). (a) Compute \(\mathbb E[f]\) and \(\operatorname{Var}[f]\), and estimate them asymptotically. (b) Describe \(D_1f\). (c) Compute \(\operatorname{Inf}_1[f]\) and \(I[f]\), with asymptotic estimates.

<a id="pdf-ffbe9c7b3306-p062-b004"></a>
<!-- pdf-source: page=62; block=4; confidence=0.99 -->
**Exercise 2.14.** For real-valued $f$ and $g=|f|$, prove pointwise $|D_ig|\le|D_if|$; conclude $\operatorname{Inf}_i[g]\le\operatorname{Inf}_i[f]$ and $\mathbf I[g]\le\mathbf I[f]$.

<a id="pdf-ffbe9c7b3306-p062-b005"></a>
<!-- pdf-source: page=62; block=5; confidence=1.00 -->
Prove Proposition 2.24.

<a id="pdf-ffbe9c7b3306-p062-b006"></a>
<!-- pdf-source: page=62; block=6; confidence=1.00 -->
Prove Proposition 2.26.

<a id="pdf-ffbe9c7b3306-p062-b007"></a>
<!-- pdf-source: page=62; block=7; confidence=1.00 -->
Prove Proposition 2.37.

<a id="pdf-ffbe9c7b3306-p062-b008"></a>
<!-- pdf-source: page=62; block=8; confidence=0.99 -->
**Exercise 2.18.** For real-valued $f$, establish $Lf(x)=\left.\frac{d}{d\rho}T_\rho f(x)\right|_{\rho=1}=-\left.\frac{d}{dt}T_{e^{-t}}f(x)\right|_{t=0}$.

<a id="pdf-ffbe9c7b3306-p062-b009"></a>
<!-- pdf-source: page=62; block=9; confidence=0.99 -->
**Exercise 2.19.** If real-valued $f$ is independent of coordinate $i$ and $g$ of coordinate $j\ne i$, prove $\mathbb E[x_ix_jf(x)g(x)]=\mathbb E[D_jf(x)D_ig(x)]$.

<a id="pdf-ffbe9c7b3306-p062-b010"></a>
<!-- pdf-source: page=62; block=10; confidence=1.00 -->
**Exercise 2.20.** For Boolean $f$ and $S\sim\mathcal S_f$, the known identity $\mathbb E[\operatorname{sens}_f(x)]=\mathbb E[|S|]$ extends to $\mathbb E[\operatorname{sens}_f(x)^2]=\mathbb E[|S|^2]$. Prove this using Proposition 2.37, and determine whether the analogous third-moment equality holds.

<a id="pdf-ffbe9c7b3306-p062-b011"></a>
<!-- pdf-source: page=62; block=11; confidence=0.99 -->
**Exercise 2.21.** For real-valued $f$, define $\operatorname{Var}_if(x)=\operatorname{Var}_{x_i}[f(x)]$ with other coordinates fixed. Prove (a) $\operatorname{Inf}_i[f]=\mathbb E_x[\operatorname{Var}_if(x)]$ and (b) $\operatorname{Inf}_i[f]=\tfrac12\mathbb E_{x_i,x_i'}[\|f|_{x_i}-f|_{x_i'}\|_2^2]$, where the two bits are independent uniform samples and each restriction has $n-1$ variables.

<a id="pdf-ffbe9c7b3306-p062-b012"></a>
<!-- pdf-source: page=62; block=12; confidence=0.98 -->
**Exercise 2.22(a–d).** For odd $n$, prove $\operatorname{Inf}_i[\operatorname{Maj}_n]=2^{1-n}\binom{n-1}{(n-1)/2}$ and that this decreases with $n$. Using $m!=(m/e)^m(\sqrt{2\pi m}+O(m^{-1/2}))$, derive $\operatorname{Inf}_1[\operatorname{Maj}_n]=\sqrt{2/\pi}/\sqrt n+O(n^{-3/2})$, with nonnegative error terms, and $2/\pi\le W^1[\operatorname{Maj}_n]\le2/\pi+O(n^{-1})$.

<a id="pdf-ffbe9c7b3306-p063-b001"></a>
<!-- pdf-source: page=63; block=1; confidence=0.96 -->
**Exercise 2.22(e–f).** (e) Deduce $\sqrt{2/\pi}\sqrt n\le\mathbf I[\operatorname{Maj}_n]\le\sqrt{2/\pi}\sqrt n+O(n^{-1/2})$. (f) For even $n$ and a majority function $f$, prove $\mathbf I[f]=\mathbf I[\operatorname{Maj}_{n-1}]=\sqrt{2/\pi}\sqrt n+O(n^{-1/2})$.

<a id="pdf-ffbe9c7b3306-p063-b002"></a>
<!-- pdf-source: page=63; block=2; confidence=1.00 -->
**Exercise 2.23.** Use only Cauchy–Schwarz and Parseval to prove $\mathbf I[f]\le\sqrt n$ for monotone Boolean $f$, then extend the bound to unate $f$ using Exercise 2.5.

<a id="pdf-ffbe9c7b3306-p063-b003"></a>
<!-- pdf-source: page=63; block=3; confidence=0.98 -->
**Exercise 2.24.** Prove Proposition 2.58 with an \(O(n^{-1})\) error in place of \(o_n(1)\). The hint is to show \(\widehat f(i)\le\sqrt{2/\pi}/\sqrt n+O(n^{-3/2})\) using Theorem 2.33.

<a id="pdf-ffbe9c7b3306-p063-b004"></a>
<!-- pdf-source: page=63; block=4; confidence=0.99 -->
**Exercise 2.25.** From Exercise 1.4, derive $T_\rho f(x)=\sum_S\rho^{|S|}\widehat f(S)x^S$.

<a id="pdf-ffbe9c7b3306-p063-b005"></a>
<!-- pdf-source: page=63; block=5; confidence=1.00 -->
**Exercise 2.26.** Calculate $\mathbf I[f]$ for each function of Exercise 1.1.

<a id="pdf-ffbe9c7b3306-p063-b006"></a>
<!-- pdf-source: page=63; block=6; confidence=1.00 -->
**Exercise 2.27.** Identify the Boolean functions maximizing $\mathbf I[f]$ subject to $|f^{-1}(1)|=3$.

<a id="pdf-ffbe9c7b3306-p063-b007"></a>
<!-- pdf-source: page=63; block=7; confidence=0.99 -->
**Exercise 2.28.** For even real-valued $f$ on the cube, prove $\operatorname{Var}[f]\le\tfrac12\mathbf I[f]$.

<a id="pdf-ffbe9c7b3306-p063-b008"></a>
<!-- pdf-source: page=63; block=8; confidence=0.98 -->
**Exercise 2.29.** For unbiased Boolean $f$, set $M=\operatorname{MaxInf}[f]=\max_i\operatorname{Inf}_i[f]$. (a) Poincaré gives $M\ge1/n$. (b) Prove $\mathbf I[f]\ge2-nM^2$ and deduce $M\ge2/n-4/n^2$. Suggested route: $\mathbf I[f]\ge W^1[f]+2(1-W^1[f])$, followed by Exercise 2.5.

<a id="pdf-ffbe9c7b3306-p063-b009"></a>
<!-- pdf-source: page=63; block=9; confidence=1.00 -->
**Exercise 2.30.** Deduce \(E_if=\sum_{S\not\ni i}\widehat f(S)\chi_S\) and \(T_\rho f=\sum_S\rho^{|S|}\widehat f(S)\chi_S\).

<a id="pdf-ffbe9c7b3306-p063-b010"></a>
<!-- pdf-source: page=63; block=10; confidence=1.00 -->
**Exercise 2.31.** Prove $f\ge0\Rightarrow T_\rho f\ge0$ for $\rho\in[-1,1]$; for $\rho\in(-1,1)$, strengthen this to $T_\rho f>0$ whenever $f\ge0$ and $f\not\equiv0$.

<a id="pdf-ffbe9c7b3306-p063-b011"></a>
<!-- pdf-source: page=63; block=11; confidence=1.00 -->
**Exercise 2.32.** Prove the composition identity $T_{\rho_1}T_{\rho_2}=T_{\rho_1\rho_2}$.

<a id="pdf-ffbe9c7b3306-p063-b012"></a>
<!-- pdf-source: page=63; block=12; confidence=0.99 -->
**Exercise 2.33.** For $\rho\in[-1,1]$ and $p\ge1$, prove $\|T_\rho f\|_p\le\|f\|_p$ for real-valued cube functions.

<a id="pdf-ffbe9c7b3306-p063-b013"></a>
<!-- pdf-source: page=63; block=13; confidence=0.99 -->
**Exercise 2.34.** Show \(|T_\rho f|\le T_\rho|f|\) pointwise. For \(-1<\rho<1\), equality holds exactly when \(f\) is everywhere nonnegative or everywhere nonpositive.

<a id="pdf-ffbe9c7b3306-p063-b014"></a>
<!-- pdf-source: page=63; block=14; confidence=0.99 -->
**Exercise 2.35.** Define $T_\rho^if=\rho f+(1-\rho)E_if=E_if+\rho L_if$ for real $\rho$. (a) For $\rho\in[-1,1]$, prove $T_\rho^if(x)=\mathbb E_{y_i\sim N_\rho(x_i)}[f(x_1,\ldots,x_{i-1},y_i,x_{i+1},\ldots,x_n)]$. (b) Prove $T_{\rho_1}^iT_{\rho_2}^i=T_{\rho_1\rho_2}^i$ and pairwise commutation of $T_\rho^i$ and $T_{\rho'}^j$.

<a id="pdf-ffbe9c7b3306-p064-b001"></a>
<!-- pdf-source: page=64; block=1; confidence=1.00 -->
**Exercise 2.35(c–d).** For \((\rho_1,\ldots,\rho_n)\in\mathbb R^n\), define \(T_{(\rho_1,\ldots,\rho_n)}=T^1_{\rho_1}\cdots T^n_{\rho_n}\). Show \(T_{(\rho,\ldots,\rho)}=T_\rho\) and that the vector with \(\rho\) in coordinate \(i\) and 1 elsewhere gives \(T^i_\rho\). For \(\rho_i\in[-1,1]\), show this operator is a contraction on \(L^p\), for all \(p\ge1\).

<a id="pdf-ffbe9c7b3306-p064-b002"></a>
<!-- pdf-source: page=64; block=2; confidence=1.00 -->
**Exercise 2.36.** Prove \(\operatorname{Stab}_{-\rho}[f]=-\operatorname{Stab}_\rho[f]\) for odd \(f\), and \(\operatorname{Stab}_{-\rho}[f]=\operatorname{Stab}_\rho[f]\) for even \(f\).

<a id="pdf-ffbe9c7b3306-p064-b003"></a>
<!-- pdf-source: page=64; block=3; confidence=1.00 -->
**Exercise 2.37.** Calculate \(\operatorname{Stab}_\rho[f]\) for each function listed in Exercise 1.1.

<a id="pdf-ffbe9c7b3306-p064-b004"></a>
<!-- pdf-source: page=64; block=4; confidence=1.00 -->
**Exercise 2.38.** Calculate \(\operatorname{Stab}_\rho[\operatorname{Tribes}_{w,s}]\).

<a id="pdf-ffbe9c7b3306-p064-b005"></a>
<!-- pdf-source: page=64; block=5; confidence=1.00 -->
**Exercise 2.39.** If Boolean \(f\) satisfies \(\min\{\Pr[f=1],\Pr[f=-1]\}=\alpha\), prove \(\operatorname{NS}_\delta[f]\le2\alpha\) for every \(\delta\in[0,1]\).

<a id="pdf-ffbe9c7b3306-p064-b006"></a>
<!-- pdf-source: page=64; block=6; confidence=1.00 -->
**Exercise 2.40.** Establish Fact 2.53, whose statement is outside these pages.

<a id="pdf-ffbe9c7b3306-p064-b007"></a>
<!-- pdf-source: page=64; block=7; confidence=0.99 -->
**Exercise 2.41.** For real-valued \(f\) on the discrete cube, prove that \(\rho\mapsto\operatorname{Stab}_\rho[f]\) is convex on \([0,1]\).

<a id="pdf-ffbe9c7b3306-p064-b008"></a>
<!-- pdf-source: page=64; block=8; confidence=1.00 -->
**Exercise 2.42.** For Boolean \(f\), prove \(\operatorname{NS}_\delta[f]\le\delta\operatorname{I}[f]\) for \(\delta\in[0,1]\).

<a id="pdf-ffbe9c7b3306-p064-b009"></a>
<!-- pdf-source: page=64; block=9; confidence=0.96 -->
**Exercise 2.43.** Define average influence by \(\mathcal I[f]=I[f]/n\). For Boolean \(f\), show \(\mathcal I[f]=\Pr_{x,i}[f(x)\ne f(x^{\oplus i})]\) and \(\frac{1-e^{-2}}2\mathcal I[f]\le\operatorname{NS}_{1/n}[f]\le\mathcal I[f]\). For integer \(k\ge2\), put \(A_k=\frac1k\sum_{j=1}^k W^{\ge j}[f]\) and prove \(\frac{1-e^{-2}}2A_k\le\operatorname{NS}_{1/k}[f]\le A_k\).

<a id="pdf-ffbe9c7b3306-p064-b010"></a>
<!-- pdf-source: page=64; block=10; confidence=0.99 -->
**Exercise 2.44.** Given Boolean \(f_1,\ldots,f_s\) with \(\operatorname{NS}_\delta[f_i]\le\epsilon_i\), and Boolean \(g\) on \(s\) bits, prove that \(h=g(f_1,\ldots,f_s)\) satisfies \(\operatorname{NS}_\delta[h]\le\sum_{i=1}^s\epsilon_i\).

<a id="pdf-ffbe9c7b3306-p064-b011"></a>
<!-- pdf-source: page=64; block=11; confidence=0.99 -->
**Exercise 2.45.** Finish Proposition 2.54 by proving \(k(1-\delta)^{k-1}\le1/\delta\) for \(0<\delta\le1\) and positive integer \(k\). Suggested comparison: \(\sum_{j=0}^{k-1}(1-\delta)^j\).

<a id="pdf-ffbe9c7b3306-p064-b012"></a>
<!-- pdf-source: page=64; block=12; confidence=0.99 -->
**Exercise 2.46.** For real-valued \(f\) and \(0\le\rho-\epsilon\le\rho<1\), prove \(\left|\operatorname{Stab}_\rho[f]-\operatorname{Stab}_{\rho-\epsilon}[f]\right|\le\frac{\epsilon}{1-\rho}\operatorname{Var}[f]\), using the mean value theorem and Exercise 2.45.

<a id="pdf-ffbe9c7b3306-p064-b013"></a>
<!-- pdf-source: page=64; block=13; confidence=1.00 -->
**Exercise 2.47.** If Boolean \(f\) is transitive-symmetric, meaning \(\operatorname{Aut}(f)\) acts transitively on \([n]\), prove \(\Pr_{\pi\sim\operatorname{Aut}(f)}[\pi(i)=j]=1/n\) for all \(i,j\in[n]\); notation follows Exercise 1.30.

<a id="pdf-ffbe9c7b3306-p065-b001"></a>
<!-- pdf-source: page=65; block=1; confidence=0.99 -->
**Exercise 2.48.** For \(F[f]=\sum_{S\subseteq[n]}c_S\widehat f(S)^2\) with \(c_S\ge0\), prove \(F[\lambda f+(1-\lambda)g]\le\lambda F[f]+(1-\lambda)F[g]\) for \(\lambda\in[0,1]\). Examples are variance, level weights, influences, total influence, noisy influences, and stability at nonnegative correlation.

<a id="pdf-ffbe9c7b3306-p065-b002"></a>
<!-- pdf-source: page=65; block=2; confidence=1.00 -->
**Exercise 2.49.** Extend FKN: a Boolean \(f\) with \(\operatorname{W}^{\le1}[f]\ge1-\delta\) is \(O(\delta)\)-close to a 1-junta. Suggested auxiliary function: \(g(x_0,x)=x_0f(x_0x)\).

<a id="pdf-ffbe9c7b3306-p065-b003"></a>
<!-- pdf-source: page=65; block=3; confidence=1.00 -->
**Exercise 2.50.** Determine the exact probability of a Condorcet winner for three candidates and three voters under impartial culture, using \(f=\operatorname{Maj}_3\).

<a id="pdf-ffbe9c7b3306-p065-b004"></a>
<!-- pdf-source: page=65; block=4; confidence=1.00 -->
**Exercise 2.51.** (a) If three unanimous Boolean aggregation rules \(f,g,h\) for the pairwise contests always yield a Condorcet winner, prove \(f=g=h\). First derive \(g(x)=-f(-x)\) from valid vote vectors \(x,-x,(f(x),\ldots,f(x))\). (b) Extend Arrow's theorem to more than three candidates.

<a id="pdf-ffbe9c7b3306-p065-b005"></a>
<!-- pdf-source: page=65; block=5; confidence=0.99 -->
**Exercise 2.52.** For real-valued \(f\), define \(f^{\sigma_i}(x)\) as the maximum of \(f(x^{(i\mapsto+1)})\) and \(f(x^{(i\mapsto-1)})\) when \(x_i=+1\), and their minimum when \(x_i=-1\). Prove preservation of expectation and every \(L^p\) norm; \(\operatorname{Inf}_j[f^{\sigma_i}]\le\operatorname{Inf}_j[f]\) for every \(j\); and \(\operatorname{Stab}_\rho[f^{\sigma_i}]\ge\operatorname{Stab}_\rho[f]\) for \(0\le\rho\le1\). Polarization makes coordinate \(i\) monotone and preserves monotonicity in other coordinates. Consequently \(f^*=f^{\sigma_1\cdots\sigma_n}\) is monotone, has the same expectation, no larger coordinate influences, and no smaller stability on \([0,1]\).

<a id="pdf-ffbe9c7b3306-p065-b006"></a>
<!-- pdf-source: page=65; block=6; confidence=0.99 -->
**Exercise 2.53.** The Hamming metric \(\Delta(x,y)=\#\{i:x_i\ne y_i\}\) is an \(\ell^1\) metric. An embedding \(F:\{-1,1\}^n\to\mathbb R^m\) has distortion \(D\ge1\) if \(\Delta(x,y)\le\|F(x)-F(y)\|_2\le D\Delta(x,y)\) for all \(x,y\). The exercise asks to establish optimal distortion \(\sqrt n\); its subparts continue on page 66.

<a id="pdf-ffbe9c7b3306-p066-b001"></a>
<!-- pdf-source: page=66; block=1; confidence=0.99 -->
**Exercise 2.53(a–c).** (a) For real-valued \(f\), prove \(\|f^{\mathrm{odd}}\|_2^2\le\operatorname{I}[f]\), hence \(\mathbb E_x[(f(x)-f(-x))^2]\le\sum_{i=1}^n\mathbb E_x[(f(x)-f(x^{\oplus i}))^2]\). (b) Sum this inequality over the coordinate functions of \(F:\{-1,1\}^n\to\mathbb R^m\) to show that no contraction forces expansion at least \(\sqrt n\). (c) Construct an embedding attaining \(\sqrt n\).

<a id="pdf-ffbe9c7b3306-p066-b002"></a>
<!-- pdf-source: page=66; block=2; confidence=1.00 -->
**Exercise 2.54.** Prove the Poincaré inequality by induction on \(n\), without Fourier analysis.

<a id="pdf-ffbe9c7b3306-p066-b003"></a>
<!-- pdf-source: page=66; block=3; confidence=0.99 -->
**Exercise 2.55.** In a normed vector space \(V\), fix \(w_1,\ldots,w_n\) and set \(g(x)=\|\sum_{i=1}^n x_iw_i\|\). (a) Use the triangle inequality to prove \(Lg\le g\) pointwise. (b) Deduce \(2\operatorname{Var}[g]\le\mathbb E[g^2]\), yielding \(\mathbb E_x\|\sum_i x_iw_i\|\ge\frac1{\sqrt2}(\mathbb E_x\|\sum_i x_iw_i\|^2)^{1/2}\); see Exercise 2.28. (c) Prove optimality of \(1/\sqrt2\), even for \(V=\mathbb R\).

<a id="pdf-ffbe9c7b3306-p066-b004"></a>
<!-- pdf-source: page=66; block=4; confidence=1.00 -->
**Exercise 2.56.** A uniform cube point \(x\) is broadcast noisily to \(q\) noncommunicating parties. Choose Boolean rules \(f_j(y^{(j)})\), each with mean zero, to maximize \(\Pr[f_1(y^{(1)})=\cdots=f_q(y^{(q)})]\).

<a id="pdf-ffbe9c7b3306-p066-b005"></a>
<!-- pdf-source: page=66; block=5; confidence=0.99 -->
**Exercise 2.56(a–b).** For \(\rho\in(0,1)\), let the observations be conditionally independent samples \(y^{(j)}\sim N_\rho(x)\). For \(q=2\), prove that optimal rules are precisely \(f_1=f_2=\pm\chi_i\) for some coordinate \(i\), using Cauchy–Schwarz. Establish the corresponding common signed-dictator characterization for \(q=3\).

<a id="pdf-ffbe9c7b3306-p066-b006"></a>
<!-- pdf-source: page=66; block=6; confidence=0.99 -->
**Exercise 2.56(c).** For \(q=2\) and \(\rho\in(1/2,1)\), party 1 receives \(x\), while party 2 independently retains each coordinate with probability \(\rho\), otherwise replacing it by zero. Prove that optimal agreement probability is \(\frac12+\frac\rho2\), with an optimal strategy having \(f_1=\pm\chi_i\) for any chosen \(i\). Suggested method: eliminate the source and introduce a fictitious party \(1'\).

<a id="pdf-ffbe9c7b3306-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.99 -->
For the previous optimization problem with \(\rho\in(0,1/2)\), show that for sufficiently large \(n\), an optimal solution does not have \(f_1=\pm\chi_i\).

<a id="pdf-ffbe9c7b3306-p067-b002"></a>
<!-- pdf-source: page=67; block=2; confidence=0.99 -->
**Exercise 2.57(a).** For nonnegative \(g:\{-1,1\}^n\to\mathbb R\) with \(\mathbb E[g]=\delta\), prove, for every \(\rho\in[0,1]\),
\[
\rho\sum_{j=1}^n|\widehat g(\{j\})|\le\delta+\sum_{k=2}^n\rho^k\|g^{=k}\|_\infty.
\]
Use Exercise 2.31.

<a id="pdf-ffbe9c7b3306-p067-b003"></a>
<!-- pdf-source: page=67; block=3; confidence=0.94 -->
**Exercise 2.57(b).** If additionally \(g\) is \(\{0,1\}\)-valued, establish
\[
\|g^{=k}\|_\infty\le\sqrt\delta\sqrt{\binom nk}.
\]
First bound \(\|g^{=k}\|_2^2\). Deduce, for \(\rho\le1/(2\sqrt n)\),
\[
\rho\sum_{j=1}^n|\widehat g(\{j\})|\le\delta+2\rho^2\sqrt\delta\,n.
\]

<a id="pdf-ffbe9c7b3306-p067-b004"></a>
<!-- pdf-source: page=67; block=4; confidence=0.99 -->
**Exercise 2.57(c).** Assuming \(\delta\le1/4\), show \(\sum_{j=1}^n|\widehat g(\{j\})|\le2\sqrt2\,\delta^{3/4}\sqrt n\). Deduce \(W^1[g]\le2\sqrt2\,\delta^{7/4}\sqrt n\).

<a id="pdf-ffbe9c7b3306-p067-b005"></a>
<!-- pdf-source: page=67; block=5; confidence=0.95 -->
**Exercise 2.57(d).** For monotone \(f:\{-1,1\}^n\to\{-1,1\}\) satisfying \(\operatorname{MaxInf}[f]\le\delta\), show
\[
\mathbf W^2[f]\le\sqrt2\,\delta^{3/4}\mathbf I[f]\sqrt n.
\]

<a id="pdf-ffbe9c7b3306-p067-b006"></a>
<!-- pdf-source: page=67; block=6; confidence=0.99 -->
**Exercise 2.57(e).** If \(f\) is also unbiased, prove
\[
\operatorname{MaxInf}[f]\le o(n^{-2/3})\implies\mathbf I[f]\ge3-o(1),
\]
and conclude \(\operatorname{MaxInf}[f]\ge3/n-o(1/n)\). Extend Exercise 2.29, then use Exercise 2.52 to obtain these conclusions without monotonicity.

<a id="pdf-ffbe9c7b3306-p067-b007"></a>
<!-- pdf-source: page=67; block=7; confidence=1.00 -->
**Exercise 2.58.** Let \(V\) be a vector space over \(\mathbb R\) with norm \(\|\cdot\|_V\). For \(f:\{-1,1\}^n\to V\), define \(\widehat f(S)=\mathbb E_x[f(x)x^S]\) and \(\|f\|_p=\mathbb E_x[\|f(x)\|_V^p]^{1/p}\). If \(V\) has an inner product inducing its norm, define \(\langle f,g\rangle=\mathbb E_x[\langle f(x),g(x)\rangle_V]\). Explore which preceding results extend.

<a id="pdf-ffbe9c7b3306-p067-b008"></a>
<!-- pdf-source: page=67; block=8; confidence=0.98 -->
The notes attribute foundational social-choice results to Arrow, May, and Guilbaud, and the term “junta” to Parnas–Ron–Samorodnitsky. Penrose introduced influence and observed \(\operatorname{Inf}_i[\operatorname{Maj}_n]\sim\sqrt{2/\pi}/\sqrt n\).

<a id="pdf-ffbe9c7b3306-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.99 -->
Influence is also known as the Penrose–Banzhaf index; Ben-Or–Linial introduced tribes as a constant-variance example with small individual influences. Total influence corresponds to cube edge-boundary size and satisfies
\[
\mathbf I[f]=\sum_{S\subseteq[n]}|S|\widehat f(S)^2.
\]
The cube Poincaré inequality expresses its spectral gap.

<a id="pdf-ffbe9c7b3306-p068-b002"></a>
<!-- pdf-source: page=68; block=2; confidence=0.99 -->
The noise operator is attributed to Bonami and Beckner; nonnegative noise parameters admit the form \(T_{e^{-t}}\), \(t\ge0\). Further credits include Kalai’s Fourier proof of Arrow’s theorem, Friedgut–Kalai–Naor’s FKN theorem, Kleitman’s polarizations, and Chor–Geréb-Graus’s precursor to KKL underlying Exercise 2.57.

<a id="pdf-ffbe9c7b3306-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=1.00 -->
# Chapter 3: Spectral structure and learning

Fourier-spectrum location, size, and structure provide complexity measures relevant to learning Boolean functions.

<a id="pdf-ffbe9c7b3306-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=1.00 -->
## 3.1. Low-degree spectral concentration

<a id="pdf-ffbe9c7b3306-p069-b003"></a>
<!-- pdf-source: page=69; block=3; confidence=0.99 -->
**Definition 3.1.** The spectrum of \(f:\{-1,1\}^n\to\mathbb R\) is \(\epsilon\)-concentrated on degrees at most \(k\) when
\[
\mathbf W^{>k}[f]=\sum_{\substack{S\subseteq[n]\\|S|>k}}\widehat f(S)^2\le\epsilon.
\]
For Boolean \(f\), this is equivalent to \(\Pr_{\boldsymbol S\sim\mathcal S_f}[|\boldsymbol S|>k]\le\epsilon\).

<a id="pdf-ffbe9c7b3306-p069-b004"></a>
<!-- pdf-source: page=69; block=4; confidence=0.99 -->
**Proposition 3.2.** For every \(f:\{-1,1\}^n\to\mathbb R\) and \(\epsilon>0\), its Fourier spectrum is \(\epsilon\)-concentrated on degrees at most \(\mathbf I[f]/\epsilon\).

<a id="pdf-ffbe9c7b3306-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p070-b002"></a>
<!-- pdf-source: page=70; block=2; confidence=0.99 -->
For \(\operatorname{Tribes}_{w,2^w}\), with \(n=w2^w\), the bound \(I[f]=O(\log n)\) implies \(.01\)-concentration of its Fourier spectrum through degree \(O(\log n)\).

<a id="pdf-ffbe9c7b3306-p070-b003"></a>
<!-- pdf-source: page=70; block=3; confidence=1.00 -->
**Proposition 3.3.** If \(f:\{-1,1\}^n\to\{-1,1\}\) and \(0<\delta\le\tfrac12\), its Fourier spectrum is \(\epsilon\)-concentrated through degree \(1/\delta\), where \(\epsilon=\frac{2}{1-e^{-2}}\operatorname{NS}_\delta[f]\le3\operatorname{NS}_\delta[f]\).

<a id="pdf-ffbe9c7b3306-p070-b004"></a>
<!-- pdf-source: page=70; block=4; confidence=1.00 -->
**Proof.** Theorem 2.49 yields
\[
2\operatorname{NS}_\delta[f]=\mathbb E_{S\sim\mathcal S_f}[1-(1-2\delta)^{|S|}]
\ge[1-(1-2\delta)^{1/\delta}]\Pr[|S|\ge1/\delta]
\ge(1-e^{-2})\Pr[|S|\ge1/\delta].
\]
Here \(1-(1-2\delta)^k\) is nonnegative and nondecreasing in \(k\).

<a id="pdf-ffbe9c7b3306-p070-b005"></a>
<!-- pdf-source: page=70; block=5; confidence=0.99 -->
Theorem 2.45 gives \(\operatorname{NS}_\delta[\operatorname{Maj}_n]\le\sqrt\delta\) for sufficiently small \(\delta>0\) and sufficiently large \(n\). Thus majority has \(3\sqrt\delta\)-concentration through degree \(1/\delta\), or \(\epsilon\)-concentration through degree \(9/\epsilon^2\). Its \(.01\)-concentration through degree \(O(1)\), despite \(I[\operatorname{Maj}_n]=\Theta(\sqrt n)\), obstructs a simple converse to Proposition 3.2.

<a id="pdf-ffbe9c7b3306-p070-b006"></a>
<!-- pdf-source: page=70; block=6; confidence=1.00 -->
**Theorem 3.4.** A Boolean function \(f:\{-1,1\}^n\to\{-1,1\}\) with real degree \(\deg(f)\le k\), equivalently zero Fourier mass above degree \(k\), is a \(k2^{k-1}\)-junta. Exercise 3.24 addresses the near-optimality of this bound.

<a id="pdf-ffbe9c7b3306-p071-b001"></a>
<!-- pdf-source: page=71; block=1; confidence=0.99 -->
**Lemma 3.5.** A nonzero real-valued function \(f\) on \(\{-1,1\}^n\) with \(\deg(f)\le k\) satisfies \(\Pr_x[f(x)\ne0]\ge2^{-k}\).

<a id="pdf-ffbe9c7b3306-p071-b002"></a>
<!-- pdf-source: page=71; block=2; confidence=1.00 -->
**Proposition 3.6.** If Boolean-valued \(f\) has degree at most \(k\), then every \(\operatorname{Inf}_i[f]\) is either zero or at least \(2^{1-k}\).

<a id="pdf-ffbe9c7b3306-p071-b003"></a>
<!-- pdf-source: page=71; block=3; confidence=1.00 -->
**Proof.** Apply Lemma 3.5 to each nonzero derivative \(D_i f\), using \(\deg(D_i f)\le k-1\) and \(\operatorname{Inf}_i[f]=\Pr[D_i f(x)\ne0]\).

<a id="pdf-ffbe9c7b3306-p071-b004"></a>
<!-- pdf-source: page=71; block=4; confidence=1.00 -->
**Proof.** Proposition 3.6 bounds the number of coordinates with positive influence by \(I[f]/2^{1-k}\). Fact 3.7 gives \(I[f]\le\deg(f)\le k\), so at most \(k2^{k-1}\) coordinates are relevant.

<a id="pdf-ffbe9c7b3306-p071-b005"></a>
<!-- pdf-source: page=71; block=5; confidence=1.00 -->
**Fact 3.7.** Every Boolean-valued \(f\) satisfies \(I[f]\le\deg(f)\).

<a id="pdf-ffbe9c7b3306-p071-b006"></a>
<!-- pdf-source: page=71; block=6; confidence=1.00 -->
**Proof.** Use the Fourier expression for total influence.

<a id="pdf-ffbe9c7b3306-p071-b007"></a>
<!-- pdf-source: page=71; block=7; confidence=1.00 -->
FKN provides a robust analogue of Theorem 3.4 for \(k=1\). Friedgut’s Junta Theorem, deferred to Chapter 9.6, states that \(I[f]\le k\) implies \(\epsilon\)-closeness to a \(2^{O(k/\epsilon)}\)-junta.

<a id="pdf-ffbe9c7b3306-p071-b008"></a>
<!-- pdf-source: page=71; block=8; confidence=1.00 -->
## 3.2. Subspaces and decision trees

<a id="pdf-ffbe9c7b3306-p071-b009"></a>
<!-- pdf-source: page=71; block=9; confidence=0.99 -->
**Notation.** Regard inputs as \(\mathbb F_2^n\) and index characters by vectors: \(\chi_\gamma(x)=(-1)^{\gamma\cdot x}\), with the dot product over \(\mathbb F_2\). Then \(\chi_0=1\), \(\chi_{e_i}\) is the \(i\)th dictator, and
\[\chi_\beta\chi_\gamma=\chi_{\beta+\gamma}\qquad\text{for all }\beta,\gamma.\tag{3.1}\]
The character group is denoted \(\widehat{\mathbb F_2^n}\) and identified with its indices. For real-valued \(f\),
\[f(x)=\sum_{\gamma\in\widehat{\mathbb F_2^n}}\widehat f(\gamma)\chi_\gamma(x),\]
so \(\widehat f\) is a real-valued function on the dual group.

<a id="pdf-ffbe9c7b3306-p072-b001"></a>
<!-- pdf-source: page=72; block=1; confidence=1.00 -->
**Definition 3.8.** The spectral \(p\)-norm of real-valued \(f\) is
\[\|\widehat f\|_p=\left(\sum_{\gamma\in\widehat{\mathbb F_2^n}}|\widehat f(\gamma)|^p\right)^{1/p}.\]
The dual group uses counting measure; Parseval becomes \(\|f\|_2=\|\widehat f\|_2\).

<a id="pdf-ffbe9c7b3306-p072-b002"></a>
<!-- pdf-source: page=72; block=2; confidence=1.00 -->
**Definition 3.9.** Spectral sparsity counts nonzero Fourier coefficients:
\[\operatorname{sparsity}(\widehat f)=|\operatorname{supp}(\widehat f)|=\#\{\gamma:\widehat f(\gamma)\ne0\}.\]

<a id="pdf-ffbe9c7b3306-p072-b003"></a>
<!-- pdf-source: page=72; block=3; confidence=1.00 -->
**Definition 3.10.** The transform \(\widehat f\) is \(\epsilon\)-granular when every coefficient is an integer multiple of \(\epsilon\).

<a id="pdf-ffbe9c7b3306-p072-b004"></a>
<!-- pdf-source: page=72; block=4; confidence=1.00 -->
**Definition.** For \(A\le\mathbb F_2^n\), set
\[A^\perp=\{\gamma\in\widehat{\mathbb F_2^n}:\gamma\cdot x=0\text{ for every }x\in A\}.\]
Then \(\dim A^\perp=n-\dim A=\operatorname{codim}A\) and \((A^\perp)^\perp=A\).

<a id="pdf-ffbe9c7b3306-p072-b005"></a>
<!-- pdf-source: page=72; block=5; confidence=1.00 -->
**Proposition 3.11.** If \(A\le\mathbb F_2^n\) has codimension \(k\), its indicator and probability density have expansions
\[1_A=2^{-k}\sum_{\gamma\in A^\perp}\chi_\gamma,\qquad\varphi_A=\sum_{\gamma\in A^\perp}\chi_\gamma.\]

<a id="pdf-ffbe9c7b3306-p072-b006"></a>
<!-- pdf-source: page=72; block=6; confidence=1.00 -->
**Proof.** For a basis \(\gamma_1,\ldots,\gamma_k\) of \(A^\perp\), membership in \(A\) means \(\chi_{\gamma_i}(x)=1\) for every \(i\). Consequently,
\[1_A(x)=\prod_{i=1}^k\frac{1+\chi_{\gamma_i}(x)}2=2^{-k}\sum_{\gamma\in\operatorname{span}\{\gamma_1,\ldots,\gamma_k\}}\chi_\gamma(x),\]
using (3.1). Since \(\mathbb E[1_A]=2^{-k}\), normalization gives the density expansion.

<a id="pdf-ffbe9c7b3306-p072-b007"></a>
<!-- pdf-source: page=72; block=7; confidence=1.00 -->
**Definition.** An affine subspace is a coset \(A=H+a\), where \(H\le\mathbb F_2^n\) and \(a\in\mathbb F_2^n\). Equivalently,
\[A=\{x:\gamma\cdot x=\gamma\cdot a\text{ for every }\gamma\in H^\perp\}.\]
An extension of Proposition 3.11 to cosets is announced, with its statement on the next page.

<a id="pdf-ffbe9c7b3306-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=1.00 -->
### 3.2. Subspaces and decision trees

<a id="pdf-ffbe9c7b3306-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.98 -->
**Proposition 3.12.** For an affine subspace $A=H+a\subseteq\mathbb F_2^n$ of codimension $k$,
$$\widehat{1_A}(\gamma)=\begin{cases}2^{-k}\chi_\gamma(a),&\gamma\in H^\perp,\\0,&\gamma\notin H^\perp.\end{cases}$$
Consequently, $\phi_A=\sum_{\gamma\in H^\perp}\chi_\gamma(a)\chi_\gamma$, the Fourier sparsity of $1_A$ is $2^k$, its coefficients are $2^{-k}$-granular, and $\|\widehat{1_A}\|_\infty=2^{-k}$, $\|\widehat{1_A}\|_1=1$.

<a id="pdf-ffbe9c7b3306-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=1.00 -->
A conjunction of parity constraints represents an affine-subspace indicator or the zero function. Constraints fixing individual coordinates $x_i=a_i$ define a subcube, whose indicator is an AND of literals.

<a id="pdf-ffbe9c7b3306-p073-b004"></a>
<!-- pdf-source: page=73; block=4; confidence=0.99 -->
**Definition 3.13.** A decision tree for $f:\mathbb F_2^n\to\mathbb R$ is a rooted binary tree with coordinate labels at internal nodes, edges labeled $0,1$, and real leaf labels. Each coordinate occurs at most once along any root-to-leaf path. On input $x$, a node labeled $i$ follows the edge labeled $x_i$; the reached leaf gives $f(x)$.

<a id="pdf-ffbe9c7b3306-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=1.00 -->
Figure 3.1 represents $\mathrm{Sort}_3(x)=1$ exactly when $x_1\le x_2\le x_3$ or $x_1\ge x_2\ge x_3$. Input $(0,1,0)$ follows queries $x_1,x_3,x_2$ and outputs $0$.

<a id="pdf-ffbe9c7b3306-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=1.00 -->
**Definition 3.14.** A decision tree's size $s$ counts its leaves; its depth $k$ is the greatest root-to-leaf path length. For trees on $n$ coordinates, $k\le n$ and $s\le2^k$. Define $\mathrm{DT}(f)$ and $\mathrm{DTsize}(f)$ as the minimum depth and minimum size among trees computing $f$; different trees may attain these minima. The displayed $\mathrm{Sort}_3$ tree has size $6$ and depth $3$.

<a id="pdf-ffbe9c7b3306-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=1.00 -->
Each root-to-leaf path $P$ specifies a subcube $C_P$ on which $f$ has the leaf value $f(P)$. These subcubes partition $\mathbb F_2^n$.

<a id="pdf-ffbe9c7b3306-p074-b004"></a>
<!-- pdf-source: page=74; block=4; confidence=1.00 -->
**Fact 3.15.** If $T$ computes $f$, then
$$f=\sum_{P\text{ a root-to-leaf path of }T}f(P)1_{C_P}.$$

<a id="pdf-ffbe9c7b3306-p074-b005"></a>
<!-- pdf-source: page=74; block=5; confidence=0.97 -->
**Proposition 3.16.** If a decision tree of size $s$ and depth $k$ computes $f:\mathbb F_2^n\to\mathbb R$, then
$$\deg(f)\le k,\qquad \operatorname{sparsity}(\widehat f)\le s2^k\le4^k,$$
$$\|\widehat f\|_1\le\|f\|_\infty s\le\|f\|_\infty2^k.$$
For integer-valued $f$, its Fourier coefficients are $2^{-k}$-granular.

<a id="pdf-ffbe9c7b3306-p074-b006"></a>
<!-- pdf-source: page=74; block=6; confidence=0.99 -->
**Proposition 3.17.** If $f:\mathbb F_2^n\to\{-1,1\}$ has a decision tree with $s$ leaves, then for every $\epsilon\in(0,1]$, its Fourier spectrum is $\epsilon$-concentrated on degrees at most $\log(s/\epsilon)$.

<a id="pdf-ffbe9c7b3306-p074-b007"></a>
<!-- pdf-source: page=74; block=7; confidence=1.00 -->
Exercises 3.21–3.22 supply proofs of the preceding propositions; Exercise 3.26 treats related bounds for subcube partitions and parity decision trees.

<a id="pdf-ffbe9c7b3306-p074-b008"></a>
<!-- pdf-source: page=74; block=8; confidence=1.00 -->
### 3.3. Restrictions

<a id="pdf-ffbe9c7b3306-p074-b009"></a>
<!-- pdf-source: page=74; block=9; confidence=0.99 -->
For $[n]=J\sqcup\overline J$, fixing the coordinates in $\overline J$ turns $f:\{-1,1\}^n\to\mathbb R$ into a function on $\{-1,1\}^J$.

<a id="pdf-ffbe9c7b3306-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=1.00 -->
Setting $x_4=1,x_5=-1$ in $\mathrm{Maj}_5$ yields $\mathrm{Maj}_3$. Further setting $x_3=-1$ yields the two-variable function equal to $1$ exactly when both remaining inputs are $1$.

<a id="pdf-ffbe9c7b3306-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.99 -->
**Definition 3.18.** Given $[n]=J\sqcup\overline J$ and $z\in\{-1,1\}^{\overline J}$, the restriction $f_{J\mid z}:\{-1,1\}^J\to\mathbb R$ fixes the complementary coordinates to $z$. Writing $(y,z)$ for the string assembled on these coordinate sets,
$$f_{J\mid z}(y)=f(y,z).$$
The notation $f_{\mid z}$ is used when the partition is understood.

<a id="pdf-ffbe9c7b3306-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.98 -->
**Example 3.19.** Define $f:\{-1,1\}^4\to\{-1,1\}$ by
$$f(x)=1\iff (x_3=x_4=-1)\ \text{or}\ (x_1\ge x_2\ge x_3\ge x_4)\ \text{or}\ (x_1\le x_2\le x_3\le x_4).\tag{3.2}$$
Its Fourier expansion is
$$\begin{aligned}f(x)=\tfrac18\big(&1-x_1+x_2-x_3-x_4+3x_1x_2+x_1x_3-3x_1x_4\\&+3x_2x_3-x_2x_4+5x_3x_4+x_1x_2x_3+x_1x_2x_4\\&-x_1x_3x_4+x_2x_3x_4-x_1x_2x_3x_4\big).\end{aligned}\tag{3.3}$$

<a id="pdf-ffbe9c7b3306-p075-b004"></a>
<!-- pdf-source: page=75; block=4; confidence=1.00 -->
For $f'=f_{\{1,2\}\mid(1,-1)}$, equation (3.2) gives $f'(x_1,x_2)=1$ exactly when $x_1=x_2=1$. Thus
$$f'(x_1,x_2)=\min_2(x_1,x_2)=-\tfrac12+\tfrac12x_1+\tfrac12x_2+\tfrac12x_1x_2.\tag{3.4}$$
This also follows by substituting $x_3=1,x_4=-1$ into (3.3). The coefficient of $x_1$ collects the terms $-x_1/8+x_1x_3/8-3x_1x_4/8-x_1x_3x_4/8$, giving $-1/8+1/8+3/8+1/8=1/2$.

<a id="pdf-ffbe9c7b3306-p075-b005"></a>
<!-- pdf-source: page=75; block=5; confidence=1.00 -->
Because $f_{J\mid z}$ has domain $\{-1,1\}^J$, its Fourier coefficients are indexed by subsets of $J$.

<a id="pdf-ffbe9c7b3306-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=0.99 -->
**Definition 3.20.** Let \((J,\bar J)\) partition \([n]\), let \(S\subseteq J\), and let \(z\in\{-1,1\}^{\bar J}\). Define \(F_{S\mid\bar J}f:\{-1,1\}^{\bar J}\to\mathbb R\) by \(F_{S\mid\bar J}f(z)=\widehat{f_{J\mid z}}(S)\). When the partition is understood, write \(F_{S\mid\bar J}f\).

<a id="pdf-ffbe9c7b3306-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.94 -->
Example 3.19 uses J̄ = {3,4}, S = {1}, and z = (1,−1). Figure 3.2 illustrates restriction coordinates, which need not be contiguous. The Fourier coefficients of F_{S∣J̄}f are indexed by subsets of J̄.

<a id="pdf-ffbe9c7b3306-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=0.99 -->
**Proposition 3.21.** For S ⊆ J,
\[
(F_{S\mid\bar J}f)(z)=\sum_{T\subseteq\bar J}\widehat f(S\cup T)z^T,
\qquad
\widehat{F_{S\mid\bar J}f}(T)=\widehat f(S\cup T).
\]

<a id="pdf-ffbe9c7b3306-p076-b004"></a>
<!-- pdf-source: page=76; block=4; confidence=0.99 -->
**Proof.** Split each Fourier index as U = S ⊔ T with S ⊆ J, T ⊆ J̄, and write x = (y,z). Since xᵁ = yˢzᵀ,
\[
f(y,z)=\sum_{S\subseteq J}\left(\sum_{T\subseteq\bar J}\widehat f(S\cup T)z^T\right)y^S.
\]
For fixed z, the parenthesized expression is the S-th Fourier coefficient of the restriction. The case S = ∅ is Exercise 1.15.

<a id="pdf-ffbe9c7b3306-p077-b001"></a>
<!-- pdf-source: page=77; block=1; confidence=0.99 -->
**Corollary 3.22.** Fix S ⊆ J and choose z uniformly from {−1,1}ᴶ̄. Then
\[
\mathbb E_z[\widehat{f_{J\mid z}}(S)]=\widehat f(S),\qquad
\mathbb E_z[\widehat{f_{J\mid z}}(S)^2]=\sum_{T\subseteq\bar J}\widehat f(S\cup T)^2.
\]

<a id="pdf-ffbe9c7b3306-p077-b002"></a>
<!-- pdf-source: page=77; block=2; confidence=0.99 -->
**Proof.** Proposition 3.21 identifies the mean with the T = ∅ coefficient. Parseval gives
\[
\mathbb E_z[(F_{S\mid\bar J}f)(z)^2]
=\sum_{T\subseteq\bar J}\widehat{F_{S\mid\bar J}f}(T)^2
=\sum_{T\subseteq\bar J}\widehat f(S\cup T)^2.
\]

<a id="pdf-ffbe9c7b3306-p077-b003"></a>
<!-- pdf-source: page=77; block=3; confidence=0.99 -->
Restrictions to affine subspaces H + z ⊆ 𝔽₂ⁿ generalize subcube restrictions: a free coordinate set J corresponds to H = span{eᵢ : i ∈ J}.

<a id="pdf-ffbe9c7b3306-p077-b004"></a>
<!-- pdf-source: page=77; block=4; confidence=0.98 -->
**Definition 3.23.** For f : 𝔽₂ⁿ → ℝ and a linear subspace H ≤ 𝔽₂ⁿ, f_H : H → ℝ denotes the restriction of f to H.

<a id="pdf-ffbe9c7b3306-p077-b005"></a>
<!-- pdf-source: page=77; block=5; confidence=0.99 -->
Identifying H + z with H by h ↦ h + z depends on the representative z. For H = {(0,0),(1,1)} ≤ 𝔽₂², one has H⊥ = H and H + (1,0) = H + (0,1) = {(1,0),(0,1)}, with no canonical representative. Affine restriction is therefore expressed as translation followed by restriction.

<a id="pdf-ffbe9c7b3306-p077-b006"></a>
<!-- pdf-source: page=77; block=6; confidence=0.98 -->
**Definition 3.24.** For f : 𝔽₂ⁿ → ℝ and z ∈ 𝔽₂ⁿ, define the translate f⁺ᶻ by f⁺ᶻ(x) = f(x + z).

<a id="pdf-ffbe9c7b3306-p078-b001"></a>
<!-- pdf-source: page=78; block=1; confidence=0.98 -->
**Fact 3.25.** Translation multiplies Fourier coefficients by character values:
\[
\widehat{f^{+z}}(\gamma)=(-1)^{\gamma\cdot z}\widehat f(\gamma),\qquad
f^{+z}(x)=\sum_{\gamma\in\widehat{\mathbb F_2^n}}\chi_\gamma(z)\widehat f(\gamma)\chi_\gamma(x).
\]
This follows by substituting x + z into the Fourier expansion, or from f⁺ᶻ = φ_{\{z\}} ∗ f (Exercise 3.31).

<a id="pdf-ffbe9c7b3306-p078-b002"></a>
<!-- pdf-source: page=78; block=2; confidence=0.99 -->
**Definition 3.26.** For z ∈ 𝔽₂ⁿ and H ≤ 𝔽₂ⁿ, set f_H⁺ᶻ = (f⁺ᶻ)_H : H → ℝ; explicitly, f_H⁺ᶻ(h) = f(h + z). This records the representative used for restriction to H + z.

<a id="pdf-ffbe9c7b3306-p078-b003"></a>
<!-- pdf-source: page=78; block=3; confidence=0.98 -->
The Fourier coefficients of f_H⁺ᶻ are indexed by cosets of H⊥ in the ambient dual group. The zero coefficient is the coset average:
\[
\widehat{f_H^{+z}}(0)=\mathbb E_{h\sim H}[f(h+z)]=\langle\varphi_H,f^{+z}\rangle.
\]
Plancherel, Proposition 3.11, and Fact 3.25 yield the following formula.

<a id="pdf-ffbe9c7b3306-p078-b004"></a>
<!-- pdf-source: page=78; block=4; confidence=0.99 -->
**Poisson Summation Formula.** For f : 𝔽₂ⁿ → ℝ, H ≤ 𝔽₂ⁿ, and z ∈ 𝔽₂ⁿ,
\[
\mathbb E_{h\sim H}[f(h+z)]=\sum_{\gamma\in H^\perp}\chi_\gamma(z)\widehat f(\gamma).
\]

<a id="pdf-ffbe9c7b3306-p078-b005"></a>
<!-- pdf-source: page=78; block=5; confidence=1.00 -->
### 3.4. Learning theory

<a id="pdf-ffbe9c7b3306-p078-b006"></a>
<!-- pdf-source: page=78; block=6; confidence=1.00 -->
Computational learning seeks a hypothesis h that predicts an unknown f on future inputs using labeled examples (x,f(x)).

<a id="pdf-ffbe9c7b3306-p078-b007"></a>
<!-- pdf-source: page=78; block=7; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.99 -->
**Learning model (continued).** Query access permits requesting any value \(f(x)\), \(x\in\{-1,1\}^n\). Given accuracy \(\epsilon\in[0,1/2]\), a learner outputs a circuit for \(h:\{-1,1\}^n\to\{-1,1\}\). Learning \(\mathcal C\) with error \(\epsilon\) means that, for every target \(f\in\mathcal C\), the output satisfies \(\operatorname{dist}(f,h)\le\epsilon\) with high probability; failure probability \(1/10\) suffices.

<a id="pdf-ffbe9c7b3306-p079-b002"></a>
<!-- pdf-source: page=79; block=2; confidence=0.98 -->
Exact learning of an arbitrary Boolean function takes \(\widetilde O(2^n)\) time, whereas Section 3.5 gives query learning for \(\{f:\operatorname{DTsize}(f)\le s\}\) in \(\operatorname{poly}(s,n,1/\epsilon)\) time. Fourier-based learning seeks a collection capturing most spectral mass.

<a id="pdf-ffbe9c7b3306-p079-b003"></a>
<!-- pdf-source: page=79; block=3; confidence=0.99 -->
**Definition 3.28.** For \(\mathcal F\subseteq 2^{[n]}\), the Fourier spectrum of \(f:\{-1,1\}^n\to\mathbb R\) is \(\epsilon\)-concentrated on \(\mathcal F\) when
\[
\sum_{S\notin\mathcal F}\widehat f(S)^2\le\epsilon.
\]
For Boolean-valued \(f\), this is equivalent to \(\Pr_{S\sim\mathcal S_f}[S\notin\mathcal F]\le\epsilon\).

<a id="pdf-ffbe9c7b3306-p079-b004"></a>
<!-- pdf-source: page=79; block=4; confidence=0.99 -->
**Theorem 3.29 (begins).** Let \(A\) have at least random-example access to a Boolean target \(f\), and suppose it can identify a collection \(\mathcal F\) capturing all but \(\epsilon/2\) of the Fourier mass. The learning guarantee continues on page 80.

<a id="pdf-ffbe9c7b3306-p080-b001"></a>
<!-- pdf-source: page=80; block=1; confidence=0.99 -->
**Theorem 3.29 (continued).** Once such \(\mathcal F\) is identified, \(A\) can produce \(h\) with \(\operatorname{dist}(f,h)\le\epsilon\), with high probability, using \(\operatorname{poly}(|\mathcal F|,n,1/\epsilon)\) additional time.

<a id="pdf-ffbe9c7b3306-p080-b002"></a>
<!-- pdf-source: page=80; block=2; confidence=0.99 -->
**Proposition 3.30.** From random examples of Boolean \(f\), given \(S\subseteq[n]\) and \(0<\delta,\epsilon\le1/2\), a randomized algorithm returns \(\widetilde f(S)\) satisfying
\[
|\widetilde f(S)-\widehat f(S)|\le\epsilon
\]
with failure probability at most \(\delta\), in time \(\operatorname{poly}(n,1/\epsilon)\log(1/\delta)\).

<a id="pdf-ffbe9c7b3306-p080-b003"></a>
<!-- pdf-source: page=80; block=3; confidence=0.99 -->
**Proof.** Average the computable signs \(f(x)\chi_S(x)\), whose expectation is \(\widehat f(S)\). Chernoff's bound gives additive error \(\epsilon\) with failure probability \(\delta\) using \(O(\epsilon^{-2}\log(1/\delta))\) examples.

<a id="pdf-ffbe9c7b3306-p080-b004"></a>
<!-- pdf-source: page=80; block=4; confidence=0.99 -->
**Proposition 3.31.** If Boolean \(f\) and real-valued \(g\) satisfy \(\|f-g\|_2^2\le\epsilon\), then \(h=\operatorname{sgn}(g)\) satisfies \(\operatorname{dist}(f,h)\le\epsilon\). Either Boolean value may be assigned to \(\operatorname{sgn}(0)\).

<a id="pdf-ffbe9c7b3306-p080-b005"></a>
<!-- pdf-source: page=80; block=5; confidence=0.99 -->
**Proof.** A sign disagreement implies \(|f(x)-g(x)|^2\ge1\). Consequently,
\[
\operatorname{dist}(f,h)=\mathbb E_x\mathbf1_{f(x)\ne\operatorname{sgn}(g(x))}
\le\mathbb E_x|f(x)-g(x)|^2=\|f-g\|_2^2.
\]

<a id="pdf-ffbe9c7b3306-p080-b006"></a>
<!-- pdf-source: page=80; block=6; confidence=0.98 -->
**Proof of Theorem 3.29.** For every \(S\in\mathcal F\), apply Proposition 3.30 with additive tolerance \(\sqrt\epsilon/(2\sqrt{|\mathcal F|})\) and failure probability \(1/(10|\mathcal F|)\). The total time is \(\operatorname{poly}(|\mathcal F|,n,1/\epsilon)\); a union bound makes all estimates accurate with probability at least \(9/10\). Set
\[
g=\sum_{S\in\mathcal F}\widetilde f(S)\chi_S,\qquad h=\operatorname{sgn}(g).
\]
Proposition 3.31 reduces the claim to bounding \(\|f-g\|_2^2\).

<a id="pdf-ffbe9c7b3306-p081-b001"></a>
<!-- pdf-source: page=81; block=1; confidence=0.99 -->
**Proof (continued).** Parseval separates coefficient error from omitted mass:
\[
\begin{aligned}
\|f-g\|_2^2
&=\sum_{S\subseteq[n]}\widehat{f-g}(S)^2\\
&=\sum_{S\in\mathcal F}(\widehat f(S)-\widetilde f(S))^2+\sum_{S\notin\mathcal F}\widehat f(S)^2\\
&\le |\mathcal F|\left(\frac{\sqrt\epsilon}{2\sqrt{|\mathcal F|}}\right)^2+\epsilon/2
=\epsilon/4+\epsilon/2\le\epsilon.
\end{aligned}
\]
This completes the learning guarantee.

<a id="pdf-ffbe9c7b3306-p081-b002"></a>
<!-- pdf-source: page=81; block=2; confidence=0.99 -->
Section 3.5 uses Goldreich–Levin with query access to find a suitable \(\mathcal F\). For classes with low-degree spectral concentration, one can instead choose all subsets of bounded size in advance.

<a id="pdf-ffbe9c7b3306-p081-b003"></a>
<!-- pdf-source: page=81; block=3; confidence=0.99 -->
**The Low-Degree Algorithm.** If \(k\ge1\) and every Boolean \(f\in\mathcal C\) has Fourier mass at most \(\epsilon/2\) above degree \(k\), then random examples suffice to learn \(\mathcal C\) with error \(\epsilon\) in time \(\operatorname{poly}(n^k,1/\epsilon)\).

<a id="pdf-ffbe9c7b3306-p081-b004"></a>
<!-- pdf-source: page=81; block=4; confidence=0.99 -->
**Proof.** Use Theorem 3.29 with \(\mathcal F=\{S\subseteq[n]:|S|\le k\}\), whose size is \(\sum_{j=0}^k\binom nj\le O(n^k)\).

<a id="pdf-ffbe9c7b3306-p081-b005"></a>
<!-- pdf-source: page=81; block=5; confidence=0.99 -->
**Corollary 3.32.** For \(t\ge1\), Boolean functions with total influence \(I[f]\le t\) can be learned from random examples with error \(\epsilon\) in time \(n^{O(t/\epsilon)}\).

<a id="pdf-ffbe9c7b3306-p081-b006"></a>
<!-- pdf-source: page=81; block=6; confidence=0.99 -->
**Proof.** Proposition 3.2 supplies the required concentration for the Low-Degree Algorithm at \(k=2t/\epsilon\).

<a id="pdf-ffbe9c7b3306-p081-b007"></a>
<!-- pdf-source: page=81; block=7; confidence=0.99 -->
**Corollary 3.33.** Monotone Boolean functions on \(\{-1,1\}^n\) can be learned from random examples with error \(\epsilon\) in time \(n^{O(\sqrt n/\epsilon)}\).

<a id="pdf-ffbe9c7b3306-p081-b008"></a>
<!-- pdf-source: page=81; block=8; confidence=0.99 -->
**Proof.** Combine Corollary 3.32 with the influence bound in Theorem 2.33.

<a id="pdf-ffbe9c7b3306-p082-b001"></a>
<!-- pdf-source: page=82; block=1; confidence=0.98 -->
Subexponential learning algorithms can improve substantially on exhaustive search and can have cryptographic consequences.

<a id="pdf-ffbe9c7b3306-p082-b002"></a>
<!-- pdf-source: page=82; block=2; confidence=0.99 -->
**Corollary 3.34.** For \(\delta\in(0,1/2]\), let \(\mathcal C=\{f:\{-1,1\}^n\to\{-1,1\}:\operatorname{NS}_\delta[f]\le\varepsilon/6\}\). Then \(\mathcal C\) is learnable from random examples with error \(\varepsilon\) in time \(\operatorname{poly}(n^{1/\delta},1/\varepsilon)\).

<a id="pdf-ffbe9c7b3306-p082-b003"></a>
<!-- pdf-source: page=82; block=3; confidence=1.00 -->
**Proof.** Apply Proposition 3.3.

<a id="pdf-ffbe9c7b3306-p082-b004"></a>
<!-- pdf-source: page=82; block=4; confidence=0.99 -->
**Corollary 3.35.** Boolean functions with decision-tree size at most \(s\) are learnable from random examples to error \(\epsilon\) in time \(n^{O(\log(s/\epsilon))}\).

<a id="pdf-ffbe9c7b3306-p082-b005"></a>
<!-- pdf-source: page=82; block=5; confidence=1.00 -->
**Proof.** Apply Proposition 3.17.

<a id="pdf-ffbe9c7b3306-p082-b006"></a>
<!-- pdf-source: page=82; block=6; confidence=0.99 -->
**Theorem 3.36.** For \(k\ge1\), Boolean functions of degree at most \(k\), including depth-\(k\) decision trees, are exactly learnable from random examples in time \(n^k\operatorname{poly}(n,2^k)\). Exercise 3.36 supplies the argument.

<a id="pdf-ffbe9c7b3306-p082-b007"></a>
<!-- pdf-source: page=82; block=7; confidence=1.00 -->
## 3.5. Highlight: the Goldreich–Levin Algorithm

<a id="pdf-ffbe9c7b3306-p082-b008"></a>
<!-- pdf-source: page=82; block=8; confidence=0.98 -->
The Goldreich–Levin construction connects one-way permutations to pseudorandom generators; its analysis uses a query algorithm that finds noticeable correlations with linear functions (Exercise 3.45).

<a id="pdf-ffbe9c7b3306-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=1.00 -->
Finding linear functions noticeably correlated with the target is equivalent to locating its large Fourier coefficients.

<a id="pdf-ffbe9c7b3306-p083-b002"></a>
<!-- pdf-source: page=83; block=2; confidence=1.00 -->
**Goldreich–Levin Theorem.** Given query access to \(f:\{-1,1\}^n\to\{-1,1\}\) and \(0<\tau\le1\), an algorithm running in \(\operatorname{poly}(n,1/\tau)\) time outputs, with high probability, a list \(L\subseteq2^{[n]}\) such that
\[
|\widehat f(U)|\ge\tau\implies U\in L,
\qquad U\in L\implies|\widehat f(U)|\ge\tau/2.
\]
Parseval gives \(|L|\le4/\tau^2\).

<a id="pdf-ffbe9c7b3306-p083-b003"></a>
<!-- pdf-source: page=83; block=3; confidence=0.99 -->
Theorem 3.29 reduces learning to finding sets carrying all but \(\epsilon/2\) of the Fourier weight; Goldreich–Levin can collect the needed large coefficients using queries.

<a id="pdf-ffbe9c7b3306-p083-b004"></a>
<!-- pdf-source: page=83; block=4; confidence=1.00 -->
**Theorem 3.37.** If every target in a Boolean concept class has Fourier weight at most \(\epsilon/4\) outside some collection of at most \(M\) sets, the class is query-learnable to error \(\epsilon\) in time \(\operatorname{poly}(M,n,1/\epsilon)\). The derivation is assigned in Exercise 3.39.

<a id="pdf-ffbe9c7b3306-p083-b005"></a>
<!-- pdf-source: page=83; block=5; confidence=1.00 -->
Theorem 3.37 is the Kushilevitz–Mansour algorithm: arbitrary small spectral support suffices, whereas the Low-Degree Algorithm needs concentration on low degrees; the former requires queries.

<a id="pdf-ffbe9c7b3306-p083-b006"></a>
<!-- pdf-source: page=83; block=6; confidence=0.99 -->
**Theorem 3.38.** Boolean functions with Fourier \(\ell^1\)-norm \(\sum_U|\widehat f(U)|\le s\) are query-learnable to error \(\epsilon\) in time \(\operatorname{poly}(n,s,1/\epsilon)\). This includes functions computed by decision trees of size at most \(s\); proof is assigned in Exercise 3.38.

<a id="pdf-ffbe9c7b3306-p084-b001"></a>
<!-- pdf-source: page=84; block=1; confidence=1.00 -->
Proposition 3.30 tests a specified coefficient against thresholds \(\tau\) and \(\tau/2\); Goldreich–Levin avoids testing all \(2^n\) sets by recursively examining groups through their Fourier weight.

<a id="pdf-ffbe9c7b3306-p084-b002"></a>
<!-- pdf-source: page=84; block=2; confidence=1.00 -->
**Definition 3.39.** For \(f:\{-1,1\}^n\to\mathbb R\) and \(S\subseteq J\subseteq[n]\), define \(W_{S\mid\bar J}[f]=\sum_{T\subseteq\bar J}\widehat f(S\cup T)^2\), the Fourier weight on sets whose restriction to \(J\) is \(S\).

<a id="pdf-ffbe9c7b3306-p084-b003"></a>
<!-- pdf-source: page=84; block=3; confidence=1.00 -->
For every \(S\subseteq J\subseteq[n]\), \[W_{S\mid\bar J}[f]=\mathbb E_{z\sim\{-1,1\}^{\bar J}}\bigl[\widehat{f_{J\mid z}}(S)^2\bigr].\tag{3.5}\]

<a id="pdf-ffbe9c7b3306-p084-b004"></a>
<!-- pdf-source: page=84; block=4; confidence=1.00 -->
**Proposition 3.40.** For any \(S\subseteq J\subseteq[n]\), query access to Boolean \(f\) permits estimation of \(W_{S\mid J}[f]\) within additive error \(\epsilon\), with failure probability at most \(\delta\), in time \(\operatorname{poly}(n,1/\epsilon)\log(1/\delta)\).

<a id="pdf-ffbe9c7b3306-p084-b005"></a>
<!-- pdf-source: page=84; block=5; confidence=0.99 -->
**Proof.** Expand (3.5) using independent uniform \(y,y'\in\{-1,1\}^J\) and uniform \(z\in\{-1,1\}^{\overline J}\):
\[
W_{S\mid J}[f]
=\mathbb E_z\left[(\mathbb E_y f(y,z)\chi_S(y))^2\right]
=\mathbb E_{z,y,y'}[f(y,z)\chi_S(y)f(y',z)\chi_S(y')].
\]
The final integrand is a query-sampleable sign. A Chernoff bound needs \(O(\epsilon^{-2}\log(1/\delta))\) samples for the claimed accuracy and confidence.

<a id="pdf-ffbe9c7b3306-p084-b006"></a>
<!-- pdf-source: page=84; block=6; confidence=1.00 -->
**Proof of the Goldreich–Levin Theorem (opening).** Initially place all \(2^n\) candidate subsets in one implicit bucket. Each iteration begins by selecting a bucket containing \(2^m\) sets with \(m\ge1\). The remaining algorithm is beyond the supplied pages.

<a id="pdf-ffbe9c7b3306-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.98 -->
**Proof (continued).** Split a bucket of size $2^m$ into two buckets of size $2^{m-1}$, estimate each weight $\sum_{U\in B_i}\widehat f(U)^2$, and discard buckets with estimated weight at most $\tau^2/2$. Output the surviving sets once every bucket is a singleton.

<a id="pdf-ffbe9c7b3306-p085-b002"></a>
<!-- pdf-source: page=85; block=2; confidence=1.00 -->
**Proof step.** Weight errors bounded by $\tau^2/4$ suffice: a coefficient with $|\widehat f(U)|\ge\tau$ keeps its bucket above the discard threshold, whereas a singleton with $|\widehat f(U)|\le\tau/2$ has estimated weight at most $\tau^2/2$ and is discarded.

<a id="pdf-ffbe9c7b3306-p085-b003"></a>
<!-- pdf-source: page=85; block=3; confidence=0.99 -->
**Proof step.** Each surviving bucket has true weight at least $\tau^2/4$. Parseval bounds the number of active buckets by $4/\tau^2$, giving at most $4n/\tau^2$ splitting iterations. Polynomial-time bucket maintenance and weighing therefore yield time $\operatorname{poly}(n,1/\tau)$.

<a id="pdf-ffbe9c7b3306-p085-b004"></a>
<!-- pdf-source: page=85; block=4; confidence=0.98 -->
**Proof step.** For $0\le k\le n$ and $S\subseteq[k]$, define $B_{k,S}=\{S\cup T:T\subseteq\{k+1,\ldots,n\}\}$, of size $2^{n-k}$. Start with $B_{0,\varnothing}$ and split $B_{k,S}$ into $B_{k+1,S}$ and $B_{k+1,S\cup\{k+1\}}$; terminal buckets are $B_{n,S}=\{S\}$. Its weight is $W^{S\mid\{k+1,\ldots,n\}}[f]$. Proposition 3.40 estimates this within $\tau^2/4$ with failure probability $\delta$ in time $\operatorname{poly}(n,1/\tau)\log(1/\delta)$. At most $8n/\tau^2$ estimates are needed, so $\delta=\tau^2/(80n)$ gives simultaneous accuracy with probability at least $9/10$ by a union bound.

<a id="pdf-ffbe9c7b3306-p085-b005"></a>
<!-- pdf-source: page=85; block=5; confidence=1.00 -->
### 3.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p085-b006"></a>
<!-- pdf-source: page=85; block=6; confidence=0.99 -->
**Exercise 3.1.** For invertible linear $M:\mathbb F_2^n\to\mathbb F_2^n$ and real-valued $f$, define $(f\circ M)(x)=f(Mx)$ and establish the Fourier transformation rule continued on page 86.

<a id="pdf-ffbe9c7b3306-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=0.97 -->
**Exercise 3.1 (continued).** Prove $\widehat{f\circ M}(\gamma)=\widehat f(M^{-\mathsf T}\gamma)$, and determine the corresponding formulas for invertible affine $M$ and for noninvertible $M$.

<a id="pdf-ffbe9c7b3306-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=0.99 -->
**Exercise 3.2.** Show that $2/(1-e^{-2})$ is the optimal constant in Proposition 3.3 when the constant must be independent of $\delta$ and $n$.

<a id="pdf-ffbe9c7b3306-p086-b003"></a>
<!-- pdf-source: page=86; block=3; confidence=0.99 -->
**Exercise 3.3.** Generalize Proposition 3.3: every $f:\{-1,1\}^n\to\mathbb R$ is $\epsilon$-concentrated on degrees at most $1/\delta$, where $\epsilon=(\mathbb E[f^2]-\operatorname{Stab}_{1-\delta}[f])/(1-1/e)$.

<a id="pdf-ffbe9c7b3306-p086-b004"></a>
<!-- pdf-source: page=86; block=4; confidence=0.99 -->
**Exercise 3.4.** Prove Lemma 3.5 by induction on dimension. Suggested step: if one restriction at the last coordinate is zero, the other has degree at most $k-1$.

<a id="pdf-ffbe9c7b3306-p086-b005"></a>
<!-- pdf-source: page=86; block=5; confidence=1.00 -->
**Exercise 3.5.** Verify that the spectral quantity $\|\widehat f\|_p$ defines a norm on real-valued functions on $\mathbb F_2^n$ for every $1\le p\le\infty$.

<a id="pdf-ffbe9c7b3306-p086-b006"></a>
<!-- pdf-source: page=86; block=6; confidence=1.00 -->
**Exercise 3.6.** Prove $\|\widehat{fg}\|_1\le\|\widehat f\|_1\|\widehat g\|_1$ for real-valued $f,g$ on $\mathbb F_2^n$.

<a id="pdf-ffbe9c7b3306-p086-b007"></a>
<!-- pdf-source: page=86; block=7; confidence=0.99 -->
**Exercise 3.7.** For $J\subseteq[n]$ and $z\in\{-1,1\}^J$, prove $\|\widehat{f_{J\mid z}}\|_1\le\|\widehat f\|_1$ and $\operatorname{sparsity}(\widehat{f_{J\mid z}})\le\operatorname{sparsity}(\widehat f)$.

<a id="pdf-ffbe9c7b3306-p086-b008"></a>
<!-- pdf-source: page=86; block=8; confidence=1.00 -->
**Exercise 3.8.** For $0<p\le q\le\infty$, show $\|\widehat f\|_p\ge\|\widehat f\|_q$; compare Exercise 1.13.

<a id="pdf-ffbe9c7b3306-p086-b009"></a>
<!-- pdf-source: page=86; block=9; confidence=1.00 -->
**Exercise 3.9.** Establish $\|\widehat f\|_\infty\le\|f\|_1$ and $\|f\|_\infty\le\|\widehat f\|_1$, special cases of Hausdorff–Young.

<a id="pdf-ffbe9c7b3306-p086-b010"></a>
<!-- pdf-source: page=86; block=10; confidence=1.00 -->
**Exercise 3.10.** If $f:\{-1,1\}^n\to\{-1,1\}$ is monotone, prove $|\widehat f(S)|\le\widehat f(\{i\})$ whenever $i\in S$. Conclude that a coefficient maximizing absolute value occurs at degree zero or one. Hint: apply Exercise 3.9 to derivatives of $f$.

<a id="pdf-ffbe9c7b3306-p086-b011"></a>
<!-- pdf-source: page=86; block=11; confidence=1.00 -->
**Exercise 3.11.** Supply a proof of Proposition 3.12.

<a id="pdf-ffbe9c7b3306-p086-b012"></a>
<!-- pdf-source: page=86; block=12; confidence=1.00 -->
**Exercise 3.12.** Check Parseval's identity for the subspace Fourier expansion in Proposition 3.11.

<a id="pdf-ffbe9c7b3306-p086-b013"></a>
<!-- pdf-source: page=86; block=13; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p086-b014"></a>
<!-- pdf-source: page=86; block=14; confidence=1.00 -->
**Exercise 3.14.** Under $\mathbb E[f^2]\le1$, prove $\|\widehat f\|_1\le2^{n/2}$. For each even $n$, construct a Boolean-valued function attaining equality.

<a id="pdf-ffbe9c7b3306-p086-b015"></a>
<!-- pdf-source: page=86; block=15; confidence=1.00 -->
**Definition (Exercise 3.15).** For $f:\mathbb F_2^n\to\mathbb R$, its fractional support size is $\operatorname{sparsity}(f)=|\operatorname{supp}(f)|/2^n=\Pr_x[f(x)\ne0]$.

<a id="pdf-ffbe9c7b3306-p087-b001"></a>
<!-- pdf-source: page=87; block=1; confidence=0.99 -->
**Exercise 3.15.** Prove \(\operatorname{sparsity}(f)\operatorname{sparsity}(\widehat f)\ge1\) for nonzero \(f\). Normalize \(\|f\|_1=1\). (a) Show this normalization may be assumed. (b) For \(\mathcal F=\{\gamma:\widehat f(\gamma)\ne0\}\), prove \(\|\widehat f\|_2^2\le|\mathcal F|\). (c) For \(\mathcal G=\{x:f(x)\ne0\}\), prove \(\|f\|_2^2\ge2^n/|\mathcal G|\), and deduce the uncertainty principle. (d) Identify equality cases.

<a id="pdf-ffbe9c7b3306-p087-b002"></a>
<!-- pdf-source: page=87; block=2; confidence=0.99 -->
**Exercise 3.16.** For $\epsilon>0$, show that $f$ is $\epsilon$-concentrated on a collection $\mathcal F\subseteq2^{[n]}$ with $|\mathcal F|\le\|\widehat f\|_1^2/\epsilon$.

<a id="pdf-ffbe9c7b3306-p087-b003"></a>
<!-- pdf-source: page=87; block=3; confidence=1.00 -->
**Exercise 3.17.** If $f$ is $\epsilon_1$-concentrated on $\mathcal F$ and $\|f-g\|_2^2\le\epsilon_2$, prove that $g$ is $2(\epsilon_1+\epsilon_2)$-concentrated on $\mathcal F$.

<a id="pdf-ffbe9c7b3306-p087-b004"></a>
<!-- pdf-source: page=87; block=4; confidence=1.00 -->
**Exercise 3.18.** Every real-valued function on $\mathbb F_2^n$ admits a decision tree of depth at most $n$ and size at most $2^n$.

<a id="pdf-ffbe9c7b3306-p087-b005"></a>
<!-- pdf-source: page=87; block=5; confidence=0.99 -->
**Exercise 3.19.** If $f$ has a decision tree of size $s$ and depth $k$, show that $-f$ and its Boolean dual $f^\dagger$ have trees with the same size and depth.

<a id="pdf-ffbe9c7b3306-p087-b006"></a>
<!-- pdf-source: page=87; block=6; confidence=1.00 -->
**Exercise 3.20.** Construct decision trees for the functions in Exercise 1.1 having at most four inputs, minimizing depth first and size second.

<a id="pdf-ffbe9c7b3306-p087-b007"></a>
<!-- pdf-source: page=87; block=7; confidence=1.00 -->
**Exercise 3.21.** Supply a proof of Proposition 3.16.

<a id="pdf-ffbe9c7b3306-p087-b008"></a>
<!-- pdf-source: page=87; block=8; confidence=1.00 -->
**Exercise 3.22.** Let a size-$s$ tree compute Boolean $f$, and let $0<\epsilon\le1$. Truncate paths to length at most $\log(s/\epsilon)$, assigning arbitrary Boolean labels to new leaves. Prove the resulting function is $\epsilon$-close to $f$, and deduce Proposition 3.17.

<a id="pdf-ffbe9c7b3306-p087-b009"></a>
<!-- pdf-source: page=87; block=9; confidence=1.00 -->
**Exercise 3.23.** A decision list is a decision tree in which each internal node has a leaf child. Prove that every function computed by a decision list is a linear threshold function.

<a id="pdf-ffbe9c7b3306-p087-b010"></a>
<!-- pdf-source: page=87; block=10; confidence=0.99 -->
**Exercise 3.24.** A read-once tree queries a different variable at each internal node. Use such trees to show that the bound $k2^{k-1}$ in Theorem 3.4 cannot be improved below $2^k-1$.

<a id="pdf-ffbe9c7b3306-p087-b011"></a>
<!-- pdf-source: page=87; block=11; confidence=1.00 -->
**Exercise 3.25.** Compute every coordinate influence and $\mathbf I[f]$ for a read-once tree whose root-to-leaf paths all have length $k$, with opposite Boolean labels on the two children of each deepest internal node.

<a id="pdf-ffbe9c7b3306-p087-b012"></a>
<!-- pdf-source: page=87; block=12; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p088-b001"></a>
<!-- pdf-source: page=88; block=1; confidence=0.99 -->
A subcube partition computes the function that takes value \(b_i\) on every input in \(C_i\). Its size is \(s\), and its codimension is the maximum codimension of its parts.

<a id="pdf-ffbe9c7b3306-p088-b002"></a>
<!-- pdf-source: page=88; block=2; confidence=0.99 -->
**Definition.** A parity decision tree queries \(\gamma\cdot x\) at a node labeled \(\gamma\in\mathbb F_2^n\). Query vectors along each root-to-leaf path must be linearly independent. Size and depth have their usual decision-tree meanings.

<a id="pdf-ffbe9c7b3306-p088-b003"></a>
<!-- pdf-source: page=88; block=3; confidence=0.99 -->
**Definition.** An affine subspace partition replaces the subcubes of a labeled subcube partition by arbitrary affine subspaces.

<a id="pdf-ffbe9c7b3306-p088-b004"></a>
<!-- pdf-source: page=88; block=4; confidence=0.99 -->
**Exercise 3.26.** Show that subcube-partition size/codimension and parity-decision-tree size/depth generalize ordinary decision-tree size/depth, and that affine-subspace partitions generalize both. Extend Proposition 3.16 to these models, except that the degree statement need not hold for parity decision trees or affine-subspace partitions. Show that functions with affine-subspace partition size at most \(s\) are query-learnable with error \(\varepsilon\) in time \(\operatorname{poly}(n,s,1/\varepsilon)\).

<a id="pdf-ffbe9c7b3306-p088-b005"></a>
<!-- pdf-source: page=88; block=5; confidence=0.98 -->
**Exercise 3.27.** Define \(\mathrm{Equ}_3:\{-1,1\}^3\to\{-1,1\}\) by \(\mathrm{Equ}_3(x)=-1\) iff \(x_1=x_2=x_3\). Show \(\deg(\mathrm{Equ}_3)=2\), \(\mathrm{DT}(\mathrm{Equ}_3)=3\), and it is computable by a parity decision tree of codimension 2. For \(f=\mathrm{Equ}_3^{\otimes d}\), show \(f:\{-1,1\}^{3^d}\to\{-1,1\}\), \(\deg(f)=2^d\), and \(\mathrm{DT}(f)=3^d\).

<a id="pdf-ffbe9c7b3306-p088-b006"></a>
<!-- pdf-source: page=88; block=6; confidence=0.99 -->
**Exercise 3.28.** For \(f:\{-1,1\}^n\to\mathbb R\) and \(J\subseteq[n]\), define \(f^{\subseteq J}(x)=\mathbb E_{y\sim\{-1,1\}^{\bar J}}[f(x_J,y)]\). Verify \(f^{\subseteq J}=\sum_{S\subseteq J}\widehat f(S)\chi_S\).

<a id="pdf-ffbe9c7b3306-p088-b007"></a>
<!-- pdf-source: page=88; block=7; confidence=0.98 -->
**Exercise 3.29.** Given a density \(\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}\) for a distribution \(\phi\) and \(J\subseteq[n]\), express in terms of \(\varphi\) the density of the marginal on \(J\), and the density after conditioning on a fixed substring \(z\in\mathbb F_2^J\), assuming the conditioning event has positive probability.

<a id="pdf-ffbe9c7b3306-p089-b001"></a>
<!-- pdf-source: page=89; block=1; confidence=0.99 -->
**Exercise 3.30.** If a decision tree for real-valued \(f\) has a leaf labeled \(b\) at depth \(k\), prove \(\|\widehat f\|_\infty\ge |b|/2^k\). Suggested tool: Exercise 3.28.

<a id="pdf-ffbe9c7b3306-p089-b002"></a>
<!-- pdf-source: page=89; block=2; confidence=1.00 -->
**Exercise 3.31.** Prove Fact 3.25 using Theorem 1.27 and Exercise 1.1(d).

<a id="pdf-ffbe9c7b3306-p089-b003"></a>
<!-- pdf-source: page=89; block=3; confidence=0.98 -->
**Exercise 3.32.** (a) Suppose \(f:\mathbb F_2^n\to\mathbb R\) has Fourier sparsity less than \(2^n\). Show that for every \(\gamma\in\operatorname{supp}(\widehat f)\), there is a nonzero \(\beta\in\mathbb F_2^n\) such that \(f_{\beta^\perp}\) has \(\widehat f(\gamma)\) as a Fourier coefficient. (b) Prove by induction that if Boolean \(f\) has Fourier sparsity \(s>1\), then \(\widehat f\) is \(2^{1-\lfloor\log_2s\rfloor}\)-granular. (c) Show there are no Boolean functions with Fourier sparsity in \(\{2,3,5,6,7,9\}\).

<a id="pdf-ffbe9c7b3306-p089-b004"></a>
<!-- pdf-source: page=89; block=4; confidence=0.98 -->
**Exercise 3.33.** Show that any Boolean function on \(n\) bits can be learned with zero error using only random examples in time \(\widetilde O(2^n)\).

<a id="pdf-ffbe9c7b3306-p089-b005"></a>
<!-- pdf-source: page=89; block=5; confidence=0.99 -->
**Exercise 3.34.** Strengthen Proposition 3.31: if Boolean \(f\) and real-valued \(g\) satisfy \(\|f-g\|_1\le\epsilon\), then a uniform threshold \(\theta\in[-1,1]\) gives \(h(x)=\operatorname{sgn}(g(x)-\theta)\) with \(\mathbb E_\theta[\operatorname{dist}(f,h)]\le\epsilon/2\).

<a id="pdf-ffbe9c7b3306-p089-b006"></a>
<!-- pdf-source: page=89; block=6; confidence=0.99 -->
**Exercise 3.35.** (a) For even \(n\), construct Boolean \(f\) whose Fourier spectrum is not \(1/2\)-concentrated on any \(\mathcal F\subseteq2^{[n]}\) of size below \(2^{n-1}\); use Exercise 1.1. (b) For a random Boolean function as in Exercise 1.7, prove with probability at least \(1/2\) that its spectrum is not \(1/4\)-concentrated on degrees at most \(\lfloor n/2\rfloor\).

<a id="pdf-ffbe9c7b3306-p089-b007"></a>
<!-- pdf-source: page=89; block=7; confidence=0.99 -->
**Exercise 3.36.** Prove Theorem 3.36; use Exercise 1.11 to round certain estimates.

<a id="pdf-ffbe9c7b3306-p089-b008"></a>
<!-- pdf-source: page=89; block=8; confidence=0.99 -->
**Exercise 3.37.** Establish exact query learning in time \(\operatorname{poly}(n,2^k)\) for the nested Boolean classes: (a) \(k\)-juntas, (b) functions with \(\operatorname{DT}(f)\le k\), and (c) functions with Fourier sparsity at most \(2^{O(k)}\). Suggested tools are influence estimates for (a) and Exercise 3.32 for (c).

<a id="pdf-ffbe9c7b3306-p089-b009"></a>
<!-- pdf-source: page=89; block=9; confidence=1.00 -->
**Exercise 3.38.** Prove Theorem 3.38 using Exercise 3.16.

<a id="pdf-ffbe9c7b3306-p089-b010"></a>
<!-- pdf-source: page=89; block=10; confidence=1.00 -->
**Exercise 3.39.** Deduce Theorem 3.37 from the Goldreich–Levin Algorithm.

<a id="pdf-ffbe9c7b3306-p089-b011"></a>
<!-- pdf-source: page=89; block=11; confidence=0.99 -->
**Exercise 3.40(a).** Suppose \(A\) learns \(\mathcal C\) from random examples to error \(\epsilon/2\) in time \(T\), with success probability at least \(9/10\). For its hypothesis \(h\), construct a test taking \(\operatorname{poly}(n,T,1/\epsilon)\log(1/\delta)\) time that, except with probability \(\delta\), accepts when \(\operatorname{dist}(f,h)\le\epsilon/2\) and rejects when \(\operatorname{dist}(f,h)>\epsilon\). Evaluating \(h\) may take \(\operatorname{poly}(T)\) time.

<a id="pdf-ffbe9c7b3306-p090-b001"></a>
<!-- pdf-source: page=90; block=1; confidence=0.95 -->
**Exercise 3.40(b).** For every \(\delta\in(0,1/2]\), show that a learner learns \(\mathcal C\) with error \(\varepsilon\) in time \(\operatorname{poly}(n,T,1/\varepsilon)\log(1/\delta)\), with probability at least \(1-\delta\).

<a id="pdf-ffbe9c7b3306-p090-b002"></a>
<!-- pdf-source: page=90; block=2; confidence=0.99 -->
**Exercise 3.41.** (a) Show that the Low-Degree Algorithm can estimate all coefficients of degree at most \(k\) from one shared batch \(E\) of \(\operatorname{poly}(n^k,1/\epsilon)\) random examples. (b) Express its hypothesis as \[h(y)=\operatorname{sgn}\!\left(\sum_{(x,f(x))\in E}w(\Delta(y,x))f(x)\right),\] where \(w:\{0,\ldots,n\}\to\mathbb R\) depends only on Hamming distance, and simplify \(w\).

<a id="pdf-ffbe9c7b3306-p090-b003"></a>
<!-- pdf-source: page=90; block=3; confidence=0.99 -->
**Exercise 3.42.** Extend Goldreich–Levin to targets \(f:\{-1,1\}^n\to[-1,1]\), assuming each queried value is rational with a \(\operatorname{poly}(n)\)-bit representation.

<a id="pdf-ffbe9c7b3306-p090-b004"></a>
<!-- pdf-source: page=90; block=4; confidence=0.99 -->
**Exercise 3.43.** (a) For distinct \(\gamma,\gamma'\in\mathbb F_2^n\), prove \(\Pr_x[\gamma\cdot x=\gamma'\cdot x]=1/2\). (b) For fixed \(\gamma\), show that \(m=Cn\) independent uniform examples, with sufficiently large constant \(C\), uniquely determine \(\gamma\) with high probability through the equations \(\gamma'\cdot x^{(i)}=\gamma\cdot x^{(i)}\). (c) Learn all linear maps \(\mathbb F_2^n\to\mathbb F_2\) exactly from random examples in polynomial time, improving Exercise 1.27; \(O(n^\omega)\) time suffices when matrix multiplication has that complexity.

<a id="pdf-ffbe9c7b3306-p090-b005"></a>
<!-- pdf-source: page=90; block=5; confidence=0.99 -->
**Exercise 3.44.** Given query access to Boolean \(f\) and \(\tau\ge1/2+\epsilon\), find with high probability the unique \(U\subseteq[n]\) satisfying \(|\widehat f(U)|\ge\tau\), assuming it exists, in time \(\operatorname{poly}(n,1/\epsilon)\). Seek an algorithm simpler than Goldreich–Levin using Proposition 1.31 and Exercise 1.27.

<a id="pdf-ffbe9c7b3306-p090-b006"></a>
<!-- pdf-source: page=90; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p091-b001"></a>
<!-- pdf-source: page=91; block=1; confidence=0.99 -->
For a bijection f on 𝔽₂ⁿ, define g(r,s) = (r,f(s),r·s), with input length k = 2n and output length m = 2n+1. Uniform independent r,s give uniform first 2n output bits. The exercise reduces efficient prediction of the last bit to inversion of f.

<a id="pdf-ffbe9c7b3306-p091-b002"></a>
<!-- pdf-source: page=91; block=2; confidence=0.98 -->
**Exercise (continued), (a)–(d).** Assume an efficient deterministic predictor A satisfies Prᵣ,ₛ[A(r,f(s)) = r·s] ≥ 1/2+γ. (a) Show that some B ⊆ 𝔽₂ⁿ has |B|/2ⁿ ≥ γ/2 and, for every s ∈ B, Prᵣ[A(r,f(s)) = r·s] ≥ 1/2+γ/2. (b) With ±1-valued outputs, deduce that the Fourier coefficient of r ↦ A(r,f(s)) at s is at least γ. (c) Use Goldreich–Levin to recover s efficiently from f(s), with high probability for s ∈ B; nonnegligible γ contradicts one-wayness. (d) Extend the reduction to randomized A.

<a id="pdf-ffbe9c7b3306-p091-b003"></a>
<!-- pdf-source: page=91; block=3; confidence=0.99 -->
Under pointwise multiplication, the characters χγ : 𝔽₂ⁿ → {−1,1} form a group isomorphic to 𝔽₂ⁿ, an instance of finite abelian Pontryagin duality. The notes attribute Fourier sparsity as a complexity measure to Karpovsky, early decision-tree and subcube-partition connections to Brandman, and the uncertainty principle in Exercise 3.15 to Matolcsi–Szücs.

<a id="pdf-ffbe9c7b3306-p091-b004"></a>
<!-- pdf-source: page=91; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p091-b005"></a>
<!-- pdf-source: page=91; block=5; confidence=0.99 -->
**Theorem (Nisan–Szegedy, cited).** Every f : {−1,1}ⁿ → {−1,1} admits a decision tree of depth at most poly(deg(f)). This supplies a converse in one direction to Proposition 3.16; Theorem 3.4 is also attributed to Nisan–Szegedy.

<a id="pdf-ffbe9c7b3306-p092-b001"></a>
<!-- pdf-source: page=92; block=1; confidence=0.99 -->
The notes give Midrijānis's bound D(f) ≤ deg(f)³ and cite the Nisan–Szegedy example in Exercise 3.27 as ruling out a linear bound in degree.

<a id="pdf-ffbe9c7b3306-p092-b002"></a>
<!-- pdf-source: page=92; block=2; confidence=0.99 -->
Attributions: Valiant introduced computational learning theory; Linial–Mansour–Nisan developed the Fourier Low-Degree Algorithm, with its noise-sensitivity approach due to Klivans–O'Donnell–Servedio. Corollary 3.33 is credited to Bshouty–Tamon. Goldreich–Levin also gives local list decoding of the Hadamard code. Kushilevitz–Mansour supplied their namesake algorithm and Exercises 3.37(b), 3.38; Gopalan et al. supplied Exercises 3.32, 3.37(c).

<a id="pdf-ffbe9c7b3306-p093-b001"></a>
<!-- pdf-source: page=93; block=1; confidence=1.00 -->
# Chapter 4. DNF formulas and small-depth circuits

<a id="pdf-ffbe9c7b3306-p093-b002"></a>
<!-- pdf-source: page=93; block=2; confidence=0.99 -->
Small DNF formulas and constant-depth circuits generalize decision trees and exhibit strong Fourier concentration.

<a id="pdf-ffbe9c7b3306-p093-b003"></a>
<!-- pdf-source: page=93; block=3; confidence=1.00 -->
## 4.1. DNF formulas

<a id="pdf-ffbe9c7b3306-p093-b004"></a>
<!-- pdf-source: page=93; block=4; confidence=1.00 -->
**Definition 4.1.** A DNF formula is an OR of terms, each an AND of literals xᵢ or ¬xᵢ. No term may contain both xᵢ and ¬xᵢ. A term's width is its number of literals. A formula is identified with its computed function f : {0,1}ⁿ → {0,1}.

<a id="pdf-ffbe9c7b3306-p093-b005"></a>
<!-- pdf-source: page=93; block=5; confidence=0.97 -->
**Example 4.2.** \(\mathrm{Sort}_3(x_1,x_2,x_3)=1\) iff \(x_1\le x_2\le x_3\) or \(x_1\ge x_2\ge x_3\). The DNF is \((x_1\land x_2)\lor(\bar x_2\land\bar x_3)\lor(x_1\land x_3)\lor(x_1\land\bar x_3)\), as displayed in the scan.

<a id="pdf-ffbe9c7b3306-p094-b001"></a>
<!-- pdf-source: page=94; block=1; confidence=0.94 -->
The preceding sorting DNF accepts when the first two bits are 1, the last two are 0, or the first and last bits differ.

<a id="pdf-ffbe9c7b3306-p094-b002"></a>
<!-- pdf-source: page=94; block=2; confidence=1.00 -->
**Definition 4.3.** A DNF's size is its number of terms; its width is the largest number of literals in a term. For Boolean $f$, $\operatorname{DNFsize}(f)$ and $\operatorname{DNFwidth}(f)$ minimize these quantities over DNFs computing $f$.

<a id="pdf-ffbe9c7b3306-p094-b003"></a>
<!-- pdf-source: page=94; block=3; confidence=1.00 -->
Example 4.2 represents $\mathrm{Sort}_3$ with size 3 and width 2. Every $n$-variable Boolean function admits a DNF with size at most $2^n$ and width at most $n$ (Exercise 4.1).

<a id="pdf-ffbe9c7b3306-p094-b004"></a>
<!-- pdf-source: page=94; block=4; confidence=1.00 -->
**Definition 4.4.** A CNF is an AND of clauses, each an OR of literals. Its size counts clauses, and its width is the maximum clause width.

<a id="pdf-ffbe9c7b3306-p094-b005"></a>
<!-- pdf-source: page=94; block=5; confidence=0.99 -->
Interchanging AND and OR in a CNF for $f$ yields a DNF for its dual $f^\dagger$. Their Fourier expansions are closely related, allowing analogous Fourier analysis despite potentially different representation sizes.

<a id="pdf-ffbe9c7b3306-p094-b006"></a>
<!-- pdf-source: page=94; block=6; confidence=1.00 -->
**Proposition 4.5.** If a decision tree of size $s$ and depth $k$ computes $f:\{0,1\}^n\to\{0,1\}$, then $f$ has both a DNF and a CNF of size at most $s$ and width at most $k$.

<a id="pdf-ffbe9c7b3306-p094-b007"></a>
<!-- pdf-source: page=94; block=7; confidence=1.00 -->
**Proof.** For the DNF, conjoin the path literals for each 1-leaf and disjoin these terms. For the CNF, use one clause per 0-leaf, disjoining the negations of its path literals. Leaf counts bound size; path lengths bound width.

<a id="pdf-ffbe9c7b3306-p094-b008"></a>
<!-- pdf-source: page=94; block=8; confidence=0.98 -->
**Example 4.6.** Converting the Figure 3.1 decision tree for \(\mathrm{Sort}_3\) gives the DNF \((\bar x_1\land\bar x_3\land\bar x_2)\lor(\bar x_1\land x_3)\lor(x_1\land\bar x_2\land\bar x_3)\lor(x_2\land x_3)\). This representation has size 4 and width 3; DNF representations are not unique.

<a id="pdf-ffbe9c7b3306-p095-b001"></a>
<!-- pdf-source: page=95; block=1; confidence=1.00 -->
Low-degree Fourier concentration for DNFs is first approached through total influence, using $\{-1,1\}$ notation.

<a id="pdf-ffbe9c7b3306-p095-b002"></a>
<!-- pdf-source: page=95; block=2; confidence=1.00 -->
**Proposition 4.7.** For $f:\{-1,1\}^n\to\{-1,1\}$ with $\operatorname{DNFwidth}(f)\le w$, the total influence satisfies $I[f]\le 2w$.

<a id="pdf-ffbe9c7b3306-p095-b003"></a>
<!-- pdf-source: page=95; block=3; confidence=1.00 -->
**Proof.** Exercise 2.10 gives $I[f]=2\mathbb E_x[\#\{i:f(x)=-1,\ f(x^{\oplus i})=1\}]$. If $f(x)=-1$ (True), choose a satisfied DNF term $T$. Every such pivotal coordinate must occur in $T$, since flipping an absent coordinate preserves its truth. Thus each input has at most $w$ such coordinates.

<a id="pdf-ffbe9c7b3306-p095-b004"></a>
<!-- pdf-source: page=95; block=4; confidence=1.00 -->
Since $I[f^\dagger]=I[f]$, width-$w$ CNFs also satisfy $I[f]\le2w$. Parity $\chi_{[w]}$ has influence $w$ and DNF width at most $w$, as does every $w$-junta. Exercise 4.17 improves the upper bound to the sharp value $w$.

<a id="pdf-ffbe9c7b3306-p095-b005"></a>
<!-- pdf-source: page=95; block=5; confidence=0.99 -->
**Corollary 4.8.** If $\operatorname{DNFwidth}(f)\le w$, then for every $\epsilon>0$ its Fourier spectrum is $\epsilon$-concentrated on degrees at most $2w/\epsilon$, by Proposition 3.2. Parity shows that the order of dependence on $w$ is necessary.

<a id="pdf-ffbe9c7b3306-p095-b006"></a>
<!-- pdf-source: page=95; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p095-b007"></a>
<!-- pdf-source: page=95; block=7; confidence=1.00 -->
**Proof.** Delete every term containing more than $\log(s/\epsilon)$ literals and let $g$ be the resulting DNF's function.

<a id="pdf-ffbe9c7b3306-p096-b001"></a>
<!-- pdf-source: page=96; block=1; confidence=1.00 -->
**Proof (continued).** Each removed term is satisfied with probability at most $2^{-\log(s/\epsilon)}=\epsilon/s$. Disagreement requires some removed term to be satisfied, so a union bound over at most $s$ terms yields $\Pr[g(x)\ne f(x)]\le\epsilon$. Clause deletion gives the analogous CNF argument.

<a id="pdf-ffbe9c7b3306-p096-b002"></a>
<!-- pdf-source: page=96; block=2; confidence=1.00 -->
Proposition 4.9, Corollary 4.8, and Exercise 3.17 imply $\epsilon$-concentration for size-$s$ DNFs through degree $O(\log(s/\epsilon)/\epsilon)$. Later sections establish $I[f]=O(\log s)$ and, for polynomial-size DNFs and constant $\epsilon>0$, concentration on $n^{O(\log\log n)}$ Fourier coefficients.

<a id="pdf-ffbe9c7b3306-p096-b003"></a>
<!-- pdf-source: page=96; block=3; confidence=1.00 -->
**Mansour's Conjecture.** If $f$ has a size-$s$ DNF with $s>1$ and $\epsilon\in(0,1/2]$, the strong conjecture predicts $\epsilon$-concentration on a Fourier collection $\mathcal F$ of size at most $s^{O(\log(1/\epsilon))}$. The weaker conjecture predicts $|\mathcal F|\le\operatorname{poly}(n)$ when $s\le\operatorname{poly}(n)$ and $\epsilon>0$ is fixed.

<a id="pdf-ffbe9c7b3306-p096-b004"></a>
<!-- pdf-source: page=96; block=4; confidence=1.00 -->
## 4.2. Tribes

<a id="pdf-ffbe9c7b3306-p096-b005"></a>
<!-- pdf-source: page=96; block=5; confidence=1.00 -->
**Definition (recalled).** Partition $sw$ variables into $s$ disjoint blocks of size $w$ and set
$$\mathrm{Tribes}_{w,s}(x)=\bigvee_{j=0}^{s-1}\left(\bigwedge_{i=1}^{w}x_{jw+i}\right).$$
Here $-1$ means True. This DNF has width $w$ and size $s$; suitable parameters make it nearly unbiased with small individual influences.

<a id="pdf-ffbe9c7b3306-p096-b006"></a>
<!-- pdf-source: page=96; block=6; confidence=1.00 -->
**Fact 4.10.** Under uniform input,
$$\Pr_x[\mathrm{Tribes}_{w,s}(x)=-1]=1-(1-2^{-w})^s.$$
The computation is referenced to Exercise 2.13.

<a id="pdf-ffbe9c7b3306-p096-b007"></a>
<!-- pdf-source: page=96; block=7; confidence=0.99 -->
**Definition 4.11.** For a positive integer $w$, choose the largest integer $s=s_w$ satisfying $1-(1-2^{-w})^s\le1/2$. Put $n=n_w=s_ww$ and define $\mathrm{Tribes}_n=\mathrm{Tribes}_{w,s_w}$. The allowed dimensions begin $1,4,15,40,\ldots$.

<a id="pdf-ffbe9c7b3306-p097-b001"></a>
<!-- pdf-source: page=97; block=1; confidence=0.99 -->
The balancing choice gives $s\approx (\ln 2)2^w$, $n\approx (\ln 2)w2^w$, $w\approx\log n-\log\ln n$, and $s\approx n/\log n$.

<a id="pdf-ffbe9c7b3306-p097-b002"></a>
<!-- pdf-source: page=97; block=2; confidence=0.99 -->
**Proposition 4.12.** For $\mathrm{Tribes}_n$ from Definition 4.11:
- $s=(\ln 2)2^w-\Theta_w(1)$;
- $n=(\ln 2)w2^w-\Theta(w)$, so $n_{w+1}=(2+o(1))n_w$;
- $w=\log n-\log\ln n+o_n(1)$ and $2^w=\frac{n}{\ln n}(1+o_n(1))$;
- $\Pr[\mathrm{Tribes}_n(x)=-1]=\frac12-O(\log n/n)$.
Thus the function is asymptotically unbiased.

<a id="pdf-ffbe9c7b3306-p097-b003"></a>
<!-- pdf-source: page=97; block=3; confidence=1.00 -->
**Proposition 4.13.** Each coordinate satisfies $\operatorname{Inf}_i[\mathrm{Tribes}_n]=\frac{\ln n}{n}(1\pm o(1))$; consequently $\mathbf I[\mathrm{Tribes}_n]=(\ln n)(1\pm o(1))$.

<a id="pdf-ffbe9c7b3306-p097-b004"></a>
<!-- pdf-source: page=97; block=4; confidence=1.00 -->
**Proof.** Coordinate $i$ is pivotal exactly when its other tribe members all equal $-1$ and every other tribe outputs $1$. Independence gives
$$\operatorname{Inf}_i[\mathrm{Tribes}_n]=2^{-(w-1)}(1-2^{-w})^{s-1}=\frac{2}{2^w-1}\Pr[\mathrm{Tribes}_n=1]=\frac{\ln n}{n}(1\pm o(1)),$$
using Fact 4.10 and Proposition 4.12.

<a id="pdf-ffbe9c7b3306-p097-b005"></a>
<!-- pdf-source: page=97; block=5; confidence=1.00 -->
Tribes has smaller individual influences than majority's $\Theta(n^{-1/2})$. For unbiased Boolean functions, Poincaré gives $\mathbf I[f]\ge1$, hence maximum influence at least $1/n$; KKL strengthens this to the Tribes scale up to constants.

<a id="pdf-ffbe9c7b3306-p097-b006"></a>
<!-- pdf-source: page=97; block=6; confidence=1.00 -->
**Kahn–Kalai–Linial (KKL) Theorem.** Every $f:\{-1,1\}^n\to\{-1,1\}$ satisfies
$$\operatorname{MaxInf}[f]:=\max_{i\in[n]}\operatorname{Inf}_i[f]\ge\operatorname{Var}[f]\,\Omega\!\left(\frac{\log n}{n}\right).$$
The proof is deferred to Chapter 9.

<a id="pdf-ffbe9c7b3306-p097-b007"></a>
<!-- pdf-source: page=97; block=7; confidence=1.00 -->
**Proposition 4.14.** For $\mathrm{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}$, write $T_i$ for the intersection of $T\subseteq[sw]$ with tribe $i$, and $k=|\{i:T_i\ne\varnothing\}|$. Then
$$\widehat{\mathrm{Tribes}_{w,s}}(T)=\begin{cases}2(1-2^{-w})^s-1,&T=\varnothing,\\2(-1)^{k+|T|}2^{-kw}(1-2^{-w})^{s-k},&k>0.\end{cases}$$
The proof is assigned in Exercise 4.6.

<a id="pdf-ffbe9c7b3306-p098-b001"></a>
<!-- pdf-source: page=98; block=1; confidence=1.00 -->
## 4.3. Random restrictions

<a id="pdf-ffbe9c7b3306-p098-b002"></a>
<!-- pdf-source: page=98; block=2; confidence=1.00 -->
Random restrictions simplify DNFs while allowing Fourier analysis. The proposed route to $\mathbf I[f]=O(\log s)$ for size-$s$ DNFs is to show that random partial inputs typically reduce their width.

<a id="pdf-ffbe9c7b3306-p098-b003"></a>
<!-- pdf-source: page=98; block=3; confidence=0.99 -->
**Definition 4.15.** A $\delta$-random subset includes each element independently with probability $\delta\in[0,1]$. A $\delta$-random restriction $(J\mid z)$ chooses such a subset $J\subseteq[n]$ of free coordinates and assigns independent uniform signs $z$ to $J^c$. Equivalently, each coordinate independently remains free with probability $\delta$, or is fixed to either sign with probability $(1-\delta)/2$.

<a id="pdf-ffbe9c7b3306-p098-b004"></a>
<!-- pdf-source: page=98; block=4; confidence=0.99 -->
**Definition 4.16.** For $f:\{-1,1\}^n\to\mathbb R$, free set $I\subseteq[n]$, and fixed assignment $z\in\{-1,1\}^{I^c}$, identify $f_{I\mid z}:\{-1,1\}^I\to\mathbb R$ with its extension to the full cube that ignores coordinates in $I^c$.

<a id="pdf-ffbe9c7b3306-p098-b005"></a>
<!-- pdf-source: page=98; block=5; confidence=1.00 -->
**Proposition 4.17.** For $f:\{-1,1\}^n\to\mathbb R$, $S\subseteq[n]$, and a $\delta$-random restriction, using the full-cube extension,
$$\mathbb E[\widehat{f_{J\mid z}}(S)]=\Pr[S\subseteq J]\widehat f(S)=\delta^{|S|}\widehat f(S),$$
$$\mathbb E[\widehat{f_{J\mid z}}(S)^2]=\sum_{U\subseteq[n]}\Pr[U\cap J=S]\widehat f(U)^2=\sum_{U\supseteq S}\delta^{|S|}(1-\delta)^{|U\setminus S|}\widehat f(U)^2.$$

<a id="pdf-ffbe9c7b3306-p099-b001"></a>
<!-- pdf-source: page=99; block=1; confidence=1.00 -->
**Proof.** With $J$ fixed, Corollary 3.22 gives
$$\mathbb E_z[\widehat{f_{J\mid z}}(S)]=\widehat f(S)\mathbf1_{S\subseteq J},\qquad \mathbb E_z[\widehat{f_{J\mid z}}(S)^2]=\sum_{U\subseteq[n]}\widehat f(U)^2\mathbf1_{U\cap J=S}.$$
Averaging these identities over $J$ proves both claims.

<a id="pdf-ffbe9c7b3306-p099-b002"></a>
<!-- pdf-source: page=99; block=2; confidence=1.00 -->
**Corollary 4.18.** For real-valued $f$ on the cube and a $\delta$-random restriction,
$$\mathbb E[\operatorname{Inf}_i[f_{J\mid z}]]=\delta\operatorname{Inf}_i[f],\qquad \mathbb E[\mathbf I[f_{J\mid z}]]=\delta\mathbf I[f].$$

<a id="pdf-ffbe9c7b3306-p099-b003"></a>
<!-- pdf-source: page=99; block=3; confidence=1.00 -->
**Proof.** Apply Proposition 4.17 to the Fourier expression for influence and interchange finite sums:
$$\mathbb E[\operatorname{Inf}_i[f_{J\mid z}]]=\sum_U\Pr[i\in U\cap J]\widehat f(U)^2=\delta\sum_{U\ni i}\widehat f(U)^2=\delta\operatorname{Inf}_i[f].$$
Summing over $i$ yields the total-influence identity.

<a id="pdf-ffbe9c7b3306-p099-b004"></a>
<!-- pdf-source: page=99; block=4; confidence=1.00 -->
Corollary 4.18 reduces bounding original total influence to bounding expected restricted influence; the next lemma controls the width of surviving DNF terms.

<a id="pdf-ffbe9c7b3306-p099-b005"></a>
<!-- pdf-source: page=99; block=5; confidence=0.99 -->
**Lemma 4.19.** If $T$ is a DNF term, $w$ is a positive integer, and $(J\mid z)$ is a $1/2$-random restriction, then
$$\Pr[\operatorname{width}(T_{J\mid z})\ge w]\le(3/4)^w.$$

<a id="pdf-ffbe9c7b3306-p099-b006"></a>
<!-- pdf-source: page=99; block=6; confidence=1.00 -->
**Proof.** Terms initially narrower than $w$ cannot reach width $w$. Otherwise, any literal fixed to False makes the term constantly False, of width zero. Each literal independently has this outcome with probability $1/4$, so survival of at least $w$ initial literals has probability at most $(3/4)^w$.

<a id="pdf-ffbe9c7b3306-p099-b007"></a>
<!-- pdf-source: page=99; block=7; confidence=1.00 -->
**Theorem 4.20.** If $f:\{-1,1\}^n\to\{-1,1\}$ has a DNF representation of size $s$, then $\mathbf I[f]\le O(\log s)$.

<a id="pdf-ffbe9c7b3306-p100-b001"></a>
<!-- pdf-source: page=100; block=1; confidence=0.98 -->
**Proof (continued).** For a half-random restriction, let \(W=\operatorname{DNFwidth}(f_{J\mid z})\). A union bound with Lemma 4.19 gives \(\Pr[W\ge t]\le s(3/4)^t\), hence
\[
\mathbb E W=\sum_{t\ge1}\Pr[W\ge t]
\le3\log s+4s(3/4)^{3\log s}
\le3\log s+4/s^{0.2}=O(\log s).
\]
Proposition 4.7 yields \(\mathbb E\,\mathrm I[f_{J\mid z}]=O(\log s)\); Corollary 4.18 then gives \(\mathrm I[f]=2\mathbb E\,\mathrm I[f_{J\mid z}]=O(\log s)\).

<a id="pdf-ffbe9c7b3306-p100-b002"></a>
<!-- pdf-source: page=100; block=2; confidence=1.00 -->
## 4.4. Håstad’s Switching Lemma and the spectrum of DNFs

<a id="pdf-ffbe9c7b3306-p100-b003"></a>
<!-- pdf-source: page=100; block=3; confidence=0.99 -->
When \(\delta\ll1/w\), a random restriction usually falsifies a width-\(w\) term or makes it identically true; leaving a nonconstant surviving term is less likely.

<a id="pdf-ffbe9c7b3306-p100-b004"></a>
<!-- pdf-source: page=100; block=4; confidence=1.00 -->
**Baby Switching Lemma.** If \(f:\{-1,1\}^n\to\{-1,1\}\) has a DNF or CNF representation of width at most \(w\), then a \(\delta\)-random restriction satisfies
\[
\Pr[f_{J\mid z}\text{ is nonconstant}]\le5\delta w.
\]

<a id="pdf-ffbe9c7b3306-p100-b005"></a>
<!-- pdf-source: page=100; block=5; confidence=1.00 -->
**Håstad’s Switching Lemma.** Let \(f\) be computable by a DNF or CNF of width at most \(w\), and let \((J\mid z)\) be a \(\delta\)-random restriction. For any \(k\in\mathbb N\), \(\Pr[\operatorname{DT}(f_{J\mid z})\ge k]\le(5\delta w)^k\).

<a id="pdf-ffbe9c7b3306-p100-b006"></a>
<!-- pdf-source: page=100; block=6; confidence=1.00 -->
The depth-tail estimate is independent of both DNF size and ambient dimension; for \(\delta\ll1/w\), failure to obtain depth below \(k\) has exponentially decreasing probability.

<a id="pdf-ffbe9c7b3306-p101-b001"></a>
<!-- pdf-source: page=101; block=1; confidence=1.00 -->
Exercise 4.19 treats the baby lemma; proofs of the full lemma are cited as [Hås87] and [Raz93, Bea94]. Combining decision-tree Fourier bounds (Proposition 3.16) with restriction identities (Proposition 4.17) gives spectral concentration for narrow DNFs.

<a id="pdf-ffbe9c7b3306-p101-b002"></a>
<!-- pdf-source: page=101; block=2; confidence=0.99 -->
**Lemma 4.21.** Let \(f:\{-1,1\}^n\to\{-1,1\}\), let \((J\mid z)\) be a \(\delta\)-random restriction with \(\delta>0\), and fix a positive integer \(k\). Set \(\epsilon=\Pr[\operatorname{DT}(f_{J\mid z})\ge k]\). Then the Fourier spectrum of \(f\) is \(3\epsilon\)-concentrated on degrees at most \(3k/\delta\).

<a id="pdf-ffbe9c7b3306-p101-b003"></a>
<!-- pdf-source: page=101; block=3; confidence=1.00 -->
**Proof.** Proposition 3.16 implies that depth below \(k\) forces degree below \(k\); Parseval bounds the restricted Fourier tail by \(1\) otherwise. Thus Proposition 4.17 gives
\[
\epsilon\ge\mathbb E\sum_{|S|\ge k}\widehat{f_{J\mid z}}(S)^2
=\sum_{U\subseteq[n]}\Pr[|U\cap J|\ge k]\widehat f(U)^2.
\]
Here \(|U\cap J|\sim\operatorname{Binomial}(|U|,\delta)\). If \(|U|\ge3k/\delta\), Chernoff's bound gives \(\Pr[|U\cap J|<k]\le e^{-2k/3}\le2/3\). Consequently
\[
\epsilon\ge\tfrac13\sum_{|U|\ge3k/\delta}\widehat f(U)^2,
\]
which proves the concentration bound.

<a id="pdf-ffbe9c7b3306-p101-b004"></a>
<!-- pdf-source: page=101; block=4; confidence=0.99 -->
**Theorem 4.22.** A Boolean function computable by a width-\(w\) DNF has Fourier spectrum \(\epsilon\)-concentrated on degrees at most \(O(w\log(1/\epsilon))\), improving the error dependence in Corollary 4.8.

<a id="pdf-ffbe9c7b3306-p101-b005"></a>
<!-- pdf-source: page=101; block=5; confidence=1.00 -->
**Proof.** Choose \(\delta=1/(10w)\) and \(k=C\log(1/\epsilon)\) with sufficiently large \(C\). The switching lemma bounds the depth-tail probability by \(2^{-k}\); Lemma 4.21 converts this into the claimed degree cutoff and error.

<a id="pdf-ffbe9c7b3306-p101-b006"></a>
<!-- pdf-source: page=101; block=6; confidence=1.00 -->
Replacing the degree bound in Lemma 4.21 by the estimate \(\|\widehat h\|_1\le2^k\) for depth-\(k\) decision trees leads to Lemma 4.23; this derivation is assigned in Exercise 4.11.

<a id="pdf-ffbe9c7b3306-p102-b001"></a>
<!-- pdf-source: page=102; block=1; confidence=1.00 -->
**Lemma 4.23.** For Boolean \(f\) and a \(\delta\)-random restriction,
\[
\sum_{U\subseteq[n]}\delta^{|U|}|\widehat f(U)|
\le\mathbb E_{(J\mid z)}\!\left[2^{\operatorname{DT}(f_{J\mid z})}\right].
\]

<a id="pdf-ffbe9c7b3306-p102-b002"></a>
<!-- pdf-source: page=102; block=2; confidence=1.00 -->
**Theorem 4.24.** If \(f\) is computable by a width-\(w\) DNF, then for every degree cutoff \(k\),
\[
\sum_{|U|\le k}|\widehat f(U)|\le2(20w)^k.
\]

<a id="pdf-ffbe9c7b3306-p102-b003"></a>
<!-- pdf-source: page=102; block=3; confidence=1.00 -->
**Proof.** With \(\delta=1/(20w)\), the switching lemma gives
\[
\mathbb E\!\left[2^{\operatorname{DT}(f_{J\mid z})}\right]
\le\sum_{d\ge0}(5/20)^d2^d=2.
\]
Lemma 4.23 therefore implies
\[
2\ge\sum_U(20w)^{-|U|}|\widehat f(U)|
\ge(20w)^{-k}\sum_{|U|\le k}|\widehat f(U)|,
\]
which yields the result.

<a id="pdf-ffbe9c7b3306-p102-b004"></a>
<!-- pdf-source: page=102; block=4; confidence=1.00 -->
**Theorem 4.25.** If \(f\) has a DNF representation of width \(w\ge2\), then for every \(\epsilon\in(0,1/2]\), its Fourier spectrum is \(\epsilon\)-concentrated on some collection \(\mathcal F\) with
\[
|\mathcal F|\le w^{O(w\log(1/\epsilon))}.
\]

<a id="pdf-ffbe9c7b3306-p102-b005"></a>
<!-- pdf-source: page=102; block=5; confidence=1.00 -->
**Proof.** Put \(k=Cw\log(4/\epsilon)\) and let \(g=f^{\le k}\) be the degree-\(k\) Fourier truncation. For sufficiently large \(C\), Theorem 4.22 gives \(\|f-g\|_2^2\le\epsilon/4\), while Theorem 4.24 gives \(\|\widehat g\|_1\le w^{O(w\log(1/\epsilon))}\). Exercise 3.16 supplies a collection on which \(g\) is \(\epsilon/4\)-concentrated, of size
\[
|\mathcal F|\le4\|\widehat g\|_1^2/\epsilon
\le w^{O(w\log(1/\epsilon))}.
\]
Exercise 3.17 transfers \(\epsilon\)-concentration to \(f\) on the same collection.

<a id="pdf-ffbe9c7b3306-p102-b006"></a>
<!-- pdf-source: page=102; block=6; confidence=0.99 -->
For width \(O(\log n)\) and constant error, Theorem 4.25 gives a concentrating collection of size \(n^{O(\log\log n)}\). Proposition 4.9 and Exercise 3.17 extend this to polynomial-size DNFs; more generally, size \(s\) permits \(\epsilon\)-concentration on at most
\[
(s/\epsilon)^{O(\log\log(s/\epsilon)\log(1/\epsilon))}
\]
coefficients.

<a id="pdf-ffbe9c7b3306-p103-b001"></a>
<!-- pdf-source: page=103; block=1; confidence=1.00 -->
Switching-lemma methods for constant-depth circuits lead to Fourier consequences associated with Linial–Mansour–Nisan.

<a id="pdf-ffbe9c7b3306-p103-b002"></a>
<!-- pdf-source: page=103; block=2; confidence=0.99 -->
**Definition 4.26.** A depth-\(d\) circuit, for \(d\ge2\), is a directed acyclic graph whose gates are arranged in \(d+1\) layers, with wires from layer \(j-1\) to layer \(j\). Layer 0 has the \(2n\) input literals and layer \(d\) has one output. Odd gate layers use \(\land\) or \(\lor\) consistently; even gate layers use the other. AND and OR gates apply their operation to their incoming functions. The circuit computes the function at its output gate.

<a id="pdf-ffbe9c7b3306-p104-b001"></a>
<!-- pdf-source: page=104; block=1; confidence=0.98 -->
**Definition 4.27.** Circuit size counts gates in layers $1,\ldots,d-1$; width is the largest fan-in of a layer-$1$ gate. Repeated connections to a given variable or its negation at a layer-$1$ gate are forbidden.

<a id="pdf-ffbe9c7b3306-p104-b002"></a>
<!-- pdf-source: page=104; block=2; confidence=0.99 -->
An unbounded-fan-in AND/OR/NOT circuit can be put into the prescribed layered form with size overhead at most a factor $2d$.

<a id="pdf-ffbe9c7b3306-p104-b003"></a>
<!-- pdf-source: page=104; block=3; confidence=0.98 -->
**Lemma 4.28.** Let \(f:\{-1,1\}^n\to\{-1,1\}\) be computed by a depth-\(d\) circuit of size \(s\) and width \(w\), and let \(\varepsilon\in(0,1]\). Set \(\ell=\log(2s/\varepsilon)\) and \(\delta=\frac1{10w}(\frac1{10\ell})^{d-2}\). Then under a \(\delta\)-random restriction, \(\Pr[\operatorname{DT}(f_{J\mid z})\ge\log(2/\varepsilon)]\le\varepsilon\).

<a id="pdf-ffbe9c7b3306-p104-b004"></a>
<!-- pdf-source: page=104; block=4; confidence=0.99 -->
**Proof.** The case $d=2$ follows from Håstad’s Switching Lemma. For $d\ge3$, successive restrictions with survival probabilities $\delta_1,\delta_2$ compose to a $\delta_1\delta_2$-random restriction. Thus use one $1/(10w)$ restriction, then $d-3$ restrictions with parameter $1/(10\ell)$, and one final restriction with that parameter. Assume layer $2$ uses OR, so its gates compute width-$w$ DNFs. The first restriction turns each into a decision tree of depth at most $\ell$, hence a width-$\ell$ CNF by Proposition 4.5, with failure probability at most $2^{-\ell}$. If $s_2$ counts layer-$2$ gates, the union bound yields
$$\Pr[\text{some layer-2 gate cannot be replaced by a width-}\ell\text{ CNF}]\le s_2 2^{-\ell}.\tag{4.1}$$

<a id="pdf-ffbe9c7b3306-p104-b005"></a>
<!-- pdf-source: page=104; block=5; confidence=0.99 -->
**Proof (compression).** Once layer-$2$ DNFs are switched to width-$\ell$ CNFs, their AND outputs merge with layer $3$, reducing circuit depth to $d-1$ and width to at most $\ell$.

<a id="pdf-ffbe9c7b3306-p105-b001"></a>
<!-- pdf-source: page=105; block=1; confidence=0.99 -->
**Proof (continued).** Compression replaces length-$2$ paths from layer $1$ to layer $3$ by single wires and removes layer $2$. Figure 4.2 illustrates this after fixing $x_3=\mathrm{True}$, when three layer-$2$ DNFs admit width-$2$ CNFs. Outside the failure event (4.1), the reduced circuit has depth $d-1$, width at most $\ell$, and at most $s_3$ gates in its new layer $2$, where $s_3$ counts original layer-$3$ gates.

<a id="pdf-ffbe9c7b3306-p105-b002"></a>
<!-- pdf-source: page=105; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p106-b001"></a>
<!-- pdf-source: page=106; block=1; confidence=1.00 -->
## 4. DNF formulas and small-depth circuits

<a id="pdf-ffbe9c7b3306-p106-b002"></a>
<!-- pdf-source: page=106; block=2; confidence=0.92 -->
Assuming the preceding bad event does not occur, Håstad’s Switching Lemma says the final \(1/(10\ell)\)-random restriction reduces the circuit to a decision tree of depth less than \(\log(2/\varepsilon)\), except with probability at most \(\varepsilon/2\). This completes the proof.

<a id="pdf-ffbe9c7b3306-p106-b003"></a>
<!-- pdf-source: page=106; block=3; confidence=1.00 -->
The section next states the Linial–Mansour–Nisan Fourier concentration theorem.

<a id="pdf-ffbe9c7b3306-p106-b004"></a>
<!-- pdf-source: page=106; block=4; confidence=0.98 -->
**Theorem (LMN).** If $f:\{-1,1\}^n\to\{-1,1\}$ is computed by a depth-$d$ circuit of size $s>1$, then for $\varepsilon\in(0,1/2]$, its Fourier spectrum is $\varepsilon$-concentrated through degree $O(\log(s/\varepsilon))^{d-1}\log(1/\varepsilon)$.

<a id="pdf-ffbe9c7b3306-p106-b005"></a>
<!-- pdf-source: page=106; block=5; confidence=0.94 -->
**Proof.** If the circuit had width at most $w$, Lemmas 4.28 and 4.21 would give $3\varepsilon$-concentration through degree $30w(10\log(2s/\varepsilon))^{d-2}\log(2/\varepsilon)$. Delete layer-1 nodes of width at least $\log(s/\varepsilon)$; as in Proposition 4.9, the resulting circuit computes a function $\varepsilon$-close to $f$. Exercise 3.17 then yields $O(\varepsilon)$-concentration through degree $O(\log(2s/\varepsilon))^{d-1}\log(2/\varepsilon)$; adjusting constants gives the claim.

<a id="pdf-ffbe9c7b3306-p106-b006"></a>
<!-- pdf-source: page=106; block=6; confidence=0.99 -->
Håstad [Hås01a] improves the degree bound to $O(\log(s/\varepsilon))^{d-2}\log(s)\log(1/\varepsilon)$.

<a id="pdf-ffbe9c7b3306-p106-b007"></a>
<!-- pdf-source: page=106; block=7; confidence=0.99 -->
**Theorem 4.30.** If $f:\{-1,1\}^n\to\{-1,1\}$ is computed by a depth-$d$ circuit of size $s$, then $I[f]\le O(\log s)^{d-1}$.

<a id="pdf-ffbe9c7b3306-p106-b008"></a>
<!-- pdf-source: page=106; block=8; confidence=0.98 -->
The Fourier concentration results yield learning applications; the next theorem gives the LMN result for low-degree learning.

<a id="pdf-ffbe9c7b3306-p106-b009"></a>
<!-- pdf-source: page=106; block=9; confidence=0.96 -->
**Theorem 4.31.** The class of functions $f:\{-1,1\}^n\to\{-1,1\}$ computed by depth-$d$, polynomial-size circuits can be learned from random examples with any error $\varepsilon=1/\operatorname{poly}(n)$ in time $n^{O(\log n)^d}$.

<a id="pdf-ffbe9c7b3306-p106-b010"></a>
<!-- pdf-source: page=106; block=10; confidence=0.97 -->
Polynomial-size constant-depth circuits form $AC^0$, so the learning bound is quasipolynomial. The text notes a factoring-based hardness result and introduces Håstad’s result that $AC^0$ cannot even approximately compute parity, deriving it from LMN.

<a id="pdf-ffbe9c7b3306-p107-b001"></a>
<!-- pdf-source: page=107; block=1; confidence=1.00 -->
## 4.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p107-b002"></a>
<!-- pdf-source: page=107; block=2; confidence=0.95 -->
**Corollary 4.32.** Fix a constant $\varepsilon_0>0$. If a depth-$d$ circuit $C$ on $\{-1,1\}^n$ satisfies $\Pr_x[C(x)=\chi_{[n]}(x)]\ge 1/2+\varepsilon_0$, then its size is at least $2^{\Omega(n^{1/(d-1)})}$.

<a id="pdf-ffbe9c7b3306-p107-b003"></a>
<!-- pdf-source: page=107; block=3; confidence=0.97 -->
**Proof.** The hypothesis implies \(\widehat C([n])\ge2\varepsilon_0\), so the LMN theorem applies with \(\varepsilon=2\varepsilon_0^2\). The result follows by taking \(\varepsilon=2\varepsilon_0^2\) in that theorem.

<a id="pdf-ffbe9c7b3306-p107-b004"></a>
<!-- pdf-source: page=107; block=4; confidence=0.98 -->
The majority function satisfies \(I[\mathrm{Maj}_n]=\Theta(\sqrt n)\). Therefore any constant-depth circuit computing majority must have size at least \(2^{n^{\Omega(1)}}\).

<a id="pdf-ffbe9c7b3306-p107-b005"></a>
<!-- pdf-source: page=107; block=5; confidence=0.95 -->
A pseudorandom function generator is a function \(f:\mathbb F_2^m\times\mathbb F_2^n\to\mathbb F_2\) such that no efficient algorithm with query access can distinguish \(f(s,\cdot)\), for uniform seed \(s\), from a uniformly random function \(g:\mathbb F_2^n\to\mathbb F_2\), except with negligible advantage.

<a id="pdf-ffbe9c7b3306-p107-b006"></a>
<!-- pdf-source: page=107; block=6; confidence=0.95 -->
Theorem 4.30 rules out such generators computed in $AC^0$: let $A$ choose uniform $x\in\{-1,1\}^n$ and $i\in[n]$, query $h(x)$ and $h(x\oplus i)$, and accept when they differ. For uniform random $h$, acceptance probability is $1/2$; in general it is $I[h]/n$. If $h$ is $AC^0$-computable, Theorem 4.30 bounds this by $\operatorname{polylog}(n)/n$, far below $1/2$.

<a id="pdf-ffbe9c7b3306-p107-b007"></a>
<!-- pdf-source: page=107; block=7; confidence=1.00 -->
Show that every Boolean function on $\{0,1\}^n$ has a DNF of size at most $2^n$ and width at most $n$.

<a id="pdf-ffbe9c7b3306-p107-b008"></a>
<!-- pdf-source: page=107; block=8; confidence=0.99 -->
For a CNF computing $f$, exchange AND and OR to obtain a DNF computing the Boolean dual $f^\dagger$.

<a id="pdf-ffbe9c7b3306-p107-b009"></a>
<!-- pdf-source: page=107; block=9; confidence=0.99 -->
Show that monotone DNFs compute monotone functions and every monotone function has a monotone DNF representation; also show that a nonmonotone DNF may compute a monotone function.

<a id="pdf-ffbe9c7b3306-p107-b010"></a>
<!-- pdf-source: page=107; block=10; confidence=1.00 -->
For $f:\{-1,1\}^n\to\{-1,1\}$ computed by a size-$s$ DNF, the exercise continues on the next page.

<a id="pdf-ffbe9c7b3306-p108-b001"></a>
<!-- pdf-source: page=108; block=1; confidence=0.98 -->
Show that some $S\subseteq[n]$ has $|S|\le\log(s)+O(1)$ and $|\widehat f(S)|\ge\Omega(1/s)$; the hint cites Proposition 4.9 and Exercise 3.30.

<a id="pdf-ffbe9c7b3306-p108-b002"></a>
<!-- pdf-source: page=108; block=2; confidence=0.97 -->
Show that size-at-most-$s$ DNFs are weakly learnable with queries, error $1/2-\Omega(1/s)$, and time $\operatorname{poly}(n,s)$.

<a id="pdf-ffbe9c7b3306-p108-b003"></a>
<!-- pdf-source: page=108; block=3; confidence=1.00 -->
Verify Propositions 4.12 and 4.14, respectively.

<a id="pdf-ffbe9c7b3306-p108-b004"></a>
<!-- pdf-source: page=108; block=4; confidence=0.98 -->
For every input length \(n\) for \(\mathrm{Tribes}_n\), show that there is a truly unbiased function with \(\operatorname{Inf}_i[f]\le O(\log n/n)\) for every \(i\in[n]\).

<a id="pdf-ffbe9c7b3306-p108-b005"></a>
<!-- pdf-source: page=108; block=5; confidence=0.91 -->
For read-once DNFs in which all terms have width exactly \(w\), compute \(\|\widehat f\|_1\) exactly. Deduce \(\|\widehat{\mathrm{Tribes}_n}\|_1=2^{n/(2\log n)(1\pm o(1))}\) and that some width-2 DNFs have Fourier \(L_1\)-norm \(\Omega(\sqrt{3/2}^{\,n})\).

<a id="pdf-ffbe9c7b3306-p108-b006"></a>
<!-- pdf-source: page=108; block=6; confidence=0.99 -->
Give a Fourier-free proof of Corollary 4.18, conditioning on whether $i\in J$.

<a id="pdf-ffbe9c7b3306-p108-b007"></a>
<!-- pdf-source: page=108; block=7; confidence=0.99 -->
Improve the constant multiplying $\log s$ in Theorem 4.20, potentially by refining Lemma 4.19, the choice of $\delta$, and Exercise 4.17.

<a id="pdf-ffbe9c7b3306-p108-b008"></a>
<!-- pdf-source: page=108; block=8; confidence=1.00 -->
Prove Lemma 4.23.

<a id="pdf-ffbe9c7b3306-p108-b009"></a>
<!-- pdf-source: page=108; block=9; confidence=0.99 -->
Show parity $\chi_{[n]}$ has a DNF (or CNF) of size $2^{n-1}$ and prove this bound is exact by showing every term must have width $n$.

<a id="pdf-ffbe9c7b3306-p108-b010"></a>
<!-- pdf-source: page=108; block=10; confidence=0.90 -->
Construct a depth-3 circuit of size $O(n^{1/2})2^{n^{1/2}}$ for parity by splitting inputs into blocks and reducing a depth-4 construction to depth 3. Generalize to depth $d$ and size $O(n^{1-1/(d-1)})2^{n^{1/(d-1)}}$.

<a id="pdf-ffbe9c7b3306-p108-b011"></a>
<!-- pdf-source: page=108; block=11; confidence=0.99 -->
**Definition (De Morgan circuit).** A circuit over Boolean variables $x_1,\ldots,x_n$ is a directed acyclic graph whose nodes are labeled by an input variable or by $\land,\lor,\neg$. Each variable labels exactly one input node of indegree $0$; AND and OR nodes have indegree $2$, and NOT nodes have indegree $1$. A designated output node determines the circuit’s computed function, as in Definition 4.26.

<a id="pdf-ffbe9c7b3306-p109-b001"></a>
<!-- pdf-source: page=109; block=1; confidence=0.98 -->
For the circuit model under discussion, size is the number of nodes; the output node computes the circuit’s function.

<a id="pdf-ffbe9c7b3306-p109-b002"></a>
<!-- pdf-source: page=109; block=2; confidence=0.98 -->
Show that the AND, parity, and complete quadratic functions on n inputs each have De Morgan circuits of size O(n).

<a id="pdf-ffbe9c7b3306-p109-b003"></a>
<!-- pdf-source: page=109; block=3; confidence=0.98 -->
Show that any CNF formula computing \(\mathrm{Tribes}_{w,s}\) has size at least \(ws\).

<a id="pdf-ffbe9c7b3306-p109-b004"></a>
<!-- pdf-source: page=109; block=4; confidence=0.94 -->
Show there is a universal constant \(\varepsilon_0>0\) such that every \(3n/4\)-junta \(g:\{-1,1\}^n\to\{-1,1\}\) is \(\varepsilon_0\)-far from \(\mathrm{Tribes}_n\), for \(n>1\). Hint: for the coordinates \(J\) on which \(g\) depends, use that if \(J\) fails to contain all coordinates of at least a quarter of the tribes, then for random \(x\in\{-1,1\}^J\), there is constant probability that \(\operatorname{Var}[f\mid x]=\Omega(1)\).

<a id="pdf-ffbe9c7b3306-p109-b005"></a>
<!-- pdf-source: page=109; block=5; confidence=0.98 -->
Using KKL, show that every transitive-symmetric Boolean function \(f:\{-1,1\}^n\to\{-1,1\}\) with \(\operatorname{Var}[f]=\Omega(1)\) satisfies \(I[f]=\Omega(\log n)\).

<a id="pdf-ffbe9c7b3306-p109-b006"></a>
<!-- pdf-source: page=109; block=6; confidence=0.91 -->
For a Boolean function computed by a width-\(w\) CNF \(C\), study an algorithm that processes variables in a uniformly random permutation using a uniformly random seed \(r\). At each variable it aborts if both unit clauses occur, assigns the forced value if exactly one corresponding unit clause occurs, and otherwise copies the seed bit; it then simplifies \(C\) under that assignment. Write \(F_j(\pi,r)\) for the indicator that coordinate \(j\) was forced.

<a id="pdf-ffbe9c7b3306-p109-b007"></a>
<!-- pdf-source: page=109; block=7; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p109-b008"></a>
<!-- pdf-source: page=109; block=8; confidence=0.96 -->
A random monotone term of width \(w\) is the AND of \(w\) independently uniform variables from \([n]\), allowing repetitions. A random monotone DNF of width \(w\) and size \(s\) is an OR of \(s\) independent such terms.

<a id="pdf-ffbe9c7b3306-p110-b001"></a>
<!-- pdf-source: page=110; block=1; confidence=0.99 -->
Assume \(n\) is a sufficiently large perfect square, and let \(\varphi\) be a random monotone DNF of width \(\sqrt n\) and size \(2^{\sqrt n}\). For fixed \(x\), put \(u=(\sum_i x_i)/\sqrt n\).

<a id="pdf-ffbe9c7b3306-p110-b002"></a>
<!-- pdf-source: page=110; block=2; confidence=0.99 -->
**Exercise 4.18.** (a) For fixed \(x\), let \(u=(\sum_i x_i)/\sqrt n\). If \(V_j\) is the event that term \(j\) evaluates to 1 (logical False), compute \(\Pr[V_j]\) and \(\Pr[\varphi(x)=1]\), and show the latter is at least \(10^{-9}\) when \(|u|\le2\). (b) If \(U_j\) is the event that term \(j\) has exactly one 1 on \(x\), show \(\Pr[U_j\mid V_j]\ge\Omega(w2^{-w})\). (c) Conditioned on \(\varphi(x)=1\), show the events \(U_j\) are independent and their unique-1 coordinates are independent uniform among the 1s of \(x\). (d) Show sensitivity is at least \(c\sqrt n\) with probability at least \(1-10^{-10}\), for sufficiently small universal \(c>0\). (e) Show \(\Pr_x[|\sum_i x_i/\sqrt n|\le2]=\Omega(1)\). (f) Deduce a monotone Boolean function whose sensitivity is at least \(c'\sqrt n\) on a constant fraction of inputs. (g) Contrast with majority.

<a id="pdf-ffbe9c7b3306-p110-b003"></a>
<!-- pdf-source: page=110; block=3; confidence=0.92 -->
Prove the Baby Switching Lemma with constant 3 instead of 5. For a width-\(w\) DNF and a random restriction parameter \(\delta\le1/3\): (a) given a bad restriction \(R=(J\mid z)\), choose the first term that remains nonconstant and the first variable in that restricted term; show there is a unique extension \(R'\) removing that variable that does not falsify the term. (b) Show each restriction occurs as such an \(R'\) at most \(w\) times. (c) Show \(\Pr[(J\mid z)=R]=\frac{2\delta}{1-\delta}\Pr[(J\mid z)=R']\). (d) Deduce that the probability a random restriction is bad is at most \(3\delta w\).

<a id="pdf-ffbe9c7b3306-p110-b004"></a>
<!-- pdf-source: page=110; block=4; confidence=0.00 -->
**Theorem 4.30 (induction exercise).** A depth-\(d\) circuit of width at most \(w\) and with at most \(s'\) gates in layers 2 through \(d\) satisfies the displayed influence bound. The exponent on \(w\) in the scan is not legible enough to reconstruct reliably.

<a id="pdf-ffbe9c7b3306-p111-b001"></a>
<!-- pdf-source: page=111; block=1; confidence=0.95 -->
Mansour’s 1994 conjecture and its weaker form concern learning DNF via the Kushilevitz–Mansour algorithm; Jackson later obtained a related polynomial-time learning result by another method. Gopalan, Kalai, and Klivans showed the conjecture implies a corresponding agnostic-learning result. Theorems 4.24 and 4.25 are also attributed to Mansour.

<a id="pdf-ffbe9c7b3306-p111-b002"></a>
<!-- pdf-source: page=111; block=2; confidence=0.96 -->
Random restrictions trace to Subbotovskaya; Håstad’s Switching Lemma and Lemma 4.28 develop work of Furst–Saxe–Sipser, Ajtai, and Yao. Linial, Mansour, and Nisan proved Lemma 4.21, enabling the LMN theorem and consequences; an additional cryptographic application is cited. The strongest known lower bound cited here for approximate parity computation in \(AC^0\) is due independently to Impagliazzo–Matthews–Paturi and Håstad.

<a id="pdf-ffbe9c7b3306-p111-b003"></a>
<!-- pdf-source: page=111; block=3; confidence=0.95 -->
Theorem 4.20 and its generalization, Theorem 4.30, are attributed to Boppana; Linial–Mansour–Nisan had an earlier weaker \(O((\log s)^d)\) bound. Exercises 4.17 and 4.18 are attributed to Amano and Talagrand, respectively.

<a id="pdf-ffbe9c7b3306-p113-b001"></a>
<!-- pdf-source: page=113; block=1; confidence=0.99 -->
Introduces linear and higher-degree threshold functions, focusing on majority and Fourier, noise-stability, and influence analysis.

<a id="pdf-ffbe9c7b3306-p113-b002"></a>
<!-- pdf-source: page=113; block=2; confidence=0.99 -->
Section on linear threshold functions (LTFs) and polynomial threshold functions.

<a id="pdf-ffbe9c7b3306-p113-b003"></a>
<!-- pdf-source: page=113; block=3; confidence=1.00 -->
A linear threshold function has the form \(f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)\) for real coefficients \(a_0,\ldots,a_n\), with \(\operatorname{sgn}(0)=1\).

<a id="pdf-ffbe9c7b3306-p114-b001"></a>
<!-- pdf-source: page=114; block=1; confidence=1.00 -->
The coefficients in an LTF representation may be perturbed to avoid zero on every cube input and scaled by a positive constant without changing the function. They may be chosen to be integers; often they are normalized so that \(\sum_{i=1}^n a_i^2=1\).

<a id="pdf-ffbe9c7b3306-p114-b002"></a>
<!-- pdf-source: page=114; block=2; confidence=0.99 -->
**Theorem 5.1.** If \(f:\{-1,1\}^n\to\{-1,1\}\) is an LTF and \(g:\{-1,1\}^n\to\{-1,1\}\) satisfies \(\widehat g(S)=\widehat f(S)\) for every \(|S|\le 1\), then \(g=f\).

<a id="pdf-ffbe9c7b3306-p114-b003"></a>
<!-- pdf-source: page=114; block=3; confidence=0.98 -->
**Proof.** Write \(f(x)=\operatorname{sgn}(\ell(x))\), where \(\ell\) has degree at most one and is nonzero on the cube. Pointwise, \(f(x)\ell(x)=|\ell(x)|\ge g(x)\ell(x)\), with equality exactly when \(f(x)=g(x)\). Plancherel gives
\[
\sum_{|S|\le1}\widehat f(S)\widehat\ell(S)=\mathbb E[f(x)\ell(x)]\ge\mathbb E[g(x)\ell(x)]=\sum_{|S|\le1}\widehat g(S)\widehat\ell(S).
\]
The assumed coefficient equalities make the two sums equal; hence equality holds pointwise and \(f=g\).

<a id="pdf-ffbe9c7b3306-p114-b004"></a>
<!-- pdf-source: page=114; block=4; confidence=0.98 -->
The degree-zero and degree-one Fourier coefficients \(\widehat g(\varnothing),\widehat g(\{1\}),\ldots,\widehat g(\{n\})\) are called the Chow parameters of \(g\).

<a id="pdf-ffbe9c7b3306-p114-b005"></a>
<!-- pdf-source: page=114; block=5; confidence=0.97 -->
**Theorem 5.2.** For every LTF \(f:\{-1,1\}^n\to\{-1,1\}\), the Fourier weight through degree one satisfies \(W_{\le1}[f]\ge\tfrac12\).

<a id="pdf-ffbe9c7b3306-p115-b001"></a>
<!-- pdf-source: page=115; block=1; confidence=1.00 -->
## 5.1. Linear threshold functions and polynomial threshold functions

<a id="pdf-ffbe9c7b3306-p115-b002"></a>
<!-- pdf-source: page=115; block=2; confidence=0.98 -->
**Proof.** For an LTF `f = sgn(ℓ)`, Plancherel and Cauchy–Schwarz give `‖ℓ‖₁ = E|ℓ| = ⟨f,ℓ⟩ = ⟨f^{≤1},ℓ⟩ ≤ ‖f^{≤1}‖₂‖ℓ‖₂ = √W^{≤1}[f]‖ℓ‖₂`. If `ℓ` has no constant term, Khintchine–Kahane gives `‖ℓ‖₁ ≥ ‖ℓ‖₂/√2`, so `W^{≤1}[f] ≥ 1/2`; the constant-term case is deferred to Exercise 5.5.

<a id="pdf-ffbe9c7b3306-p115-b003"></a>
<!-- pdf-source: page=115; block=3; confidence=0.99 -->
Since majority has `W^{≤1}[Maj_n] = W_1[Maj_n] ≥ 2/π`, the text proposes the following open extremal conjecture.

<a id="pdf-ffbe9c7b3306-p115-b004"></a>
<!-- pdf-source: page=115; block=4; confidence=1.00 -->
**Conjecture 5.3.** Every `f : {−1,1}ⁿ → {−1,1}` that is an LTF satisfies `W^{≤1}[f] ≥ 2/π`.

<a id="pdf-ffbe9c7b3306-p115-b005"></a>
<!-- pdf-source: page=115; block=5; confidence=0.99 -->
**Definition 5.4.** A function `f : {−1,1}ⁿ → {−1,1}` is a polynomial threshold function (PTF) of degree at most `k` if `f(x) = sgn(p(x))` for a real polynomial `p` of degree at most `k`.

<a id="pdf-ffbe9c7b3306-p115-b006"></a>
<!-- pdf-source: page=115; block=6; confidence=0.99 -->
**Example 5.5.** The 4-bit equality function, equal to `1` exactly when all four bits agree, is a degree-2 PTF via `sgn(−3 + ∑_{1≤i<j≤4} x_i x_j)`.

<a id="pdf-ffbe9c7b3306-p115-b007"></a>
<!-- pdf-source: page=115; block=7; confidence=0.98 -->
Every Boolean function is a PTF of degree at most `n`, by taking the sign of its Fourier expansion. Low-degree PTFs are useful in learning; low noise sensitivity also implies approximation by one:

<a id="pdf-ffbe9c7b3306-p115-b008"></a>
<!-- pdf-source: page=115; block=8; confidence=0.88 -->
**Proposition 5.6.** For `f : {−1,1}ⁿ → {−1,1}` and `δ ∈ (0,1/2]`, `f` is `(3 NS_δ[f])`-close to a PTF of degree `1/δ`.

<a id="pdf-ffbe9c7b3306-p115-b009"></a>
<!-- pdf-source: page=115; block=9; confidence=0.96 -->
The page begins describing a PTF `f(x) = sgn(∑_{i=1}^s a_i x^{T_i})` as a depth-2 threshold-of-parities circuit; the explanation continues on page 116.

<a id="pdf-ffbe9c7b3306-p116-b001"></a>
<!-- pdf-source: page=116; block=1; confidence=0.99 -->
In the threshold-of-parities interpretation, circuit size corresponds to the number of terms in the PTF representation.

<a id="pdf-ffbe9c7b3306-p116-b002"></a>
<!-- pdf-source: page=116; block=2; confidence=1.00 -->
**Definition 5.7.** A PTF representation `f(x)=sgn(p(x))` has sparsity at most `s` when the multilinear polynomial `p` has at most `s` terms. The representation in Example 5.5 has sparsity 7.

<a id="pdf-ffbe9c7b3306-p116-b003"></a>
<!-- pdf-source: page=116; block=3; confidence=1.00 -->
**Theorem 5.8.** If `f : {−1,1}ⁿ → {−1,1}` is a PTF of degree at most `k`, and `g : {−1,1}ⁿ → {−1,1}` satisfies `ĝ(S)=f̂(S)` for every `|S|≤k`, then `g=f`.

<a id="pdf-ffbe9c7b3306-p116-b004"></a>
<!-- pdf-source: page=116; block=4; confidence=1.00 -->
**Theorem 5.9.** Every degree-`k` PTF `f : {−1,1}ⁿ → {−1,1}` satisfies `W^{≤k}[f] ≥ e^{−2k}`.

<a id="pdf-ffbe9c7b3306-p116-b005"></a>
<!-- pdf-source: page=116; block=5; confidence=0.99 -->
**Proof.** Writing `f=sgn(p)` with `deg(p)≤k`, we have `‖p‖₁=E|p|=⟨f,p⟩=⟨f^{≤k},p⟩≤‖f^{≤k}‖₂‖p‖₂=√W^{≤k}[f]‖p‖₂`. The result follows from the stated hypercontractive bound `‖p‖₂≤e^k‖p‖₁` for degree-`k` polynomials, proved later as Theorem 9.22. The text notes the bound cannot be improved past `2^{1−k}` (Exercise 5.11).

<a id="pdf-ffbe9c7b3306-p116-b006"></a>
<!-- pdf-source: page=116; block=6; confidence=0.99 -->
**Theorem 5.10.** Let `F ⊆ 2^[n]`, and suppose `f(x)=sgn(p(x))` where `p(x)=∑_{S∈F} p̂(S)x^S`. Then `∑_{S∈F}|f̂(S)| ≥ 1`.

<a id="pdf-ffbe9c7b3306-p116-b007"></a>
<!-- pdf-source: page=116; block=7; confidence=0.95 -->
**Proof.** Set `g(x)=∑_{S∈F} f̂(S)x^S`. Using `‖p̂‖_∞≤‖p‖₁`, the sign relation, and Fourier expansion, `‖p̂‖_∞ ≤ ‖p‖₁ = E[f(x)p(x)] = ∑_{S∈F} ĝ(S)p̂(S) ≤ ‖ĝ‖₁‖p̂‖_∞`. Hence `‖ĝ‖₁=∑_{S∈F}|f̂(S)|≥1`.

<a id="pdf-ffbe9c7b3306-p116-b008"></a>
<!-- pdf-source: page=116; block=8; confidence=0.98 -->
Theorem 5.10 is applied to lower-bound the sparsity of threshold-of-parities circuits computing the inner product mod 2 function.

<a id="pdf-ffbe9c7b3306-p117-b001"></a>
<!-- pdf-source: page=117; block=1; confidence=0.95 -->
**Corollary 5.11.** Every PTF representation of `IP_{2n} : {−1,1}^{2n} → {−1,1}` has sparsity at least `2^n`.

<a id="pdf-ffbe9c7b3306-p117-b002"></a>
<!-- pdf-source: page=117; block=2; confidence=0.99 -->
**Proof.** Theorem 5.10 applies because `|IP̂_{2n}(S)|=2^{−n}` for every `S⊆[2n]` (Exercise 1.1), forcing at least `2^n` terms.

<a id="pdf-ffbe9c7b3306-p117-b003"></a>
<!-- pdf-source: page=117; block=3; confidence=0.99 -->
A small Fourier `1`-norm yields sparse PTF representations; the stronger claim below gives uniform additive approximation by a sparse polynomial.

<a id="pdf-ffbe9c7b3306-p117-b004"></a>
<!-- pdf-source: page=117; block=4; confidence=0.96 -->
**Theorem 5.12.** Let `f : {−1,1}ⁿ → ℝ` be nonzero, `δ>0`, and let integer `s ≥ 4n‖f̂‖₁²/δ²`. There exists a multilinear polynomial `q` with at most `s` terms such that `‖f−q‖∞<δ`.

<a id="pdf-ffbe9c7b3306-p117-b005"></a>
<!-- pdf-source: page=117; block=5; confidence=0.91 -->
**Proof.** Sample `T₁,…,T_s` independently with `Pr[T_i=T]=|f̂(T)|/‖f̂‖₁`, and set `p(x)=∑_{i=1}^s sgn(f̂(T_i))x^{T_i}`. For fixed `x`, each summand is ±1 with expectation `f(x)/‖f̂‖₁`. A Chernoff bound gives `Pr[|p(x)/s−f(x)/‖f̂‖₁|≥ε]≤2exp(−ε²s/2)`. With `ε=δ/‖f̂‖₁` and the assumed lower bound on `s`, this is at most `2exp(−2n)<2^{−n}`. A union bound over all `2^n` inputs yields a choice of samples for which `q=(‖f̂‖₁/s)p` has at most `s` terms and `‖f−q‖∞<δ`.

<a id="pdf-ffbe9c7b3306-p117-b006"></a>
<!-- pdf-source: page=117; block=6; confidence=0.94 -->
**Corollary 5.13.** Every Boolean `f : {−1,1}ⁿ → {−1,1}` has a PTF representation of sparsity at most `⌈4n‖f̂‖₁²⌉`; equivalently, it is representable as a majority of that many parities or negated parities.

<a id="pdf-ffbe9c7b3306-p117-b007"></a>
<!-- pdf-source: page=117; block=7; confidence=0.96 -->
**Proof.** Apply Theorem 5.12 with `δ=1`. Since the resulting `q` is uniformly within `1` of the Boolean-valued `f`, `f(x)=sgn(q(x))`; the sampled summands correspond to parities or their negations.

<a id="pdf-ffbe9c7b3306-p118-b001"></a>
<!-- pdf-source: page=118; block=1; confidence=1.00 -->
## 5. Majority and threshold functions

<a id="pdf-ffbe9c7b3306-p118-b002"></a>
<!-- pdf-source: page=118; block=2; confidence=0.99 -->
Small DNFs have sparse PTF representations (Exercise 5.13); majority has a sparse LTF but exponentially large Fourier 1-norm (Exercise 5.26).

<a id="pdf-ffbe9c7b3306-p118-b003"></a>
<!-- pdf-source: page=118; block=3; confidence=1.00 -->
## 5.2. Majority, and the Central Limit Theorem

<a id="pdf-ffbe9c7b3306-p118-b004"></a>
<!-- pdf-source: page=118; block=4; confidence=0.99 -->
The section uses the central limit theorem (CLT) to estimate majority’s total influence and noise stability, with methods that extend to other linear threshold functions.

<a id="pdf-ffbe9c7b3306-p118-b005"></a>
<!-- pdf-source: page=118; block=5; confidence=1.00 -->
**Notation 5.14.** \(Z\sim N(0,1)\) denotes a standard Gaussian, with \(\phi(z)=\frac1{\sqrt{2\pi}}e^{-z^2/2}\), \(\Phi(t)=\int_{-\infty}^t\phi(z)\,dz\), and \(\overline\Phi(t)=\Phi(-t)=\int_t^\infty\phi(z)\,dz\). More generally, \(Z\sim N(\mu,\Sigma)\) has mean \(\mu\) and covariance \(\Sigma\).

<a id="pdf-ffbe9c7b3306-p118-b006"></a>
<!-- pdf-source: page=118; block=6; confidence=0.99 -->
The text introduces Berry–Esseen as a quantitative CLT and notes a multidimensional version (Exercise 5.33).

<a id="pdf-ffbe9c7b3306-p118-b007"></a>
<!-- pdf-source: page=118; block=7; confidence=1.00 -->
\(I[\mathrm{Maj}_n]=\sum_{i=1}^n\widehat{\mathrm{Maj}_n}(i)=\mathbb E_x[\mathrm{Maj}_n(x)\sum_i x_i]=\mathbb E_x[|\sum_i x_i|]\).

<a id="pdf-ffbe9c7b3306-p119-b001"></a>
<!-- pdf-source: page=119; block=1; confidence=0.88 -->
**Equation (5.3).** With $S=\frac1{\sqrt n}\sum_{i=1}^n x_i$, one has $I[\mathrm{Maj}_n]=\sqrt n\,\mathbb E_x[|S|]$. The summands have mean zero and total variance $1$, so the CLT gives $S$ an asymptotic standard Gaussian distribution. Thus **equation (5.4)** gives $\mathbb E|S|\sim\mathbb E|Z|=\int_{-\infty}^{\infty}|z|\frac{e^{-z^2/2}}{\sqrt{2\pi}}\,dz=\sqrt{2/\pi}$, and consequently $I[\mathrm{Maj}_n]\sim\sqrt{2n/\pi}$.

<a id="pdf-ffbe9c7b3306-p119-b002"></a>
<!-- pdf-source: page=119; block=2; confidence=0.99 -->
**Berry–Esseen Theorem.** Let \(X_1,\ldots,X_n\) be independent, mean-zero random variables with variances \(\sigma_i^2\), where \(\sum_i\sigma_i^2=1\). For \(S=\sum_iX_i\) and \(Z\sim N(0,1)\), \(|\Pr[S\le u]-\Pr[Z\le u]|\le c\gamma\), where \(\gamma=\sum_i\mathbb E[|X_i|^3]\) and \(c\) is universal.

<a id="pdf-ffbe9c7b3306-p119-b003"></a>
<!-- pdf-source: page=119; block=3; confidence=0.96 -->
**Remark 5.15.** If $|X_i|\le\varepsilon$ almost surely for every $i$, then $\gamma=\sum_i\mathbb E|X_i|^3\le\varepsilon\sum_i\mathbb E|X_i|^2=\varepsilon\sum_i\sigma_i^2=\varepsilon$.

<a id="pdf-ffbe9c7b3306-p119-b004"></a>
<!-- pdf-source: page=119; block=4; confidence=0.98 -->
The common application is $S=\sum_i a_ix_i$ for uniform independent signs $x\in\{-1,1\}^n$, with $\sum_i a_i^2=1$; small coefficients make the sum close in distribution to a standard Gaussian.

<a id="pdf-ffbe9c7b3306-p119-b005"></a>
<!-- pdf-source: page=119; block=5; confidence=0.94 -->
**Theorem 5.16.** If $a_1,\ldots,a_n\in\mathbb R$ satisfy $\sum_i a_i^2=1$ and $|a_i|\le\varepsilon$ for all $i$, then $\left|\mathbb E_{x\sim\{-1,1\}^n}\left[\left|\sum_i a_ix_i\right|\right]-\sqrt{2/\pi}\right|\le C\varepsilon$, for a universal constant $C$.

<a id="pdf-ffbe9c7b3306-p120-b001"></a>
<!-- pdf-source: page=120; block=1; confidence=0.98 -->
Theorem 5.16 yields $I[\mathrm{Maj}_n]=\sqrt{2n/\pi}+O(1)$; Exercise 2.22 gives a sharper error estimate.

<a id="pdf-ffbe9c7b3306-p120-b002"></a>
<!-- pdf-source: page=120; block=2; confidence=0.99 -->
**Equation (5.5).** $\displaystyle\lim_{n\to\infty}\operatorname{Stab}_\rho[\mathrm{Maj}_n]=\frac{2}{\pi}\arcsin\rho=1-\frac{2}{\pi}\arccos\rho$.

<a id="pdf-ffbe9c7b3306-p120-b003"></a>
<!-- pdf-source: page=120; block=3; confidence=0.99 -->
In (5.7), \(\widetilde S=\sum_{i=1}^n(x_i/\sqrt n,y_i/\sqrt n)\in\mathbb R^2\). By the multidimensional CLT it converges to \(\widetilde Z\sim N((0,0),\begin{bmatrix}1&\rho\\\rho&1\end{bmatrix})\). Thus majority's limiting noise stability is \(4\Pr[\widetilde Z\in Q_{--}]-1\), with \(\Pr[\widetilde Z\in Q_{--}]=\frac12-\frac{\arccos\rho}{2\pi}\).

<a id="pdf-ffbe9c7b3306-p120-b004"></a>
<!-- pdf-source: page=120; block=4; confidence=0.96 -->
**Sheppard’s Formula.** For standard Gaussian random variables $z_1,z_2$ with correlation $\mathbb E[z_1z_2]=\rho\in[-1,1]$, $\Pr[z_1\le0,\ z_2\le0]=\frac12-\frac{\arccos\rho}{2\pi}$.

<a id="pdf-ffbe9c7b3306-p121-b001"></a>
<!-- pdf-source: page=121; block=1; confidence=0.98 -->
The Gaussian limit argument extends from majority to unbiased linear threshold functions; its error depends on the largest coefficient.

<a id="pdf-ffbe9c7b3306-p121-b002"></a>
<!-- pdf-source: page=121; block=2; confidence=0.97 -->
**Theorem 5.17.** If an unbiased LTF \(f(x)=\operatorname{sgn}(\sum_i a_ix_i)\) has \(\sum_i a_i^2=1\) and \(|a_i|\le\varepsilon\), then for \(\rho\in(-1,1)\), \(\left|\operatorname{Stab}_\rho[f]-\frac2\pi\arcsin\rho\right|\le O\bigl(\frac{\varepsilon}{\sqrt{1-\rho^2}}\bigr)\).

<a id="pdf-ffbe9c7b3306-p121-b003"></a>
<!-- pdf-source: page=121; block=3; confidence=0.98 -->
**Theorem 5.18.** For \(\rho\in[0,1)\), \(\operatorname{Stab}_\rho[\mathrm{Maj}_n]\) decreases with \(n\), and \[\frac2\pi\arcsin\rho\le\operatorname{Stab}_\rho[\mathrm{Maj}_n]\le\frac2\pi\arcsin\rho+O\left(\frac1{\sqrt{1-\rho^2}\sqrt n}\right).\]

<a id="pdf-ffbe9c7b3306-p121-b004"></a>
<!-- pdf-source: page=121; block=4; confidence=0.99 -->
**Majority Is Stablest Theorem.** Fix $\rho\in(0,1)$. If $f:\{-1,1\}^n\to[-1,1]$, $\mathbb E[f]=0$, and $\operatorname{MaxInf}[f]\leq\tau$, then $\operatorname{Stab}_\rho[f]\leq \frac{2}{\pi}\arcsin\rho+o_\tau(1)=1-\frac{2}{\pi}\arccos\rho+o_\tau(1)$.

<a id="pdf-ffbe9c7b3306-p121-b005"></a>
<!-- pdf-source: page=121; block=5; confidence=0.99 -->
## 5.3. The Fourier coefficients of Majority

<a id="pdf-ffbe9c7b3306-p121-b006"></a>
<!-- pdf-source: page=121; block=6; confidence=0.99 -->
The section studies the Fourier spectrum of $\operatorname{Maj}_n$: symmetry makes coefficients depend only on set size, and oddness forces coefficients on even-sized sets to vanish.

<a id="pdf-ffbe9c7b3306-p122-b001"></a>
<!-- pdf-source: page=122; block=1; confidence=0.91 -->
For odd $k$, symmetry gives $\widehat{\operatorname{Maj}_n}(S)^2=W_k[\operatorname{Maj}_n]/\binom nk$ when $|S|=k$. The limiting stability expansion $\lim_{n\to\infty}\operatorname{Stab}_\rho[\operatorname{Maj}_n]=\frac2\pi\arcsin\rho$ suggests, and Theorem 5.22 proves, that $W_k[\operatorname{Maj}_n]\to[\rho^k](\frac2\pi\arcsin\rho)$, equal to $\frac{4}{\pi k2^k}\binom{k-1}{(k-1)/2}$ for odd $k$ and zero for even $k$ (5.10). The expansion uses the power series for $\arcsin z$ on $|z|\leq1$.

<a id="pdf-ffbe9c7b3306-p122-b002"></a>
<!-- pdf-source: page=122; block=2; confidence=0.98 -->
For each fixed odd \(k\), \(\lim_{n\to\infty}W^k[\mathrm{Maj}_n]=[\rho^k](\frac2\pi\arcsin\rho)=\frac4{\pi k2^k}\binom{k-1}{(k-1)/2}\); for even \(k\) the limit is 0. As \(k\to\infty\), \(W^k[\mathrm{Maj}]\sim(2/\pi)^{3/2}k^{-3/2}\) for odd \(k\), and \(W^{>k}[\mathrm{Maj}]\sim(2/\pi)^{3/2}k^{-1/2}\).

<a id="pdf-ffbe9c7b3306-p122-b003"></a>
<!-- pdf-source: page=122; block=3; confidence=0.90 -->
**Theorem 5.19.** If $|S|$ is even, then $\widehat{\operatorname{Maj}_n}(S)=0$. If $|S|=k$ is odd, then
\[\widehat{\operatorname{Maj}_n}(S)=(-1)^{(k-1)/2}\frac{\binom{(n-1)/2}{(k-1)/2}}{\binom{n-1}{k-1}}\cdot\frac{2}{2^n}\binom{n-1}{(n-1)/2}.\]

<a id="pdf-ffbe9c7b3306-p122-b004"></a>
<!-- pdf-source: page=122; block=4; confidence=0.90 -->
**Proof.** The even-size case follows from oddness of majority. For odd $k$, the proof reduces the coefficient to that of the majority derivative, the indicator $\operatorname{Half}_{n-1}$ of strings with equally many $-1$ and $+1$ coordinates; the calculation continues on the next page.

<a id="pdf-ffbe9c7b3306-p123-b001"></a>
<!-- pdf-source: page=123; block=1; confidence=0.94 -->
By the derivative formula and symmetry, $\widehat{\operatorname{Maj}_n}(S)=\widehat{\operatorname{Half}_{n-1}}(T)$ for $T\subseteq[n-1]$ with $|T|=k-1$. Writing $n-1=2m$ and $k-1=2j$, it remains to show
\[\widehat{\operatorname{Half}_{2m}}([2j])=(-1)^j\frac{\binom mj}{\binom{2m}{2j}}\cdot\frac{1}{2^{2m}}\binom{2m}{m}.\tag{5.12}\]

<a id="pdf-ffbe9c7b3306-p123-b002"></a>
<!-- pdf-source: page=123; block=2; confidence=0.93 -->
At the all-ones input, the probabilistic definition gives $T_\rho\operatorname{Half}_{2m}(1,\ldots,1)=\Pr[x\text{ has }m\text{ ones and }m\text{ minus ones}]=\binom{2m}{m}2^{-2m}(1-\rho^2)^m$ (5.13). By the Fourier formula and symmetry, the same value is $\sum_{i=0}^{2m}\binom{2m}{i}\widehat{\operatorname{Half}_{2m}}([i])\rho^i$ (5.14). Equating coefficients of these polynomials gives (5.12), since $[\rho^{2j}](1-\rho^2)^m=(-1)^j\binom mj$.

<a id="pdf-ffbe9c7b3306-p123-b003"></a>
<!-- pdf-source: page=123; block=3; confidence=0.97 -->
The next two corollaries are assigned as exercises.

<a id="pdf-ffbe9c7b3306-p123-b004"></a>
<!-- pdf-source: page=123; block=4; confidence=0.98 -->
**Corollary 5.20.** \(\widehat{\mathrm{Maj}_n}(S)=(-1)^{(n-1)/2}\widehat{\mathrm{Maj}_n}(T)\) whenever \(|S|+|T|=n+1\). Hence \(W^{n-k+1}[\mathrm{Maj}_n]=\frac{k}{n-k+1}W^k[\mathrm{Maj}_n]\).

<a id="pdf-ffbe9c7b3306-p123-b005"></a>
<!-- pdf-source: page=123; block=5; confidence=0.93 -->
**Corollary 5.21.** For odd $k$, $W_k[\operatorname{Maj}_n]$ strictly decreases with odd $n\geq k$.

<a id="pdf-ffbe9c7b3306-p123-b006"></a>
<!-- pdf-source: page=123; block=6; confidence=0.97 -->
**Theorem 5.22.** For each fixed odd $k$, as odd $n\geq k$ tends to infinity, $W_k[\operatorname{Maj}_n]\searrow [\rho^k](\frac2\pi\arcsin\rho)=\frac{4}{\pi k2^k}\binom{k-1}{(k-1)/2}$. Moreover, for $k<n/2$,
\[[\rho^k](\tfrac2\pi\arcsin\rho)\leq W_k[\operatorname{Maj}_n]\leq(1+2k/n)[\rho^k](\tfrac2\pi\arcsin\rho).\tag{5.15}\]
For $k>n/2$, use Corollary 5.20.

<a id="pdf-ffbe9c7b3306-p124-b001"></a>
<!-- pdf-source: page=124; block=1; confidence=0.98 -->
The proof uses Corollary 5.21 to reduce to (5.15). Applying Theorem 5.19 and simplifying the binomial coefficients gives a ratio tending to \(\frac{n}{\sqrt{n-k}\sqrt{n-1}}=(1-\frac{k+1}{n}+\frac{k}{n^2})^{-1/2}\), which is at most \(1+2k/n\) for \(1\le k\le n/2\).

<a id="pdf-ffbe9c7b3306-p124-b002"></a>
<!-- pdf-source: page=124; block=2; confidence=0.96 -->
**Corollary 5.23.** For odd \(k\) and \(n=n(k)\ge2k^2\), \(W^k[\mathrm{Maj}_n]=(2/\pi)^{3/2}k^{-3/2}(1+O(1/k))\) and \(W^{>k}[\mathrm{Maj}_n]=(2/\pi)^{3/2}k^{-1/2}(1+O(1/k))\). Hence the spectrum is \(\epsilon\)-concentrated up to degree \(\frac8{\pi^3\epsilon^2}+O_\epsilon(1)\).

<a id="pdf-ffbe9c7b3306-p124-b003"></a>
<!-- pdf-source: page=124; block=3; confidence=1.00 -->
## 5.4. Degree-1 weight

<a id="pdf-ffbe9c7b3306-p124-b004"></a>
<!-- pdf-source: page=124; block=4; confidence=0.91 -->
For Boolean $f$, $W_1[f]=\sum_{i=1}^n\widehat f(i)^2$. From $\mathrm{Stab}_\rho[f]=\sum_{k\ge0}\rho^kW_k[f]$, one has $W_1[f]=\left.\frac{d}{d\rho}\mathrm{Stab}_\rho[f]\right|_{\rho=0}$. Thus for small $\rho$, $\mathrm{Stab}_\rho[f]=\mathbb E[f]^2+W_1[f]\rho\pm O(\rho^2)$, equivalently $\mathrm{Cov}_{(x,y)\ \rho\text{-correlated}}[f(x),f(y)]=W_1[f]\rho\pm O(\rho^2)$.

<a id="pdf-ffbe9c7b3306-p125-b001"></a>
<!-- pdf-source: page=125; block=1; confidence=0.88 -->
For Boolean-valued $f$, $W_1[f]$ measures the first-order increase in agreement under small positive correlation. For an indicator, it is also related to noisy boundary size near the maximal noise rate. Subcubes and Hamming balls provide examples with small boundary.

<a id="pdf-ffbe9c7b3306-p125-b002"></a>
<!-- pdf-source: page=125; block=2; confidence=0.98 -->
**Proposition 5.24.** If $f$ indicates a codimension-$k$ subcube, $k\ge1$, then $\mathbb E[f]=2^{-k}$ and $W_1[f]=k2^{-2k}$.

<a id="pdf-ffbe9c7b3306-p125-b003"></a>
<!-- pdf-source: page=125; block=3; confidence=0.99 -->
**Proposition 5.25.** For fixed \(t\in\mathbb R\), let \(f_n(x)=1\) iff \(\sum_{i=1}^n x_i/\sqrt n>t\). Then \(\lim_{n\to\infty}\mathbb E[f_n]=\overline\Phi(t)\) and \(\lim_{n\to\infty}W^1[f_n]=\phi(t)^2\).

<a id="pdf-ffbe9c7b3306-p125-b004"></a>
<!-- pdf-source: page=125; block=4; confidence=0.89 -->
**Definition 5.26.** The Gaussian isoperimetric function $U:[0,1]\to[0,1/\sqrt{2\pi}]$ is $U=\phi\circ\Phi^{-1}$; it is symmetric about $1/2$. For $\alpha=\lim_n\mathbb E[f_n]$, Proposition 5.25 identifies the limiting degree-1 weight with $U(\alpha)^2$.

<a id="pdf-ffbe9c7b3306-p125-b005"></a>
<!-- pdf-source: page=125; block=5; confidence=0.99 -->
**Proposition 5.27.** As $\alpha\to0^+$, $U(\alpha)\sim\alpha\sqrt{2\ln(1/\alpha)}$.

<a id="pdf-ffbe9c7b3306-p125-b006"></a>
<!-- pdf-source: page=125; block=6; confidence=0.98 -->
**Proof.** Write $\alpha=\Phi(t)$ with $t\to\infty$. Using $\Phi(t)\sim\phi(t)/t$, obtain $\alpha\sim (\sqrt{2\pi}t)^{-1}e^{-t^2/2}$, hence $t\sim\sqrt{2\ln(1/\alpha)}$. Also $\phi(t)\sim\Phi(t)t$, so $U(\alpha)=\phi(t)\sim\alpha\sqrt{2\ln(1/\alpha)}$.

<a id="pdf-ffbe9c7b3306-p125-b007"></a>
<!-- pdf-source: page=125; block=7; confidence=0.95 -->
As the volume $\alpha=\mathbb E[f]$ tends to zero, subcubes satisfy $W_1[f]=\alpha^2\log(1/\alpha)$; Hamming balls satisfy $W_1[f_n]\to U(\alpha)^2\sim2\alpha^2\ln(1/\alpha)$.

<a id="pdf-ffbe9c7b3306-p126-b001"></a>
<!-- pdf-source: page=126; block=1; confidence=0.95 -->
These examples have degree-1 weight of order $\alpha^2\log(1/\alpha)$, much smaller than the general bound $W_1[f]\le\mathrm{Var}[f]=\alpha(1-\alpha)\sim\alpha$ for an indicator of mean $\alpha$.

<a id="pdf-ffbe9c7b3306-p126-b002"></a>
<!-- pdf-source: page=126; block=2; confidence=0.99 -->
**Level-1 Inequality.** If $f:\{-1,1\}^n\to\{0,1\}$ has mean $\alpha\le1/2$, then $W_1[f]\le O(\alpha^2\log(1/\alpha))$. For $\alpha\ge1/2$, apply the statement to $1-f$.

<a id="pdf-ffbe9c7b3306-p126-b003"></a>
<!-- pdf-source: page=126; block=3; confidence=0.95 -->
The sharp bound is $W_1[f]\le2\alpha^2\ln(1/\alpha)$; Hamming balls asymptotically maximize this weight at small volume. The inequality also extends to $f:\{-1,1\}^n\to[-1,1]$ with $\alpha=\mathbb E[|f|]$. The result is also known as Chang’s Inequality and generalizes to level-$k$ inequalities later.

<a id="pdf-ffbe9c7b3306-p126-b004"></a>
<!-- pdf-source: page=126; block=4; confidence=0.78 -->
Without a volume constraint, dictators and their negations maximize $W_1$ among unbiased Boolean functions, with weight $1$. Majority has $W_1[\mathrm{Maj}_n]\to2/\pi$. Motivated by excluding dominant coordinates, the text introduces a second theorem extending Proposition 2.58, which bounds $W_1[f]$ by $2/\pi+o_n(1)$ when all influences are equal.

<a id="pdf-ffbe9c7b3306-p127-b001"></a>
<!-- pdf-source: page=127; block=1; confidence=1.00 -->
## 5.4. Degree-1 weight

<a id="pdf-ffbe9c7b3306-p127-b002"></a>
<!-- pdf-source: page=127; block=2; confidence=0.98 -->
**The \(2/\pi\) Theorem.** If \(|\widehat f(i)|\le\varepsilon\) for all \(i\in[n]\), then \(W^1[f]\le2/\pi+O(\varepsilon)\). If \(W^1[f]\ge2/\pi-\varepsilon\), then \(f\) is \(O(\sqrt\varepsilon)\)-close to the LTF \(\operatorname{sgn}(f^{=1})\).

<a id="pdf-ffbe9c7b3306-p127-b003"></a>
<!-- pdf-source: page=127; block=3; confidence=0.98 -->
Functions satisfying $|\widehat f(i)|\le\varepsilon$ for every coordinate $i$ are called $(\varepsilon,1)$-regular.

<a id="pdf-ffbe9c7b3306-p127-b004"></a>
<!-- pdf-source: page=127; block=4; confidence=0.95 -->
For Boolean \(f\) with \(\alpha=\mathbb E[f]\), \(W^1[f]=\mathbb E[f(x)L(x)]\), where \(L(x)=\sum_i\widehat f(i)x_i\). For a threshold \(t\) chosen so \(\Pr[L(x)\ge t]\approx\alpha\), \(W^1[f]\le\mathbb E[1_{\{L(x)\ge t\}}L(x)]\). For unbiased \(f\), the Gaussian approximation with variance \(W^1[f]\) gives \(W^1[f]\le\sqrt{W^1[f]}/\sqrt{2\pi}\), hence the \(2/\pi\) bound after converting to \(\{-1,1\}\)-valued functions.

<a id="pdf-ffbe9c7b3306-p128-b001"></a>
<!-- pdf-source: page=128; block=1; confidence=0.99 -->
**Lemma 5.31.** For $L(x)=\sum_i a_ix_i$ with $\sum_i a_i^2=1$, and every $s\ge1$,
\[
\mathbb E[\mathbf 1_{\{|L(x)|>s\}}|L(x)|]\le(2s+2)e^{-s^2/2}.
\]

<a id="pdf-ffbe9c7b3306-p128-b002"></a>
<!-- pdf-source: page=128; block=2; confidence=0.98 -->
**Proof.** Tail integration and Hoeffding's inequality give
\[
\mathbb E[\mathbf 1_{\{|L|>s\}}|L|]=s\Pr(|L|>s)+\int_s^\infty\Pr(|L|>u)\,du
\le 2s e^{-s^2/2}+\int_s^\infty 2e^{-u^2/2}\,du.
\]
For $s\ge1$, bound the integral by $\int_s^\infty 2u e^{-u^2/2}\,du=2e^{-s^2/2}$, proving the claim.

<a id="pdf-ffbe9c7b3306-p128-b003"></a>
<!-- pdf-source: page=128; block=3; confidence=0.99 -->
The proofs use the normalized linear form $L(x)=f^{=1}(x)/\sigma=\sum_i(\widehat f(i)/\sigma)x_i$, where $\sigma=\sqrt{W_1[f]}$.

<a id="pdf-ffbe9c7b3306-p128-b004"></a>
<!-- pdf-source: page=128; block=4; confidence=0.95 -->
**Proof.** Let $f:\{-1,1\}^n\to[-1,1]$, $\alpha=\mathbb E|f|$, and assume $\sigma=\sqrt{W_1[f]}>0$. Then $\langle f,L\rangle=\sigma$. For any $s\ge1$, split this expectation according to $|L|\le s$ and $|L|>s$. The first part is at most $\alpha s$; Lemma 5.31 bounds the second by $(2s+2)e^{-s^2/2}\le4s e^{-s^2/2}$. Thus
\[
\sigma\le\alpha s+4s e^{-s^2/2}.
\]
Choosing $s=(\sqrt2+o_\alpha(1))\sqrt{\ln(1/\alpha)}$ yields $\sigma\le(\sqrt2+o(1))\alpha\sqrt{\ln(1/\alpha)}$. Squaring proves $W_1[f]\le(2+o_\alpha(1))\alpha^2\ln(1/\alpha)$.

<a id="pdf-ffbe9c7b3306-p128-b005"></a>
<!-- pdf-source: page=128; block=5; confidence=0.92 -->
**Proof.** Assume $\sigma\ge1/\sqrt2$ (otherwise the upper-bound claim is immediate, and for the stability claim this follows by taking $\varepsilon$ sufficiently small). Set $L=f^{=1}/\sigma$, so $\|L\|_2=1$ and $|\widehat L(i)|\le2\varepsilon$. By Theorem 5.16,
\[
\sigma=\langle f,L\rangle\le\mathbb E|L|\le\sqrt{2/\pi}+C\varepsilon.\tag{5.19}
\]
Squaring yields (5.16), and the same upper bound applies to $f$ valued in $[-1,1]$. For the stability part, assume also $W_1[f]\ge2/\pi-\varepsilon$, hence $\sigma\ge\sqrt{2/\pi}-2\varepsilon$.

<a id="pdf-ffbe9c7b3306-p129-b001"></a>
<!-- pdf-source: page=129; block=1; confidence=0.88 -->
The bounds on $\sigma$ and (5.19) imply
\[
(C+2)\varepsilon\ge\mathbb E|L|-\langle f,L\rangle
=\mathbb E[(\operatorname{sgn}(L(x))-f(x))L(x)].\tag{5.20}
\]
Berry–Esseen bounds $\Pr(|L|\le K\sqrt\varepsilon)$ by at most $2K\sqrt\varepsilon/\sqrt{2\pi}+1.12\varepsilon$. Consequently, if $\Pr[f\ne\operatorname{sgn}(L)]\ge3K\sqrt\varepsilon$, then the disagreement outside this small-$|L|$ region has probability at least $K\sqrt\varepsilon$, forcing the right side of (5.20) to be at least $2K^2\varepsilon$. Taking $K=\sqrt{C+2}$ contradicts (5.20), so the disagreement probability is at most $3\sqrt{C+2}\sqrt\varepsilon$.

<a id="pdf-ffbe9c7b3306-p129-b002"></a>
<!-- pdf-source: page=129; block=2; confidence=0.95 -->
An interpolation between the Level-1 and $2/\pi$ results is deferred to Exercise 5.44. The section then applies the Level-1 inequality.

<a id="pdf-ffbe9c7b3306-p129-b003"></a>
<!-- pdf-source: page=129; block=3; confidence=0.96 -->
**Corollary 5.32.** If $f:\{-1,1\}^n\to\{-1,1\}$ and $|\mathbb E f|\ge1-\delta\ge0$, then
\[
W_1[f]\le4\delta^2\log(2/\delta).
\]

<a id="pdf-ffbe9c7b3306-p129-b004"></a>
<!-- pdf-source: page=129; block=4; confidence=0.96 -->
Assuming the FKN theorem gives $C\delta$-closeness to a dictator or its negation, the next result sharpens the closeness estimate.

<a id="pdf-ffbe9c7b3306-p129-b005"></a>
<!-- pdf-source: page=129; block=5; confidence=0.99 -->
**Theorem 5.33.** If the FKN theorem holds with closeness bound $C\delta$, for a universal $C\ge1$, then it holds with bound $\delta/4+\eta$, where
\[
\eta=16C^2\delta^2\max(\log(1/(C\delta)),1).
\]

<a id="pdf-ffbe9c7b3306-p129-b006"></a>
<!-- pdf-source: page=129; block=6; confidence=0.95 -->
**Proof.** Suppose $W_1[f]\ge1-\delta\ge0$. By the assumed FKN bound, $f$ is $C\delta$-close to some $\pm x_i$; take $i=n$. Then $|\widehat f(n)|\ge1-2C\delta$. It suffices to prove $|\widehat f(n)|\ge1-\delta/2-2\eta$. Assume $\delta\le1/(10C)$ and, by the exercise's symmetrization trick, $\mathbb E f=0$. For either restriction obtained by fixing coordinate $n$ to $b\in\{-1,1\}$, the restricted mean has absolute value at least $1-2C\delta$. Corollary 5.32 gives $W_1[f|_{x_n=b}]\le16C^2\delta^2\log(1/(C\delta))$. Averaging over $b$ yields
\[
16C^2\delta^2\log(1/(C\delta))\ge\mathbb E_b W_1[f|_{x_n=b}]
=\sum_{j<n}\bigl(\widehat f(j)^2+\widehat f(\{j,n\})^2\bigr)\ge\sum_{j<n}\widehat f(j)^2.
\]
The proof continues beyond the supplied pages.

<a id="pdf-ffbe9c7b3306-p130-b001"></a>
<!-- pdf-source: page=130; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p130-b002"></a>
<!-- pdf-source: page=130; block=2; confidence=0.99 -->
## 5.5. Highlight: Peres’s Theorem and uniform noise stability

<a id="pdf-ffbe9c7b3306-p130-b003"></a>
<!-- pdf-source: page=130; block=3; confidence=0.98 -->
Peres’s Theorem states that every LTF has \(\operatorname{NS}_\delta[f]\le O(\sqrt\delta)\). For unbiased LTFs with small coefficients, Theorem 5.17 gives the sharper noise-stability approximation \(\operatorname{Stab}_\rho[f]\approx\frac2\pi\arcsin\rho\).

<a id="pdf-ffbe9c7b3306-p130-b004"></a>
<!-- pdf-source: page=130; block=4; confidence=0.98 -->
**Theorem (Peres).** For every linear threshold function \(f:\{-1,1\}^n\to\{-1,1\}\), \(\operatorname{NS}_\delta[f]\le O(\sqrt\delta)\).

<a id="pdf-ffbe9c7b3306-p130-b005"></a>
<!-- pdf-source: page=130; block=5; confidence=0.98 -->
**Definition 5.34.** A class \(\mathcal B\) of Boolean-valued functions is uniformly noise-stable if there is a function \(\varepsilon:[0,1/2]\to[0,1]\), with \(\varepsilon(\delta)\to0\) as \(\delta\to0^+\), such that \(\operatorname{NS}_\delta[f]\le\varepsilon(\delta)\) for every \(f\in\mathcal B\).

<a id="pdf-ffbe9c7b3306-p130-b006"></a>
<!-- pdf-source: page=130; block=6; confidence=0.88 -->
The definition is nontrivial for infinite classes. Proposition 5.6 implies uniform Fourier concentration at some constant degree for each fixed error tolerance; Corollary 3.34 then gives polynomial-time learning from random examples to constant error for the restrictions to \(n\)-input functions.

<a id="pdf-ffbe9c7b3306-p131-b001"></a>
<!-- pdf-source: page=131; block=1; confidence=0.88 -->
Peres’s theorem yields Fourier concentration of LTFs through degree \(O(1/\varepsilon^2)\) and learning time \(n^{O(1/\varepsilon^2)}\) by Corollary 3.34. More generally, for \(\mathcal C=\{g(f_1,\ldots,f_s): f_i\text{ are LTFs}\}\), the stated union-bound estimate is \(\operatorname{NS}_\delta[h]\le O(s\sqrt\delta)\); hence learning time is \(n^{O(s^2/\varepsilon^2)}\).

<a id="pdf-ffbe9c7b3306-p131-b002"></a>
<!-- pdf-source: page=131; block=2; confidence=1.00 -->
**Theorem 5.35.** Let \(\delta\in(0,1/2]\) and \(A:\mathbb N^+\to\mathbb R\). If a class \(\mathcal B\) is closed under negating and identifying input variables, and every \(n\)-input \(f\in\mathcal B\) has \(I[f]\le A(n)\), then \(\operatorname{NS}_\delta[f]\le A(m)/m\), where \(m=\lfloor1/\delta\rfloor\).

<a id="pdf-ffbe9c7b3306-p131-b003"></a>
<!-- pdf-source: page=131; block=3; confidence=0.94 -->
**Proof.** Fix \(f:\{-1,1\}^n\to\{-1,1\}\) in \(\mathcal B\), and set \(m=\lfloor1/\delta\rfloor\). Monotonicity of noise sensitivity in the noise parameter reduces the claim to bounding \(\operatorname{NS}_{1/m}[f]\). For uniform \(z\in\{-1,1\}^n\) and a uniformly chosen map \(\pi:[n]\to[m]\), define \(w_\pi=(w_{\pi(1)},\ldots,w_{\pi(n)})\) and \(g_{z,\pi}(w)=f(z\circ w_\pi)\). This function is obtained by input negations and identifications, so it belongs to \(\mathcal B\); thus \(I[g_{z,\pi}]\le A(m)\), and its average influence is at most \(A(m)/m\). Averaging over \(z,\pi\), the expected average influence equals \(\operatorname{NS}_{1/m}[f]\): choosing a uniform coordinate \(j\in[m]\) flips the random block \(J=\pi^{-1}(j)\), whose coordinates are independently included with probability \(1/m\). The resulting pair has the noise distribution at rate \(1/m\), proving the bound.

<a id="pdf-ffbe9c7b3306-p132-b001"></a>
<!-- pdf-source: page=132; block=1; confidence=0.97 -->
For uniform independent \(w\in\{-1,1\}^m\) and \(j\in[m]\), the averaged influence is \(\Pr[g_{z,\pi}(w)\ne g_{z,\pi}(w\oplus j)]\). Writing \(J=\pi^{-1}(j)\) and letting \(\lambda_i=-1\) on \(J\), \(+1\) otherwise, this becomes the probability that \(f(z\circ w_\pi)\ne f(z\circ w_\pi\circ\lambda)\). Since \(z\circ w_\pi\) is uniform, the probability equals \(\operatorname{NS}_{1/m}[f]\), completing the theorem’s proof.

<a id="pdf-ffbe9c7b3306-p132-b002"></a>
<!-- pdf-source: page=132; block=2; confidence=0.99 -->
For LTFs, the class is closed under input negation and identification. An LTF on \(m\) bits is unate and has total influence at most \(\sqrt m\). Theorem 5.35 gives \(\operatorname{NS}_\delta[f]\le m^{-1}\sqrt m=1/\sqrt m\le O(\sqrt\delta)\), for \(m=\lfloor1/\delta\rfloor\).

<a id="pdf-ffbe9c7b3306-p132-b003"></a>
<!-- pdf-source: page=132; block=3; confidence=0.99 -->
Using the sharper unate bound \(I[f]\le\sqrt{2/\pi}\sqrt m+O(m^{-1/2})\) gives \(\operatorname{NS}_\delta[f]\le\sqrt{2/\pi}\sqrt\delta+O(\delta^{3/2})\).

<a id="pdf-ffbe9c7b3306-p133-b001"></a>
<!-- pdf-source: page=133; block=1; confidence=1.00 -->
## 5.5. Highlight: Peres’s Theorem and uniform noise stability

<a id="pdf-ffbe9c7b3306-p133-b002"></a>
<!-- pdf-source: page=133; block=2; confidence=0.96 -->
**Conjecture (Majority Is Least Stable).** If an odd-dimensional Boolean linear threshold function (LTF) is given, then for every $\rho\in[0,1]$, its noise stability satisfies $\operatorname{Stab}_\rho[f]\geq \operatorname{Stab}_\rho[\operatorname{Maj}_n]$. The text reports a counterexample for $n=5$ and suggests the possible replacement bound $\operatorname{Stab}_\rho[f]\geq \frac{2}{\pi}\arcsin\rho$ for all LTFs.

<a id="pdf-ffbe9c7b3306-p133-b003"></a>
<!-- pdf-source: page=133; block=3; confidence=0.83 -->
For integers $n,k$, define $P^{n,k}=\{f:\{-1,1\}^n\to\{-1,1\}: f\text{ is a PTF of degree at most }k\}$ and $P^k=\bigcup_n P^{n,k}$. Peres’s theorem gives uniform noise stability for $P^1$, the class of LTFs. The text asks whether this extends to higher-degree classes and discusses bounding $\operatorname{NS}_\delta[f]$ through total influence $I[f]$, using Theorem 5.35: an $o(n)$ influence bound would imply $\operatorname{NS}_\delta[f]=o_\delta(1)$ uniformly, while an $O_k(1)\sqrt n$ bound would yield $\operatorname{NS}_\delta[f]=O_k(1)\sqrt\delta$.

<a id="pdf-ffbe9c7b3306-p133-b004"></a>
<!-- pdf-source: page=133; block=4; confidence=0.99 -->
**Gotsman–Linial Conjecture.** For \(f\in\mathcal P_{n,k}\), \(I[f]\le O_k(1)\sqrt n\), more strongly \(I[f]\le O(k)\sqrt n\); the maximum is conjectured to be attained by a symmetric function \(f(x)=\operatorname{sgn}(p(x_1+\cdots+x_n))\) with \(p\) alternating sign on the \(k+1\) values closest to 0. The strongest form is known for \(k=1\).

<a id="pdf-ffbe9c7b3306-p133-b005"></a>
<!-- pdf-source: page=133; block=5; confidence=0.94 -->
The influence bounds are presented as progress toward the conjecture and as a converse perspective to Proposition 5.6, which approximates uniformly noise-stable classes by constant-degree PTFs.

<a id="pdf-ffbe9c7b3306-p134-b001"></a>
<!-- pdf-source: page=134; block=1; confidence=0.94 -->
**Theorem 5.37.** Every $f\in P^{n,k}$ satisfies $I[f]\leq \sqrt n\,(2k\log n)^{O(k\log k)}$. Consequently, for each fixed $k$, every $f\in P^k$ satisfies $\operatorname{NS}_\delta[f]\leq \sqrt\delta\,\operatorname{polylog}(1/\delta)$, by Theorem 5.35.

<a id="pdf-ffbe9c7b3306-p134-b002"></a>
<!-- pdf-source: page=134; block=2; confidence=1.00 -->
## 5.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p134-b003"></a>
<!-- pdf-source: page=134; block=3; confidence=0.99 -->
**Exercise 5.1.** (a) Show every LTF $f:\{-1,1\}^n\to\{-1,1\}$ has a representation $f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)$ with integer coefficients, using perturbation to obtain rational coefficients first. (b) Show a degree-$d$ PTF has a representation with all polynomial coefficients integral.

<a id="pdf-ffbe9c7b3306-p134-b004"></a>
<!-- pdf-source: page=134; block=4; confidence=0.99 -->
**Exercise 5.2.** For $f(x)=\operatorname{sgn}(a_0+\sum_{i=1}^n a_ix_i)$, prove: (a) $a_0=0$ implies $\mathbb E[f]=0$ because $f$ is odd; (b) $a_0\geq0$ implies $\mathbb E[f]\geq0$, while the converse can fail; (c) any unbiased LTF has a representation with zero constant term.

<a id="pdf-ffbe9c7b3306-p134-b005"></a>
<!-- pdf-source: page=134; block=5; confidence=0.99 -->
**Exercise 5.3.** If $f(x)=\operatorname{sgn}(a_0+\sum_i a_ix_i)$ and $|a_1|\geq\cdots\geq|a_n|$, prove $\operatorname{Inf}_1[f]\geq\cdots\geq\operatorname{Inf}_n[f]$. The hint reduces the argument to $n=2$.

<a id="pdf-ffbe9c7b3306-p134-b006"></a>
<!-- pdf-source: page=134; block=6; confidence=1.00 -->
**Exercise 5.4.** (a) Show there are at most \(2^{n^2+O(n)}\) LTFs on \(n\) variables. (b) Show there are at most \(2^{n^{k+1}+O(n)}\) degree-\(k\) PTFs.

<a id="pdf-ffbe9c7b3306-p134-b007"></a>
<!-- pdf-source: page=134; block=7; confidence=0.99 -->
**Exercise 5.5.** For the affine form $\ell(x)=a_0+\sum_{i=1}^n a_ix_i$, define its homogenization $\widetilde\ell(x_0,\ldots,x_n)=a_0x_0+\sum_{i=1}^n a_ix_i$. (a) Prove $\|\widetilde\ell\|_1=\|\ell\|_1$ and $\|\widetilde\ell\|_2^2=\|\ell\|_2^2$. (b) Complete the proof of Theorem 5.2.

<a id="pdf-ffbe9c7b3306-p134-b008"></a>
<!-- pdf-source: page=134; block=8; confidence=1.00 -->
**Exercise 5.6.** Show that an unbiased LTF has some coordinate \(i\) with \(\operatorname{Inf}_i[f]\ge1/\sqrt{2n}\).

<a id="pdf-ffbe9c7b3306-p134-b009"></a>
<!-- pdf-source: page=134; block=9; confidence=0.88 -->
**Exercise 5.7.** In a correlation-distillation setup, coordinate $i$ has independent repeated pairs of $\rho_i$-correlated bits, and a party observing the first vectors sends values $f(a^{(t)})$ so the other party can estimate each $\rho_i$ via $\mathbb E[f(a)b_i]$. The parties do not know the correlations in advance.

<a id="pdf-ffbe9c7b3306-p135-b001"></a>
<!-- pdf-source: page=135; block=1; confidence=0.97 -->
**Exercise 5.7 (continued).** (a) Prove $\mathbb E[f(a)b_i]=\widehat f(i)\rho_i$. (b) Show majority functions maximize the common value when all first-level Fourier coefficients $\widehat f(i)$ are required to be equal.

<a id="pdf-ffbe9c7b3306-p135-b002"></a>
<!-- pdf-source: page=135; block=2; confidence=1.00 -->
**Exercise 5.8.** For \(n\ge2\), a uniformly random Boolean function satisfies \(\|\widehat f\|_\infty\le2\sqrt n\,2^{-n/2}\), except with probability at most \(2^{-n}\).

<a id="pdf-ffbe9c7b3306-p135-b003"></a>
<!-- pdf-source: page=135; block=3; confidence=1.00 -->
**Exercise 5.9.** Prove Theorem 5.8.

<a id="pdf-ffbe9c7b3306-p135-b004"></a>
<!-- pdf-source: page=135; block=4; confidence=0.96 -->
**Exercise 5.10.** (a) Give a simple proof that parity $\chi_{[n]}$ is not a PTF of degree $n-1$. (b) Show every Boolean function other than $\pm\chi_{[n]}$ is a degree-$(n-1)$ PTF; the hint is to consider its Fourier truncation $f^{\leq n-1}$.

<a id="pdf-ffbe9c7b3306-p135-b005"></a>
<!-- pdf-source: page=135; block=5; confidence=0.99 -->
**Exercise 5.11.** For each \(k\in\mathbb N^+\), show there is a degree-\(k\) PTF \(f\) with \(W^{\le k}[f]<2^{1-k}\).

<a id="pdf-ffbe9c7b3306-p135-b006"></a>
<!-- pdf-source: page=135; block=6; confidence=0.99 -->
**Exercise 5.12.** (a) Every symmetric Boolean function is a sum of at most \(2n\) LTFs plus a constant. (b) A size-\(s\) threshold-of-parities circuit can be simulated by a size-\(2ns\) threshold-of-thresholds circuit. (c) \(\mathrm{CQ}_n\) has a size-\(2n\) threshold-of-thresholds circuit. (d) For even \(n\), every threshold-of-parities circuit for \(\mathrm{CQ}_n\) has size at least \(2^{n/2}\).

<a id="pdf-ffbe9c7b3306-p135-b007"></a>
<!-- pdf-source: page=135; block=7; confidence=0.98 -->
**Exercise 5.13.** Show that a Boolean function computed by a size-$s$ DNF has a PTF representation of sparsity $O(ns^3)$, and investigate whether this improves to $O(ns^2)$; use Theorem 5.12 to approximate the AND gates.

<a id="pdf-ffbe9c7b3306-p135-b008"></a>
<!-- pdf-source: page=135; block=8; confidence=0.95 -->
**Exercise 5.14.** Construct a depth-3 $\mathrm{AC}^0$ function requiring threshold-of-parities circuits of size at least $n^{\log n}$, using inner product modulo $2$ and Exercise 4.12.

<a id="pdf-ffbe9c7b3306-p135-b009"></a>
<!-- pdf-source: page=135; block=9; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p136-b001"></a>
<!-- pdf-source: page=136; block=1; confidence=0.99 -->
## 5. Majority and threshold functions

<a id="pdf-ffbe9c7b3306-p136-b002"></a>
<!-- pdf-source: page=136; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p136-b003"></a>
<!-- pdf-source: page=136; block=3; confidence=0.82 -->
Deduce that, except for at most a \(2^{-n}\) fraction of Boolean functions \(f\), there is a multilinear polynomial supported on the monomials \(\{\chi_S:S\in F\}\) whose uniform error from \(f\) is less than \(\varepsilon\).

<a id="pdf-ffbe9c7b3306-p136-b004"></a>
<!-- pdf-source: page=136; block=4; confidence=0.93 -->
For all but a \(2^{-n}\) fraction of Boolean functions, there is a real multilinear polynomial supported on the monomials \(\{\chi_S:S\in\mathcal F\}\) that is \(\varepsilon\)-close to \(f\), with PTF degree at most \(n/2+O(\sqrt{n\log n})\).

<a id="pdf-ffbe9c7b3306-p136-b005"></a>
<!-- pdf-source: page=136; block=5; confidence=0.90 -->
(a) Strengthen the Berry–Esseen conclusion to \(|\Pr[S<u]-\Pr[Z<u]|\le c\gamma\); the hint invokes \(\lim_{\delta\to0^+}\Pr[Z\le u-\delta]=\Pr[Z\le u]\). (b) Deduce for every interval \(I\) that \(|\Pr[S\in I]-\Pr[Z\in I]|\le 2c\gamma\).

<a id="pdf-ffbe9c7b3306-p136-b006"></a>
<!-- pdf-source: page=136; block=6; confidence=0.94 -->
For independent random variables \(X_1,\ldots,X_n\) with finite means and variances, set \(S=\sum_iX_i\), \(\mu=\sum_i\mathbb E[X_i]\), \(\sigma^2=\sum_i\operatorname{Var}(X_i)>0\), and \(Z\sim N(\mu,\sigma^2)\). Show for every real \(u\) that \(|\Pr[S\le u]-\Pr[Z\le u]|\le c\varepsilon/\sigma^3\), where \(\varepsilon=\sum_i\|X_i-\mathbb E[X_i]\|_3^3\).

<a id="pdf-ffbe9c7b3306-p136-b007"></a>
<!-- pdf-source: page=136; block=7; confidence=0.97 -->
(a) Use the generalized binomial theorem to derive the power series of \((1-z^2)^{-1/2}\) for \(|z|<1\). (b) Integrate it to obtain the arcsine series (5.9), valid for \(|z|<1\). (c) Verify equality at \(z=\pm1\) as well.

<a id="pdf-ffbe9c7b3306-p136-b008"></a>
<!-- pdf-source: page=136; block=8; confidence=0.94 -->
Verify for the random vector \(\widetilde S\) in (5.7) that \(\mathbb E[\widetilde S_1]=\mathbb E[\widetilde S_2]=0\), each coordinate has second moment 1, and \(\mathbb E[\widetilde S_1\widetilde S_2]=\rho\); hence its covariance matrix is \(\begin{bmatrix}1&\rho\\\rho&1\end{bmatrix}\).

<a id="pdf-ffbe9c7b3306-p136-b009"></a>
<!-- pdf-source: page=136; block=9; confidence=0.99 -->
Prove Corollary 5.20.

<a id="pdf-ffbe9c7b3306-p136-b010"></a>
<!-- pdf-source: page=136; block=10; confidence=0.87 -->
For odd \(n\), use Theorem 5.19 to show that \(|\widehat{\mathrm{Maj}}_n(S)|\) decreases as \(|S|\) ranges over odd values from 1 to \(n-1\). Together with Corollary 5.20, deduce \(\|\widehat{\mathrm{Maj}}_n\|_\infty=\widehat{\mathrm{Maj}}_n(\{1\})\sim\sqrt{2/\pi}/\sqrt n\).

<a id="pdf-ffbe9c7b3306-p136-b011"></a>
<!-- pdf-source: page=136; block=11; confidence=0.99 -->
Prove Corollary 5.21.

<a id="pdf-ffbe9c7b3306-p136-b012"></a>
<!-- pdf-source: page=136; block=12; confidence=0.99 -->
Prove Theorem 5.18, using Corollary 5.21.

<a id="pdf-ffbe9c7b3306-p136-b013"></a>
<!-- pdf-source: page=136; block=13; confidence=0.94 -->
Show \((1-(\binom{n}{k+1}/\binom{n}{k})^2)^{-1/2}\le1+2k/n\) for \(1\le k\le n/2\).

<a id="pdf-ffbe9c7b3306-p137-b001"></a>
<!-- pdf-source: page=137; block=1; confidence=0.99 -->
## 5.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p137-b002"></a>
<!-- pdf-source: page=137; block=2; confidence=0.92 -->
Assuming \(\operatorname{Stab}_\rho[\mathrm{Maj}_n]\to(2/\pi)\arcsin\rho\) for every \(\rho\in[-1,1]\), and \(\operatorname{Stab}_\rho[\mathrm{Maj}_n]=\sum_{k\ge0}W_k[\mathrm{Maj}_n]\rho^k\), deduce coefficientwise convergence \(W_k[\mathrm{Maj}_n]\to[\rho^k]((2/\pi)\arcsin\rho)\) for every nonnegative integer \(k\). Hint: induct on \(k\), choosing \(\rho\) sufficiently small.

<a id="pdf-ffbe9c7b3306-p137-b003"></a>
<!-- pdf-source: page=137; block=3; confidence=0.92 -->
**Exercise 5.26.** (a) For \(0\le j\le m\), show \(\|\widehat{\mathrm{Maj}_{2m+1}}\|_1=\mathbb E[\frac1{2X+1}]\,\frac{2m+1}{2^{2m}}\binom{2m}{m}\), where \(X\sim\operatorname{Binomial}(m,1/2)\). (b) Deduce \(\|\widehat{\mathrm{Maj}_n}\|_1\sim\frac{2}{\sqrt\pi}\frac{2^{n/2}}{\sqrt n}\).

<a id="pdf-ffbe9c7b3306-p137-b004"></a>
<!-- pdf-source: page=137; block=4; confidence=0.96 -->
**Exercise 5.27.** For each odd \(k\), prove \[(2/\pi)^{3/2}k^{-3/2}\le[\rho^k](\tfrac2\pi\arcsin\rho)\le(2/\pi)^{3/2}k^{-3/2}(1+O(1/k)).\] Use Stirling’s approximation, then prove Corollary 5.23.

<a id="pdf-ffbe9c7b3306-p137-b005"></a>
<!-- pdf-source: page=137; block=5; confidence=0.92 -->
**Definition (Exercise 5.28).** For integers \(0\le j\le n\), define \(K_j(x)=\sum_{|S|=j}x_S\) on \(\{-1,1\}^n\), and regard it as a function of the number \(z\) of minus signs in \(x\), since \(\sum_i x_i=n-2z\).

<a id="pdf-ffbe9c7b3306-p137-b006"></a>
<!-- pdf-source: page=137; block=6; confidence=0.97 -->
Show that \(K_j(z)\) is a degree-\(j\) polynomial in \(z\), called the degree-\(j\) Kravchuk (Krawtchouk) polynomial, with dependence on \(n\) implicit.

<a id="pdf-ffbe9c7b3306-p137-b007"></a>
<!-- pdf-source: page=137; block=7; confidence=0.97 -->
Show \(\sum_{j=0}^n K_j(x)=2^n\mathbf 1_{(1,\ldots,1)}(x)\).

<a id="pdf-ffbe9c7b3306-p137-b008"></a>
<!-- pdf-source: page=137; block=8; confidence=0.99 -->
For \(\rho\in[-1,1]\), show \(\sum_{j=0}^nK_j(x)\rho^j=2^n\Pr[y=(1,\ldots,1)]\), where \(y\sim N_\rho(x)\).

<a id="pdf-ffbe9c7b3306-p137-b009"></a>
<!-- pdf-source: page=137; block=9; confidence=0.82 -->
Deduce the generating-function identity \(K_j(z)=[\rho^j]((1-\rho)^z(1+\rho)^{n-z})\).

<a id="pdf-ffbe9c7b3306-p137-b010"></a>
<!-- pdf-source: page=137; block=10; confidence=0.99 -->
Prove Proposition 5.24.

<a id="pdf-ffbe9c7b3306-p137-b011"></a>
<!-- pdf-source: page=137; block=11; confidence=0.97 -->
**Exercise 5.31(b).** Let \(S=\sum_i a_ix_i\), where \(x\) is uniform on the cube and \(\sum_i a_i^2=1\). For \(Z\sim N(0,1)\), use Berry–Esseen and the tail bounds to show \(|\mathbb E|S|-\mathbb E|Z||\le O(\varepsilon T+e^{-T^2/2})\) for \(T\ge1\).

<a id="pdf-ffbe9c7b3306-p137-b012"></a>
<!-- pdf-source: page=137; block=12; confidence=0.76 -->
In the setting of Theorem 5.16, let \(S=\sum_{i=1}^n a_i x_i/\sqrt n\) and \(Z\sim N(0,1)\). (a) Show both tails satisfy \(\Pr[|S|\ge t],\Pr[|Z|\ge t]\le2e^{-t^2/2}\) for \(t\ge0\). (b) Using \(\mathbb E|Y|=\int_0^\infty\Pr[|Y|\ge t]dt\), Berry–Esseen, and Remark 5.15 and Exercise 5.16, prove \(|\mathbb E|S|-\mathbb E|Z||=O(\varepsilon T+e^{-T^2/2})\) for \(T\ge1\). (c) Deduce an error bound \(O(\varepsilon\sqrt{\log(1/\varepsilon)})\) for approximating \(\mathbb E|S|\) by \(\sqrt{2/\pi}\). (d) Improve this to the \(O(\varepsilon)\) bound in Theorem 5.16 using the nonuniform Berry–Esseen bound \(C\gamma/(1+|u|^3)\).

<a id="pdf-ffbe9c7b3306-p138-b001"></a>
<!-- pdf-source: page=138; block=1; confidence=0.87 -->
For the sequence of LTFs in Proposition 5.25, show \(\lim_{n\to\infty}\operatorname{Stab}_\rho[f_n]=\Lambda_\rho(\mu)\), where \(\mu=\Phi(t)\) and \(\Lambda_\rho(\mu)=\Pr[z_1>t,z_2>t]\) for standard Gaussians with correlation \(\rho\). Also verify \(\Lambda_\rho(\alpha)=\Pr[z_1\le t,z_2\le t]\) when \(\alpha=\Phi(t)\).

<a id="pdf-ffbe9c7b3306-p138-b002"></a>
<!-- pdf-source: page=138; block=2; confidence=0.96 -->
**Theorem 5.38.** Let \(X_1,\ldots,X_n\) be independent mean-zero random vectors in \(\mathbb R^d\), set \(S=\sum_iX_i\), and assume \(\Sigma=\operatorname{Cov}(S)\) is invertible. If \(Z\sim N(0,\Sigma)\), then for every convex \(U\subseteq\mathbb R^d\), \(|\Pr[S\in U]-\Pr[Z\in U]|\le C d^{1/4}\gamma\), where \(C\) is universal and \(\gamma=\sum_i\mathbb E[\|\Sigma^{-1/2}X_i\|_2^3]\).

<a id="pdf-ffbe9c7b3306-p138-b003"></a>
<!-- pdf-source: page=138; block=3; confidence=1.00 -->
For \(\Sigma=\begin{bmatrix}1&\rho\\\rho&1\end{bmatrix}\), verify \(\Sigma^{-1}=\begin{bmatrix}1&-\rho\\0&1\end{bmatrix}\begin{bmatrix}1&0\\0&(1-\rho^2)^{-1}\end{bmatrix}\begin{bmatrix}1&0\\-\rho&1\end{bmatrix}\), then compute \(y^T\Sigma^{-1}y\) for \(y=(\pm a,\pm a)^T\) and complete the proof of Theorem 5.17.

<a id="pdf-ffbe9c7b3306-p138-b004"></a>
<!-- pdf-source: page=138; block=4; confidence=0.88 -->
For a class \(B\) of Boolean functions whose input lengths are at most \(n\), show \(NS_\delta[f]\le n\delta\) for all \(f\in B\), and hence that \(B\) is uniformly noise-stable in the stated sense. Hint: Exercise 2.42.

<a id="pdf-ffbe9c7b3306-p138-b005"></a>
<!-- pdf-source: page=138; block=5; confidence=0.98 -->
If \(f:\{-1,1\}^n\to\{-1,1\}\) has \(\mathbb E[f]=0\) and \(I[f]\le1+\delta\), show it is \(O(\delta)\)-close to some \(\pm\chi_i\); the exercise notes that \(\delta\)-closeness should be achievable.

<a id="pdf-ffbe9c7b3306-p138-b006"></a>
<!-- pdf-source: page=138; block=6; confidence=0.86 -->
Show Theorem 5.33 is essentially sharp by constructing Boolean functions with \(\widehat f(1)=1-\delta/2\) and \(W_1[f]\ge1-\delta+\Omega(\delta^2\log(1/\delta))\) along a sequence \(\delta\to0\).

<a id="pdf-ffbe9c7b3306-p138-b007"></a>
<!-- pdf-source: page=138; block=7; confidence=0.99 -->
Prove Corollary 5.32.

<a id="pdf-ffbe9c7b3306-p138-b008"></a>
<!-- pdf-source: page=138; block=8; confidence=0.99 -->
Fill in the details of the proof of Theorem 5.33.

<a id="pdf-ffbe9c7b3306-p139-b001"></a>
<!-- pdf-source: page=139; block=1; confidence=1.00 -->
## 5.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p139-b002"></a>
<!-- pdf-source: page=139; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p139-b003"></a>
<!-- pdf-source: page=139; block=3; confidence=0.92 -->
**Exercise 5.40.** Suppose \(\operatorname{NS}_\delta[f]\le\varepsilon(\delta)\) for all \(f\in\mathcal P_k\). Show \(I[f]\le O(\varepsilon(1/n)n)\) for all \(f\in\mathcal P_{n,k}\). Deduce that \(\mathcal P_k\) is uniformly noise-stable iff \(I[f]=o(n)\) for every \(f\in\mathcal P_{n,k}\), and that \(\operatorname{NS}_\delta[f]\le O(k\sqrt\delta)\) iff \(I[f]\le O(k\sqrt n)\), as stated in the exercise.

<a id="pdf-ffbe9c7b3306-p139-b004"></a>
<!-- pdf-source: page=139; block=4; confidence=0.91 -->
**Exercise 5.41.** Carefully estimate the asymptotics of $I[f]$ for the degree-$k$ PTF from the strongest form of the Gotsman–Linial Conjecture.

<a id="pdf-ffbe9c7b3306-p139-b005"></a>
<!-- pdf-source: page=139; block=5; confidence=0.87 -->
**Exercise 5.42.** If $A\subseteq\{-1,1\}^n$ has size $\alpha 2^n$, with $\alpha\le 1/2$, regard the cube as a subset of $\mathbb R^n$ and let $\mu_A$ be the center of mass of $A$. Show $\|\mu_A\|_2\le O(\sqrt{\log(1/\alpha)})$.

<a id="pdf-ffbe9c7b3306-p139-b006"></a>
<!-- pdf-source: page=139; block=6; confidence=0.98 -->
**Exercise 5.43.** Show that the Gaussian isoperimetric function satisfies $U''=-1/U$ on $(0,1)$, and deduce that $U$ is concave.

<a id="pdf-ffbe9c7b3306-p139-b007"></a>
<!-- pdf-source: page=139; block=7; confidence=0.92 -->
**Exercise 5.44.** Fix $\alpha\in(0,1/2)$. If $f:\{-1,1\}^n\to[-1,1]$ satisfies $\mathbb E[|f|]\le\alpha$ and $|\widehat f(i)|\le\varepsilon$ for every $i$, show $W_1[f]\le U(\alpha)^2+C\varepsilon$, where $U$ is the Gaussian isoperimetric function and $C$ may depend on $\alpha$. (Hint: use the nonuniform Berry–Esseen theorem from Exercise 5.31.)

<a id="pdf-ffbe9c7b3306-p139-b008"></a>
<!-- pdf-source: page=139; block=8; confidence=0.82 -->
**Exercise 5.45.** Prove by induction on $k$ that every degree-$k$ PTF $f:\{-1,1\}^n\to\{-1,1\}$ satisfies $I[f]\le 2n^{1-1/(2k)}$. The base case $k=0$ is immediate. For $k>0$, write $f=\operatorname{sgn}(p)$, where $p$ is a degree-$k$ polynomial that never vanishes. Parts (a)–(e) specify the induction: (a) show $\mathbb E[f(x)x_i\operatorname{sgn}(D_i p(x))]=\operatorname{Inf}_i[f]$, using $f=x_iD_i f+E_i f$ and $D_i f=\operatorname{sgn}(D_i p)$ whenever $D_i f\ne0$; (b) deduce $I[f]\le\mathbb E[|\sum_i x_i\operatorname{sgn}(D_i p(x))|]$; (c) apply Cauchy–Schwarz to obtain $I[f]\le\sqrt{n+\sum_{i\ne j}\mathbb E[x_ix_j\operatorname{sgn}(D_i p(x))\operatorname{sgn}(D_j p(x))]}$; (d) use Exercise 2.19 and AM–GM to get $I[f]\le\sqrt{n+\sum_i I[\operatorname{sgn}(D_i p)]}$; (e) complete the induction. The remark in (b) says that for $k=2$, when each $\operatorname{sgn}(D_i p)$ is an LTF, the bound is conjectured to remain $O(\sqrt n)$.

<a id="pdf-ffbe9c7b3306-p140-b001"></a>
<!-- pdf-source: page=140; block=1; confidence=0.98 -->
**Exercise 5.45(f).** Deduce from Theorem 5.35 that every degree-$k$ PTF is uniformly noise-stable, specifically $\operatorname{NS}_\delta[f]\le 3\delta^{1/(2k)}$ for $\delta\in(0,1/2]$.

<a id="pdf-ffbe9c7b3306-p140-b002"></a>
<!-- pdf-source: page=140; block=2; confidence=0.87 -->
The notes attribute Chow’s Theorem to Chow and Tannenbaum, its PTF generalization and related results to Bruck, and the Gotsman–Linial theorems and conjecture to Gotsman and Linial. They also credit Bruck–Smolensky, Krause–Pudlák, Zuev, and O’Donnell–Servedio for other results and exercises in the chapter. The discussion of Majority’s Fourier expansion and level weights cites Titsworth, O’Donnell, and others, and notes the origins of Kravchuk polynomials.

<a id="pdf-ffbe9c7b3306-p140-b003"></a>
<!-- pdf-source: page=140; block=3; confidence=0.90 -->
The Berry–Esseen theorem is credited independently to Berry and Esseen; the nonuniform version in Exercise 5.31 to Bikelis; the multidimensional version in Theorem 5.38 (stated in Exercise 5.33) to Bentkus; and Sheppard’s formula to Sheppard. The notes also give attributions for the Level-1 inequality, the two parts of the $2/\pi$ theorem, and the FKN closeness result and its optimality.

<a id="pdf-ffbe9c7b3306-p141-b001"></a>
<!-- pdf-source: page=141; block=1; confidence=0.94 -->
The original FKN proof achieved closeness $\delta/2$; Kindler–Safra gave a self-contained proof of that bound using the Hoeffding bound. Exercise 5.35 was communicated by Eric Blais; Exercise 5.44 is attributed to [KKMO07], and Exercise 5.42 was suggested by Rocco Servedio.

<a id="pdf-ffbe9c7b3306-p141-b002"></a>
<!-- pdf-source: page=141; block=2; confidence=0.94 -->
Peres’s theorem appeared in 2004 after being mentioned in 1999; the earlier work introduced uniform noise stability and established it for LTFs, with a weaker $O(\delta^{1/4})$ noise-sensitivity bound. The presented proof is a simplification by Parikshit Gopalan incorporating an idea of Diakonikolas et al. Kane’s result gives $I[f]\le\operatorname{poly}(k)n^{1-1/O(k)}$ for degree-$k$ PTFs, improving Theorem 5.37 for some superconstant $k$. Exercise 5.39 was suggested by Nitin Saurabh.

<a id="pdf-ffbe9c7b3306-p143-b001"></a>
<!-- pdf-source: page=143; block=1; confidence=1.00 -->
# Chapter 6: Pseudorandomness and \(\mathbb F_2\)-polynomials

<a id="pdf-ffbe9c7b3306-p143-b002"></a>
<!-- pdf-source: page=143; block=2; confidence=0.89 -->
The chapter studies pseudorandom properties of Boolean functions, small-support pseudorandom densities, and connections between real and over \(\mathbb F_2\) polynomial representations.

<a id="pdf-ffbe9c7b3306-p143-b003"></a>
<!-- pdf-source: page=143; block=3; confidence=0.99 -->
## 6.1. Notions of pseudorandomness

<a id="pdf-ffbe9c7b3306-p143-b004"></a>
<!-- pdf-source: page=143; block=4; confidence=0.95 -->
For a random Boolean function with values in \(\{0,1\}\), the mean is near \(1/2\) and nonconstant Fourier coefficients are small; the next proposition quantifies this for a \(p\)-biased random function.

<a id="pdf-ffbe9c7b3306-p143-b005"></a>
<!-- pdf-source: page=143; block=5; confidence=0.99 -->
**Proposition 6.1.** Let \(n>1\) and choose each \(f(x)\) independently to be 1 with probability \(p\), otherwise 0. Except with probability at most \(2^{-n}\), \[|\widehat f(\varnothing)-p|\le2\sqrt n\,2^{-n/2},\qquad |\widehat f(S)|\le2\sqrt n\,2^{-n/2}\quad(S\ne\varnothing).\]

<a id="pdf-ffbe9c7b3306-p144-b001"></a>
<!-- pdf-source: page=144; block=1; confidence=0.88 -->
**Proof.** Each Fourier coefficient is \(\widehat f(S)=2^{-n}\sum_x x_S f(x)\), a sum of independent random variables. Its expectation is \(p\) when \(S=\varnothing\) and \(0\) otherwise, since the coefficients \(2^{-n}x_S\) sum to \(1\) for the empty set and to \(0\) otherwise. Hoeffding's inequality gives
\[
\Pr\big[|\widehat f(S)-\mathbb E\widehat f(S)|\ge t\big]\le 2\exp(-t^2 2^{n-1})\quad(t>0).
\]
Taking \(t=2\sqrt n\,2^{-n/2}\) makes this at most \(2e^{-2n}\le4^{-n}\). A union bound over all \(S\subseteq[n]\) proves the claim.

<a id="pdf-ffbe9c7b3306-p144-b002"></a>
<!-- pdf-source: page=144; block=2; confidence=0.99 -->
The proposition motivates a Fourier-uniformity notion called regularity.

<a id="pdf-ffbe9c7b3306-p144-b003"></a>
<!-- pdf-source: page=144; block=3; confidence=1.00 -->
**Definition 6.2.** \(f:\{-1,1\}^n\to\mathbb R\) is \(\varepsilon\)-regular if \(|\widehat f(S)|\le\varepsilon\) for every nonempty \(S\subseteq[n]\).

<a id="pdf-ffbe9c7b3306-p144-b004"></a>
<!-- pdf-source: page=144; block=4; confidence=0.91 -->
By Exercise 3.9, every function is \(\|f\|_1\)-regular; for functions valued in \([-1,1]\), the text focuses on \(\epsilon\le1\).

<a id="pdf-ffbe9c7b3306-p144-b005"></a>
<!-- pdf-source: page=144; block=5; confidence=0.99 -->
An affine subspace of codimension \(k\) has indicator that is \(2^{-k}\)-regular. For even \(n\), \(\mathrm{IP}_n\) and \(\mathrm{CQ}_n\) are \(2^{-n/2-1}\)-regular. Nonempty parity characters are not \(\varepsilon\)-regular for \(\varepsilon<1\), while \(\mathrm{Maj}_n\) is \(1/\sqrt n\)-regular.

<a id="pdf-ffbe9c7b3306-p144-b006"></a>
<!-- pdf-source: page=144; block=6; confidence=0.99 -->
For probability densities, regularity is also expressed through a notion of biasedness.

<a id="pdf-ffbe9c7b3306-p144-b007"></a>
<!-- pdf-source: page=144; block=7; confidence=1.00 -->
**Definition 6.5.** A probability density \(\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}\) is \(\varepsilon\)-biased if it is \(\varepsilon\)-regular, equivalently \(|\mathbb E_{x\sim\varphi}[\chi_\gamma(x)]|\le\varepsilon\) for every nonzero \(\gamma\in\mathbb F_2^n\).

<a id="pdf-ffbe9c7b3306-p144-b008"></a>
<!-- pdf-source: page=144; block=8; confidence=0.87 -->
Every probability density is \(1\)-biased, and the uniform density is the only \(0\)-biased density. A uniform density on a proper affine subspace is not \(\epsilon\)-biased for any \(\epsilon<1\) (Proposition 3.12). The two-point set \(\{(0,\ldots,0),(1,\ldots,1)\}\) is \(1/2\)-biased.

<a id="pdf-ffbe9c7b3306-p144-b009"></a>
<!-- pdf-source: page=144; block=9; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p145-b001"></a>
<!-- pdf-source: page=145; block=1; confidence=1.00 -->
## 6.1. Notions of pseudorandomness

<a id="pdf-ffbe9c7b3306-p145-b002"></a>
<!-- pdf-source: page=145; block=2; confidence=0.98 -->
The section compares the non-Fourier expression \(\mathbb E_{x,y,z}[f(x)f(y)f(z)f(x+y+z)]\) with \((\mathbb E f)^4\) as a test for regularity.

<a id="pdf-ffbe9c7b3306-p145-b003"></a>
<!-- pdf-source: page=145; block=3; confidence=0.97 -->
**Proposition 6.7.** Let \(f:\mathbb F_2^n\to\mathbb R\). (1) If \(f\) is \(\varepsilon\)-regular, then \(\|\widehat f\|_4^4-\mathbb E[f]^4\le\varepsilon^2\operatorname{Var}[f]\). (2) If \(f\) is not \(\varepsilon\)-regular, then \(\|\widehat f\|_4^4-\mathbb E[f]^4\ge\varepsilon^4\).

<a id="pdf-ffbe9c7b3306-p145-b004"></a>
<!-- pdf-source: page=145; block=4; confidence=0.92 -->
**Proof.** In the regular case, \(\sum_{S\ne\varnothing}\widehat f(S)^4\le \max_{S\ne\varnothing}\widehat f(S)^2\sum_{S\ne\varnothing}\widehat f(S)^2\le\varepsilon^2\operatorname{Var}[f]\). Otherwise some nonempty \(T\) has \(|\widehat f(T)|\ge\varepsilon\), so \(\|\widehat f\|_4^4\ge\widehat f(\varnothing)^4+\widehat f(T)^4\ge(\mathbb E f)^4+\varepsilon^4\).

<a id="pdf-ffbe9c7b3306-p145-b005"></a>
<!-- pdf-source: page=145; block=5; confidence=0.99 -->
The text motivates weaker conditions based on small low-degree Fourier coefficients or small influences, and proceeds with stable influences.

<a id="pdf-ffbe9c7b3306-p145-b006"></a>
<!-- pdf-source: page=145; block=6; confidence=0.96 -->
**Fact 6.8.** For fixed \(\delta\in[0,1]\), a uniformly random Boolean function \(f:\{-1,1\}^n\to\{-1,1\}\) satisfies, for each \(i\in[n]\), \(\mathbb E[\operatorname{Inf}^{(1-\delta)}_i[f]]=\frac{(1-\delta/2)^n}{2-\delta}\).

<a id="pdf-ffbe9c7b3306-p145-b007"></a>
<!-- pdf-source: page=145; block=7; confidence=0.98 -->
Having all stable influences small is presented as having no notable coordinates.

<a id="pdf-ffbe9c7b3306-p145-b008"></a>
<!-- pdf-source: page=145; block=8; confidence=0.98 -->
**Definition 6.9.** The function \(f\) has \((\varepsilon,\delta)\)-small stable influences (or no \((\varepsilon,\delta)\)-notable coordinates) if \(\operatorname{Inf}^{(1-\delta)}_i[f]\le\varepsilon\) for every coordinate \(i\). At \(\delta=0\), this is called having \(\varepsilon\)-small influences.

<a id="pdf-ffbe9c7b3306-p145-b009"></a>
<!-- pdf-source: page=145; block=9; confidence=0.99 -->
**Example 6.10.** The example begins listing Boolean-valued functions with no notable coordinates; the list continues on page 146.

<a id="pdf-ffbe9c7b3306-p146-b001"></a>
<!-- pdf-source: page=146; block=1; confidence=0.99 -->
A parity \(\chi_S\), with \(S\ne\varnothing\), has stable influence \((1-\delta)^{|S|-1}\) on coordinates in \(S\) and 0 otherwise. In particular, it has \((\varepsilon,\delta)\)-small stable influences when \(|S|\ge\ln(1/\varepsilon)/\delta\).

<a id="pdf-ffbe9c7b3306-p146-b002"></a>
<!-- pdf-source: page=146; block=2; confidence=0.99 -->
An unbiased \(k\)-junta has variance 1, so its stable influences sum to at least \((1-\delta)^{k-1}\). Thus some coordinate has stable influence at least \((1-\delta)^{k-1}/k\). The function \(f(x)=x_0\mathrm{Maj}_n(x_1,\ldots,x_n)\) satisfies \(\operatorname{Inf}^{(1-\delta)}_0[f]\ge1-\sqrt\delta\).

<a id="pdf-ffbe9c7b3306-p146-b003"></a>
<!-- pdf-source: page=146; block=3; confidence=0.92 -->
The condition \(|\widehat f(\{i\})|\le\varepsilon\) for every coordinate is called \((\varepsilon,1)\)-regularity; equivalently, \(f^{\le1}\) is \(\varepsilon\)-regular, or \(|\langle f,\pm\chi_i\rangle|\le\varepsilon\) for every dictator. The next definition extends this to higher degrees.

<a id="pdf-ffbe9c7b3306-p146-b004"></a>
<!-- pdf-source: page=146; block=4; confidence=0.94 -->
**Definition 6.11.** The function \(f:\{-1,1\}^n\to\mathbb R\) is \((\varepsilon,k)\)-regular if \(|\widehat f(S)|\le\varepsilon\) whenever \(0<|S|\le k\), equivalently if \(f^{\le k}\) is \(\varepsilon\)-regular. For \(k=n\) (or \(k=\infty\)) this is \(\varepsilon\)-regularity. A probability density \(\varphi:\{-1,1\}^n\to\mathbb R_{\ge0}\) with this property is called \((\varepsilon,k)\)-wise independent.

<a id="pdf-ffbe9c7b3306-p146-b005"></a>
<!-- pdf-source: page=146; block=5; confidence=0.99 -->
Two rough characterizations have exponential losses in \(k\): restrictions to at most \(k\) coordinates change the mean by at most order \(\varepsilon\), and covariance with any \(k\)-junta is at most order \(\varepsilon\).

<a id="pdf-ffbe9c7b3306-p146-b006"></a>
<!-- pdf-source: page=146; block=6; confidence=0.96 -->
**Proposition 6.12.** For \(f:\{-1,1\}^n\to\mathbb R\), \(\varepsilon\ge0\), and integer \(k\): (1) if \(f\) is \((\varepsilon,k)\)-regular, every restriction fixing at most \(k\) coordinates changes its mean by at most \(2^k\varepsilon\); (2) if it is not \((\varepsilon,k)\)-regular, some restriction fixing at most \(k\) coordinates changes its mean by more than \(\varepsilon\).

<a id="pdf-ffbe9c7b3306-p146-b007"></a>
<!-- pdf-source: page=146; block=7; confidence=0.99 -->
**Proposition 6.13.** The statement begins here and continues on page 147.

<a id="pdf-ffbe9c7b3306-p147-b001"></a>
<!-- pdf-source: page=147; block=1; confidence=0.95 -->
**Proposition 6.13.** For \(f:\{-1,1\}^n\to\mathbb R\), \(\varepsilon\ge0\), and integer \(k\): (1) if \(f\) is \((\varepsilon,k)\)-regular, then \(\operatorname{Cov}[f,h]\le\|\widehat h\|_1\varepsilon\) for every \(h\) of degree at most \(k\), and in particular \(\operatorname{Cov}[f,h]\le2^{k/2}\varepsilon\) for every Boolean-valued \(k\)-junta; (2) if \(f\) is not \((\varepsilon,k)\)-regular, some Boolean-valued \(k\)-junta \(h\) satisfies \(\operatorname{Cov}[f,h]>\varepsilon\).

<a id="pdf-ffbe9c7b3306-p147-b002"></a>
<!-- pdf-source: page=147; block=2; confidence=0.99 -->
The proof of Proposition 6.12 is given; Proposition 6.13 is left as an exercise.

<a id="pdf-ffbe9c7b3306-p147-b003"></a>
<!-- pdf-source: page=147; block=3; confidence=0.95 -->
**Proof.** For the first claim, if \(|J|\le k\) and \(z\in\{-1,1\}^J\), then \(\mathbb E[f\mid x_J=z]=\widehat f(\varnothing)+\sum_{\varnothing\ne T\subseteq J}\widehat f(T)z_T\). There are at most \(2^k\) nonconstant terms, each bounded by \(\varepsilon\), giving the stated mean-change bound. For the second claim, choose \(J\) with \(0<|J|\le k\) and \(|\widehat f(J)|>\varepsilon\). The mean change as a function of the restriction \(z\) is \(h(z)=\sum_{\varnothing\ne T\subseteq J}\widehat f(T)z_T\). Since \(\|h\|_\infty=\|h\chi_J\|_\infty\ge|\mathbb E[h\chi_J]|=|\widehat h(J)|=|\widehat f(J)|>\varepsilon\), some restriction changes the mean by more than \(\varepsilon\).

<a id="pdf-ffbe9c7b3306-p147-b004"></a>
<!-- pdf-source: page=147; block=4; confidence=0.97 -->
**Corollary 6.14.** For \(f:\{-1,1\}^n\to\mathbb R\), the following are equivalent: (1) \(f\) is \((0,k)\)-regular; (2) every restriction fixing at most \(k\) coordinates leaves the mean unchanged; (3) \(\operatorname{Cov}[f,h]=0\) for every Boolean-valued \(k\)-junta \(h\). If \(f\) is a probability density, (3) is equivalent to \(\mathbb E_{x\sim f}[h(x)]=\mathbb E[h]\) for every such junta.

<a id="pdf-ffbe9c7b3306-p147-b005"></a>
<!-- pdf-source: page=147; block=5; confidence=0.99 -->
The text introduces terminology for functions satisfying the equivalent conditions of Corollary 6.14.

<a id="pdf-ffbe9c7b3306-p147-b006"></a>
<!-- pdf-source: page=147; block=6; confidence=0.98 -->
**Definition 6.15.** A Boolean-valued \((0,k)\)-regular function is called \(k\)th-order correlation immune; if it is also unbiased, it is \(k\)-resilient. A \((0,k)\)-regular probability density, and its associated distribution, are called \(k\)-wise independent.

<a id="pdf-ffbe9c7b3306-p147-b007"></a>
<!-- pdf-source: page=147; block=7; confidence=0.90 -->
**Example 6.16.** Any parity \(\chi_S\) with \(|S|=k+1\) is \(k\)-resilient; so is \(\chi_Sg\) when Boolean-valued \(g\) is independent of coordinates in \(S\). A correlation-immune but non-resilient example is \(h=\chi_{\{1,\ldots,2m\}}\wedge\chi_{\{m+1,\ldots,3m\}}\) on \(3m\) coordinates; it is true on only a fraction of inputs, so is biased.

<a id="pdf-ffbe9c7b3306-p148-b001"></a>
<!-- pdf-source: page=148; block=1; confidence=0.96 -->
A function whose bias changes only after fixing at least `2m` input bits is `(2m − 1)`st-order correlation immune.

<a id="pdf-ffbe9c7b3306-p148-b002"></a>
<!-- pdf-source: page=148; block=2; confidence=1.00 -->
## 6.2. 2-polynomials

<a id="pdf-ffbe9c7b3306-p148-b003"></a>
<!-- pdf-source: page=148; block=3; confidence=0.99 -->
The section considers Boolean functions represented over `𝔽₂`, with False/True encoded as `0/1`; addition and multiplication correspond to XOR and AND.

<a id="pdf-ffbe9c7b3306-p148-b004"></a>
<!-- pdf-source: page=148; block=4; confidence=0.99 -->
**Example 6.17.** Parity on `n` bits has real representation `χ_[n](x) = x₁⋯xₙ` under the `±1` encoding, of degree `n`. Under the `𝔽₂` encoding it is `χ_[n](x) = x₁ + ⋯ + xₙ`, of degree `1`.

<a id="pdf-ffbe9c7b3306-p148-b005"></a>
<!-- pdf-source: page=148; block=5; confidence=0.99 -->
For `a ∈ 𝔽₂ⁿ`, its indicator has the degree-`n` representation `1_{a}(x) = ∏_{i:aᵢ=1} xᵢ ∏_{i:aᵢ=0}(1−xᵢ)` (6.1).

<a id="pdf-ffbe9c7b3306-p149-b001"></a>
<!-- pdf-source: page=149; block=1; confidence=0.98 -->
Summing the indicators weighted by `f(a)` gives `f(x) = ∑_{a∈𝔽₂ⁿ} f(a)1_a(x)`. After simplification, `f(x) = ∑_{S⊆[n]} c_S x_S` (6.2), where `x_S = ∏_{i∈S}xᵢ` and `c_S∈𝔽₂`; this is the 2-polynomial representation (6.3). For three-bit parity, interpolation simplifies as in (6.4): `x₁+x₂+x₃−2(x₁x₂+x₁x₃+x₂x₃)+4x₁x₂x₃ = x₁+x₂+x₃` over `𝔽₂`.

<a id="pdf-ffbe9c7b3306-p149-b002"></a>
<!-- pdf-source: page=149; block=2; confidence=0.99 -->
**Proposition 6.18.** Every `f:𝔽₂ⁿ→𝔽₂` has a unique 2-polynomial representation of the form (6.3).

<a id="pdf-ffbe9c7b3306-p149-b003"></a>
<!-- pdf-source: page=149; block=3; confidence=0.99 -->
**Example 6.19.** `AND_n(x)=x₁⋯xₙ`; the inner product mod 2 is `IP₂ₙ(x₁,…,xₙ,y₁,…,yₙ)=∑_{i=1}ⁿxᵢyᵢ`, a degree-2 polynomial.

<a id="pdf-ffbe9c7b3306-p149-b004"></a>
<!-- pdf-source: page=149; block=4; confidence=0.99 -->
**Definition 6.20.** The 2-degree `deg₂(f)` of a Boolean function is the degree of its unique 2-polynomial representation. The notation `deg(f)` is reserved for the degree of its Fourier expansion.

<a id="pdf-ffbe9c7b3306-p149-b005"></a>
<!-- pdf-source: page=149; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p149-b006"></a>
<!-- pdf-source: page=149; block=6; confidence=0.99 -->
**Corollary 6.22.** `deg₂(f)=n` if and only if `f(x)=True` on an odd number of inputs.

<a id="pdf-ffbe9c7b3306-p149-b007"></a>
<!-- pdf-source: page=149; block=7; confidence=0.98 -->
Proposition 6.21 is deferred to Exercise 6.10; the corollary is its case `S=[n]`. The top-degree coefficient can also be read from the interpolation formula (6.1)–(6.2).

<a id="pdf-ffbe9c7b3306-p150-b001"></a>
<!-- pdf-source: page=150; block=1; confidence=0.99 -->
If \(p(x)\) is the Fourier expansion of a Boolean function in the \(\pm1\) encoding, then \(q(x)=\frac12-\frac12p(1-2x_1,\ldots,1-2x_n)\) is its multilinear representation in the \(0,1\) encoding. Reducing the integer coefficients of \(q\) modulo 2 gives the \(\mathbb F_2\)-polynomial representation.

<a id="pdf-ffbe9c7b3306-p150-b002"></a>
<!-- pdf-source: page=150; block=2; confidence=0.99 -->
**Proposition 6.23.** For `f:{−1,1}ⁿ→{−1,1}`, `deg₂(f) ≤ deg(f)`.

<a id="pdf-ffbe9c7b3306-p150-b003"></a>
<!-- pdf-source: page=150; block=3; confidence=0.98 -->
If `f` is `k`-resilient (`f̂(S)=0` for `|S|≤k<n`) and `g=χ_[n]f`, then `ĝ(S)=f̂([n]\S)` and `deg(g)≤n−k−1`. Proposition 6.23 gives `deg₂(g)≤n−k−1`; in the `0/1` encoding `g=x₁+⋯+xₙ+f`, so `deg₂(f)=deg₂(g)` unless `f` is parity or its negation.

<a id="pdf-ffbe9c7b3306-p150-b004"></a>
<!-- pdf-source: page=150; block=4; confidence=0.99 -->
**Proposition 6.24.** If `f:{−1,1}ⁿ→{−1,1}` is `k`-resilient with `k<n−1`, then `deg₂(f)≤n−k−1`.

<a id="pdf-ffbe9c7b3306-p150-b005"></a>
<!-- pdf-source: page=150; block=5; confidence=0.98 -->
**Siegenthaler’s Theorem.** Proposition 6.24 holds; moreover, if `f` is only `k`th-order correlation immune, then `deg₂(f)≤n−k` for `k<n`.

<a id="pdf-ffbe9c7b3306-p150-b006"></a>
<!-- pdf-source: page=150; block=6; confidence=0.99 -->
**Proof.** Choose a maximal-degree monomial `x_J` in the 2-polynomial of `f`, with degree `d=deg₂(f)`. Assume `d>1`, since otherwise the result is immediate. The proof continues beyond the supplied page.

<a id="pdf-ffbe9c7b3306-p151-b001"></a>
<!-- pdf-source: page=151; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p151-b002"></a>
<!-- pdf-source: page=151; block=2; confidence=0.99 -->
**Theorem 6.25.** If \(f:\{-1,1\}^n\to\{-1,1\}\) is \(k\)th-order correlation immune but not \(k\)-resilient (equivalently, \(\mathbb E[f]\ne0\)), then \(k+1\le \frac{2}{3}n\).

<a id="pdf-ffbe9c7b3306-p151-b003"></a>
<!-- pdf-source: page=151; block=3; confidence=0.97 -->
The proof of Theorem 6.25 is assigned as Exercise 6.14 and uses the Fourier expansion; the bounds in this theorem and Siegenthaler's theorem can be sharp (Exercise 6.15).

<a id="pdf-ffbe9c7b3306-p151-b004"></a>
<!-- pdf-source: page=151; block=4; confidence=0.99 -->
Section 6.3 introduces constructions of Boolean functions with pseudorandomness properties, beginning with bent functions.

<a id="pdf-ffbe9c7b3306-p151-b005"></a>
<!-- pdf-source: page=151; block=5; confidence=0.94 -->
**Definition 6.26.** For even \(n\), a function \(f:\{-1,1\}^n\to\{-1,1\}\) is bent if \(|\widehat f(\gamma)|=2^{-n/2}\) for every \(\gamma\in\{0,1\}^n\).

<a id="pdf-ffbe9c7b3306-p151-b006"></a>
<!-- pdf-source: page=151; block=6; confidence=0.99 -->
The inner-product-mod-2 function is \(\mathrm{IP}_n(x)=\chi(x_1x_{n/2+1}+\cdots+x_{n/2}x_n)\). For \(n=2\), it is \(\mathrm{AND}_2\), with real multilinear representation \(\frac12+\frac12x_1+\frac12x_2-\frac12x_1x_2\).

<a id="pdf-ffbe9c7b3306-p152-b001"></a>
<!-- pdf-source: page=152; block=1; confidence=0.99 -->
**Proposition 6.27.** If \(f:\{-1,1\}^n\to\{-1,1\}\) and \(g:\{-1,1\}^{n'}\to\{-1,1\}\) are bent, then their product on disjoint inputs, \((f\oplus g)(x,x')=f(x)g(x')\), is bent.

<a id="pdf-ffbe9c7b3306-p152-b002"></a>
<!-- pdf-source: page=152; block=2; confidence=0.99 -->
The complete quadratic function is \(\mathrm{CQ}_n(x)=\chi(\sum_{1\le i<j\le n}x_ix_j)\); the text relates it to the inner-product example via Proposition 6.28.

<a id="pdf-ffbe9c7b3306-p152-b003"></a>
<!-- pdf-source: page=152; block=3; confidence=0.95 -->
**Proposition 6.28.** If \(f:\{-1,1\}^n\to\{-1,1\}\) is bent, then \(\pm\chi_\gamma f\) is bent for every \(\gamma\in\{0,1\}^n\), and \(f\circ M\) is bent for every invertible linear transformation \(M:\{0,1\}^n\to\{0,1\}^n\).

<a id="pdf-ffbe9c7b3306-p152-b004"></a>
<!-- pdf-source: page=152; block=4; confidence=0.95 -->
**Proof.** Negating \(f\) preserves bentness, and multiplying by a character or composing with an invertible linear map permutes its Fourier coefficients (Exercise 3.1), preserving their magnitudes.

<a id="pdf-ffbe9c7b3306-p152-b005"></a>
<!-- pdf-source: page=152; block=5; confidence=0.99 -->
For \(n=4\), \(\sum_{1\le i<j\le4}x_ix_j=(x_1+x_3)(x_2+x_3)+(x_1+x_2+x_3)x_4+x_3\) over \(\mathbb F_2\). Hence \(\mathrm{CQ}_4(x)=\mathrm{IP}_4(Mx)\chi_{(0,0,1,0)}(x)\), where \(M=\begin{bmatrix}1&0&1&0\\1&1&1&0\\0&1&1&0\\0&0&0&1\end{bmatrix}\) is invertible.

<a id="pdf-ffbe9c7b3306-p152-b006"></a>
<!-- pdf-source: page=152; block=6; confidence=0.99 -->
**Proposition 6.29.** For arbitrary \(g:\{-1,1\}^n\to\{-1,1\}\), the function \(f:\{-1,1\}^{2n}\to\{-1,1\}\) defined by \(f(x,y)=\mathrm{IP}_{2n}(x,y)g(y)\) is bent.

<a id="pdf-ffbe9c7b3306-p152-b007"></a>
<!-- pdf-source: page=152; block=7; confidence=0.92 -->
**Proof.** Regard \(y\in\{0,1\}^n\) and write \(\mathrm{IP}_{2n}(x,y)=\chi_y(x)\); index a frequency as \((\gamma_1,\gamma_2)\). Then \(\widehat f(\gamma)=\mathbb E_{x,y}[\chi_y(x)g(y)\chi_{(\gamma_1,\gamma_2)}(x,y)] =\mathbb E_y[g(y)\chi_{\gamma_2}(y)\mathbb E_x[\chi_{y+\gamma_1}(x)]]=2^{-n}g(\gamma_1)\chi_{\gamma_2}(\gamma_1)=\pm2^{-n}\), so every Fourier coefficient has the required magnitude.

<a id="pdf-ffbe9c7b3306-p152-b008"></a>
<!-- pdf-source: page=152; block=8; confidence=0.98 -->
An explicit \(\varepsilon\)-biased multiset of size \(2^\ell\) permits sampling from its induced density using only \(\ell\) random bits, motivating constructions for derandomization.

<a id="pdf-ffbe9c7b3306-p153-b001"></a>
<!-- pdf-source: page=153; block=1; confidence=0.94 -->
For \(\ell\ge1\), use a field \(\mathbb F_{2^\ell}\) with \(2^\ell\) elements and a linear encoding \(\mathrm{enc}:\mathbb F_{2^\ell}\to\{0,1\}^\ell\), satisfying \(\mathrm{enc}(0)=0\) and \(\mathrm{enc}(x+y)=\mathrm{enc}(x)+\mathrm{enc}(y)\). Its representation can be constructed explicitly in time \(2^{O(\ell)}\) (and the text notes a deterministic polynomial-\(\ell\) method).

<a id="pdf-ffbe9c7b3306-p153-b002"></a>
<!-- pdf-source: page=153; block=2; confidence=0.99 -->
**Theorem 6.30.** There is a deterministic algorithm that, given \(n\ge1\) and \(0<\varepsilon\le\frac12\), runs in \(\operatorname{poly}(n/\varepsilon)\) time and outputs a multiset \(A\subseteq\{0,1\}^n\) of size at most \(16(n/\varepsilon)^2\) such that its induced density \(\varphi_A\) is \(\varepsilon\)-biased.

<a id="pdf-ffbe9c7b3306-p153-b003"></a>
<!-- pdf-source: page=153; block=3; confidence=0.97 -->
**Proof.** First construct a set of size \((n/\varepsilon)^2\) in the case \(\varepsilon=2^{-t}\) and \(n=2^{\ell-t}\), with integral powers as assumed. Define a distribution by sampling independent uniform \(r,s\in\mathbb F_{2^\ell}\), using \(2\ell\) random bits, and setting \(y_i=\langle\mathrm{enc}(r^i),\mathrm{enc}(s)\rangle\) for \(i\in[n]\), with the inner product over \(\mathbb F_2\). The multiset of all \(2^{2\ell}=(n/\varepsilon)^2\) outcomes is deterministically generable in polynomial time.

<a id="pdf-ffbe9c7b3306-p153-b004"></a>
<!-- pdf-source: page=153; block=4; confidence=0.97 -->
For nonzero \(\gamma\in\mathbb F_2^n\), let \(p_\gamma(a)=\sum_{i=1}^n\gamma_i a^i\). Then equation (6.5) averages over \(r\) and \(s\); the inner character expectation is 1 when \(p_\gamma(r)=0\) and 0 otherwise. Since \(p_\gamma\) is nonzero of degree at most \(n\), it has at most \(n\) roots. Thus \(0\le\mathbb E[\chi_\gamma(y)]\le n/2^\ell=2^{-t}=\varepsilon\).

<a id="pdf-ffbe9c7b3306-p154-b001"></a>
<!-- pdf-source: page=154; block=1; confidence=0.99 -->
The theorem’s bound is close to optimal; see Exercise 6.24 and the chapter notes.

<a id="pdf-ffbe9c7b3306-p154-b002"></a>
<!-- pdf-source: page=154; block=2; confidence=0.97 -->
A distribution may remain useful for randomized algorithms when every subset of at most $k$ random bits is independent. This motivates small sets $A\subseteq\mathbb F_2^n$ whose density $\phi_A$ is $k$-wise independent, equivalently $(0,k)$-regular. Known constructions can take $A$ to be a linear subspace.

<a id="pdf-ffbe9c7b3306-p154-b003"></a>
<!-- pdf-source: page=154; block=3; confidence=0.99 -->
**Proposition 6.31.** Let $H$ be an $m\times n$ matrix over $\mathbb F_2$, and let $A\leq\mathbb F_2^n$ be the span of the rows of $H$. Then $\phi_A$ is $k$-wise independent if and only if every sum of between one and $k$ columns of $H$ is nonzero in $\mathbb F_2^m$.

<a id="pdf-ffbe9c7b3306-p154-b004"></a>
<!-- pdf-source: page=154; block=4; confidence=0.98 -->
**Proof.** By Proposition 3.11, $\phi_A=\sum_{\gamma\in A^\perp}\chi_\gamma$. Thus $\phi_A$ is $k$-wise independent exactly when every nonzero $\gamma\in A^\perp$ has $|\gamma|>k$. Since $\gamma\in A^\perp$ iff $H\gamma=0$, this is equivalent to the stated column-sum condition.

<a id="pdf-ffbe9c7b3306-p154-b005"></a>
<!-- pdf-source: page=154; block=5; confidence=0.97 -->
A construction with $m$ on the order of $k\log n$ follows.

<a id="pdf-ffbe9c7b3306-p154-b006"></a>
<!-- pdf-source: page=154; block=6; confidence=0.98 -->
**Theorem 6.32.** Let $k,\ell\in\mathbb Z_{>0}$ and suppose $n=2^\ell\geq k$. For $m=(k-1)\ell+1$, there exists $H\in\mathbb F_2^{m\times n}$ such that every sum of at most $k$ columns is nonzero in $\mathbb F_2^m$.

<a id="pdf-ffbe9c7b3306-p154-b007"></a>
<!-- pdf-source: page=154; block=7; confidence=0.95 -->
**Proof.** Enumerate the elements of the finite field $\mathbb F_{2^\ell}$ as $\alpha_1,\ldots,\alpha_n$. Form $H'\in\mathbb F_{2^\ell}^{k\times n}$ with column $j$ equal to $(1,\alpha_j,\alpha_j^2,\ldots,\alpha_j^{k-1})^T$. Any $k$ columns form a nonsingular Vandermonde matrix, so they are linearly independent. Consequently, every nonempty sum of at most $k$ columns of $H'$ is nonzero. Encode each entry $\alpha_j^i$ as a vector in $\mathbb F_2^\ell$ using a linear map $\operatorname{enc}$, and stack these encodings to form a column of $H\in\mathbb F_2^{m\times n}$. Linearity preserves the nonzero-sum property.

<a id="pdf-ffbe9c7b3306-p154-b008"></a>
<!-- pdf-source: page=154; block=8; confidence=0.97 -->
**Corollary 6.33.** There is a deterministic algorithm which, given integers $1\leq k\leq n$, runs in time $\operatorname{poly}(nk)$ and outputs a subspace $A\leq\mathbb F_2^n$ of cardinality at most $2k n^{k-1}$ such that $\phi_A$ is $k$-wise independent.

<a id="pdf-ffbe9c7b3306-p155-b001"></a>
<!-- pdf-source: page=155; block=1; confidence=0.96 -->
**Proof.** It suffices to treat $n=2^\ell$, obtaining a set of size at most $2^{(k-1)\ell+1}=2n^{k-1}$. Construct $H$ as in Theorem 6.32 and let $A$ be its row span. Proposition 6.31 gives the $k$-wise independence.

<a id="pdf-ffbe9c7b3306-p155-b002"></a>
<!-- pdf-source: page=155; block=2; confidence=0.95 -->
For fixed $k$, the $O(n^{k-1})$ size is near optimal; bounds of order $n^{\lfloor k/2\rfloor}$ are achievable and necessary up to constants (Exercises 6.27–6.28).

<a id="pdf-ffbe9c7b3306-p155-b003"></a>
<!-- pdf-source: page=155; block=3; confidence=0.98 -->
An $\varepsilon$-biased distribution supported on a suitable $k$-wise independent subspace yields an $(\varepsilon,k)$-wise independent distribution.

<a id="pdf-ffbe9c7b3306-p155-b004"></a>
<!-- pdf-source: page=155; block=4; confidence=0.98 -->
**Lemma 6.34.** Suppose $H\in\mathbb F_2^{m\times n}$ has the property that every sum of one through $k$ columns is nonzero in $\mathbb F_2^m$. Let $\phi$ be an $\varepsilon$-biased density on $\mathbb F_2^m$. Draw $y\sim\phi$ and set $z=y^T H\in\mathbb F_2^n$. Then the distribution of $z$ is $(\varepsilon,k)$-wise independent.

<a id="pdf-ffbe9c7b3306-p155-b005"></a>
<!-- pdf-source: page=155; block=5; confidence=0.98 -->
**Proof.** For any $\gamma\in\mathbb F_2^n$ with $0<|\gamma|\leq k$, the hypothesis gives $H\gamma\neq0$. Hence $\left|\mathbb E[\chi_\gamma(z)]\right|=\left|\mathbb E_{y\sim\phi}[(-1)^{y^T H\gamma}]\right|\leq\varepsilon$ by the bias bound.

<a id="pdf-ffbe9c7b3306-p155-b006"></a>
<!-- pdf-source: page=155; block=6; confidence=0.96 -->
Combining Theorems 6.30 and 6.32 gives an efficiently constructible $(\varepsilon,k)$-wise independent distribution sampleable using $O(\log k+\log\log n+\log(1/\varepsilon))$ independent random bits.

<a id="pdf-ffbe9c7b3306-p155-b007"></a>
<!-- pdf-source: page=155; block=7; confidence=0.97 -->
**Theorem 6.35.** There is a deterministic algorithm which, given \(1\le k\le n\) and \(0<\varepsilon\le1/2\), runs in time \(\operatorname{poly}(n/\varepsilon)\) and outputs a multiset \(A\subseteq\mathbb F_2^n\) of cardinality \(O(k\log(n)/\varepsilon)^2\), a power of 2, such that \(\varphi_A\) is \((\varepsilon,k)\)-wise independent.

<a id="pdf-ffbe9c7b3306-p155-b008"></a>
<!-- pdf-source: page=155; block=8; confidence=0.99 -->
## 6.4. Applications in learning and testing

<a id="pdf-ffbe9c7b3306-p155-b009"></a>
<!-- pdf-source: page=155; block=9; confidence=0.98 -->
This section presents applications of pseudorandomness, beginning with the open problem of learning juntas from random examples.

<a id="pdf-ffbe9c7b3306-p155-b010"></a>
<!-- pdf-source: page=155; block=10; confidence=0.96 -->
Let $\mathcal C=\{f:\mathbb F_2^n\to\{0,1\}\mid f\text{ is a }k\text{-junta}\}$, with $k\leq O(\log n)$. Query access permits exact learning in polynomial time (Exercise 3.37(a)), but random-example learning has the $nk\cdot\operatorname{poly}(n)$-time Low-Degree Algorithm bound (Theorem 3.36), superpolynomial when $k=\omega(1)$. Similar barriers arise for depth-$k$ decision trees and polynomial-size DNFs/CNFs; learning such larger classes from examples would require progress on $O(\log n)$-juntas.

<a id="pdf-ffbe9c7b3306-p156-b001"></a>
<!-- pdf-source: page=156; block=1; confidence=0.98 -->
Whether $\omega(1)$-juntas can be learned from random examples in polynomial time remains open; the next result improves the known $n^k$-time bound.

<a id="pdf-ffbe9c7b3306-p156-b002"></a>
<!-- pdf-source: page=156; block=2; confidence=0.98 -->
**Theorem 6.36.** For $k\leq O(\log n)$, the class of Boolean $k$-juntas on $\mathbb F_2^n$ can be exactly learned from random examples in time $n^{(3/4)k}\operatorname{poly}(n)$.

<a id="pdf-ffbe9c7b3306-p156-b003"></a>
<!-- pdf-source: page=156; block=3; confidence=0.97 -->
The exponent $3/4$ may be replaced by $\omega/(\omega+1)$ for any exponent $\omega$ such that $n\times n$ matrices can be multiplied in time $O(n^\omega)$.

<a id="pdf-ffbe9c7b3306-p156-b004"></a>
<!-- pdf-source: page=156; block=4; confidence=0.97 -->
The proof reduces junta learning to finding one relevant coordinate (Definition 2.18); this reduction is deferred to Exercise 6.31.

<a id="pdf-ffbe9c7b3306-p156-b005"></a>
<!-- pdf-source: page=156; block=5; confidence=0.98 -->
**Lemma 6.37.** Theorem 6.36 follows if there is an algorithm that, given random examples of a nonconstant $k$-junta $f:\mathbb F_2^n\to\{0,1\}$, finds a relevant coordinate with probability at least $1-\delta$ in time $n^{(3/4)k}\operatorname{poly}(n)\log(1/\delta)$.

<a id="pdf-ffbe9c7b3306-p156-b006"></a>
<!-- pdf-source: page=156; block=6; confidence=0.96 -->
**Proof.** Assume random-example access to a nonconstant $k$-junta $f$. Estimate all Fourier coefficients $\widehat f(S)$ for $1\leq |S|\leq d$, where $d\leq k$ is chosen later. By Proposition 3.30, all estimates are within $(1/3)2^{-k}$ of their true values, except with probability at most $\delta/2$, using time $n^d\operatorname{poly}(n)\log(1/\delta)$. Since each coefficient of a $k$-junta is either zero or has magnitude at least $2^{-k}$, these estimates identify the nonzero coefficients exactly. Any coordinate in a set $S$ with $\widehat f(S)\neq0$ is relevant (Exercise 2.11). Thus, if such an $S$ occurs for $1\leq|S|\leq d$, the algorithm finds a relevant coordinate within this time and failure probability.

<a id="pdf-ffbe9c7b3306-p156-b007"></a>
<!-- pdf-source: page=156; block=7; confidence=0.94 -->
If all Fourier coefficients of sizes 1 through \(d\) vanish, then \(f\) is \(d\)th-order correlation immune. Siegenthaler’s theorem gives \(\deg_{\mathbb F_2}(f)\le k-d\). The polynomial learner uses time \(O(n)^{3(k-d)}\operatorname{poly}(n)\log(1/delta)\).

<a id="pdf-ffbe9c7b3306-p156-b008"></a>
<!-- pdf-source: page=156; block=8; confidence=0.98 -->
Choose \(d=\lceil3k/4\rceil\) to balance the two running times. A relevant coordinate is found with failure probability at most \(\delta\), in time \(n^{(3/4)k}\operatorname{poly}(n)\log(1/\delta)\). This proves Theorem 6.36.

<a id="pdf-ffbe9c7b3306-p157-b001"></a>
<!-- pdf-source: page=157; block=1; confidence=1.00 -->
## 6.4. Applications in learning and testing

<a id="pdf-ffbe9c7b3306-p157-b002"></a>
<!-- pdf-source: page=157; block=2; confidence=0.99 -->
An ε-biased distribution gives deterministic estimates for functions with small Fourier 1-norm, beginning with their means.

<a id="pdf-ffbe9c7b3306-p157-b003"></a>
<!-- pdf-source: page=157; block=3; confidence=1.00 -->
**Lemma 6.38.** If \(f:\{-1,1\}^n\to\mathbb R\) and \(\varphi\) is an \(\varepsilon\)-biased density, then \(\left|\mathbb E_{x\sim\varphi}[f(x)]-\mathbb E[f]\right|\le\|\widehat f\|_1\varepsilon\).

<a id="pdf-ffbe9c7b3306-p157-b004"></a>
<!-- pdf-source: page=157; block=4; confidence=0.91 -->
**Proof.** By Plancherel, `𝔼_{x∼φ}[f(x)] = ⟨φ,f⟩ = f̂(∅) + ∑_{S≠∅} φ̂(S)f̂(S)`. Since `𝔼[f]=f̂(∅)` and `|φ̂(S)|≤ε` for nonempty `S`, the difference is at most `∑_{S≠∅}|φ̂(S)||f̂(S)| ≤ ε∑_{S≠∅}|f̂(S)| ≤ ε‖f̂‖₁`.

<a id="pdf-ffbe9c7b3306-p157-b005"></a>
<!-- pdf-source: page=157; block=5; confidence=0.86 -->
Applying the mean estimate to `f²` and using `‖(f²)^̂‖₁ ≤ ‖f̂‖₁²` yields the following corollary.

<a id="pdf-ffbe9c7b3306-p157-b006"></a>
<!-- pdf-source: page=157; block=6; confidence=1.00 -->
**Corollary 6.39.** For real-valued \(f\) and an \(\varepsilon\)-biased density \(\varphi\), \(\left|\mathbb E_{x\sim\varphi}[f(x)^2]-\mathbb E[f^2]\right|\le\|\widehat f\|_1^2\varepsilon\).

<a id="pdf-ffbe9c7b3306-p157-b007"></a>
<!-- pdf-source: page=157; block=7; confidence=0.98 -->
The mean estimate gives a deterministic version of the algorithm for estimating a specified Fourier coefficient.

<a id="pdf-ffbe9c7b3306-p157-b008"></a>
<!-- pdf-source: page=157; block=8; confidence=1.00 -->
**Proposition 6.40.** A deterministic algorithm, given query access to \(f:\{-1,1\}^n\to\mathbb R\), \(U\subseteq[n]\), \(0<\varepsilon\le1/2\), and \(s\ge1\), estimates \(\widehat f(U)\) to additive error at most \(\varepsilon\), assuming \(\|\widehat f\|_1\le s\), in time \(\operatorname{poly}(n,s,1/\varepsilon)\).

<a id="pdf-ffbe9c7b3306-p157-b009"></a>
<!-- pdf-source: page=157; block=9; confidence=0.83 -->
**Proof.** It suffices to estimate the empty-set coefficient: for general `U`, simulate queries to `fχ_U`, whose empty-set coefficient is `f̂(U)`. Use Theorem 6.30 to construct an `(ε/s)`-biased density uniform on a multiset of size `O(n²s²/ε²)`, enumerate it, and output `𝔼_{x∼φ}[f(x)]`. The runtime is polynomial in `n,s,1/ε`, and Lemma 6.38 gives error at most `ε`. ∎

<a id="pdf-ffbe9c7b3306-p158-b001"></a>
<!-- pdf-source: page=158; block=1; confidence=0.98 -->
The other ingredient in Goldreich–Levin estimates Fourier weight on a set of coefficients.

<a id="pdf-ffbe9c7b3306-p158-b002"></a>
<!-- pdf-source: page=158; block=2; confidence=0.84 -->
For `S ⊆ J ⊆ [n]`, `W_{S|J}[f] := ∑_{T⊆J} f̂(S∪T)² = 𝔼_{z∼{−1,1}^J}[ f̂_{J|z}(S)² ]`. For each `z`, Proposition 6.40 estimates the restricted coefficient `f̂_{J|z}(S)`; the restricted function retains Fourier 1-norm at most `s` when `‖f̂‖₁≤s`.

<a id="pdf-ffbe9c7b3306-p158-b003"></a>
<!-- pdf-source: page=158; block=3; confidence=0.87 -->
**Proposition 6.41.** There is a deterministic algorithm which, given query access to `f : {−1,1}ⁿ → {−1,1}`, `S ⊆ J ⊆ [n]`, `0<ε≤1/2`, and `s≥1`, outputs `β` satisfying `|W_{S|J}[f]−β|≤ε`, provided `‖f̂‖₁≤s`. Its running time is `poly(n,s,1/ε)`.

<a id="pdf-ffbe9c7b3306-p158-b004"></a>
<!-- pdf-source: page=158; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p158-b005"></a>
<!-- pdf-source: page=158; block=5; confidence=0.98 -->
Propositions 6.40 and 6.41 provide the ingredients to derandomize Goldreich–Levin and its learning consequence.

<a id="pdf-ffbe9c7b3306-p158-b006"></a>
<!-- pdf-source: page=158; block=6; confidence=0.94 -->
**Theorem 6.42.** Let `C={f:{−1,1}ⁿ→{−1,1} : ‖f̂‖₁≤s}`. Then `C` is deterministically learnable from queries with error `ε` in time `poly(n,s,1/ε)`.

<a id="pdf-ffbe9c7b3306-p159-b001"></a>
<!-- pdf-source: page=159; block=1; confidence=0.90 -->
Fourier sparsity at most `s` implies Fourier 1-norm at most `s`; the cited exercise then yields exact deterministic learning for the following class. Decision trees of size at most `s` and depth at most `k` are examples for the respective learning results.

<a id="pdf-ffbe9c7b3306-p159-b002"></a>
<!-- pdf-source: page=159; block=2; confidence=0.87 -->
**Theorem 6.43.** The class `C={f:{−1,1}ⁿ→{−1,1} : sparsity(f̂)≤2^{O(k)}}` is deterministically learnable exactly, with zero error, from queries in time `poly(n,2^k)`.

<a id="pdf-ffbe9c7b3306-p159-b003"></a>
<!-- pdf-source: page=159; block=3; confidence=0.99 -->
The derandomized BLR test samples uniform \(x\in\mathbb F_2^n\) and \(y\sim\varphi\), queries \(f(x),f(y),f(x+y)\), and accepts iff \(f(x)+f(y)=f(x+y)\). It uses \(n+O(\log(n/\varepsilon))\) random bits. Linear functions pass with probability 1; the approximate converse is to closeness to an affine function.

<a id="pdf-ffbe9c7b3306-p159-b004"></a>
<!-- pdf-source: page=159; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p159-b005"></a>
<!-- pdf-source: page=159; block=5; confidence=0.82 -->
**Remark 6.45.** The bound is informative near both `θ=0` and `θ=1`; for `θ=1−2δ`, acceptance probability `1−δ` implies distance nearly `δ` from an affine function when `ε` is much smaller than `δ`.

<a id="pdf-ffbe9c7b3306-p159-b006"></a>
<!-- pdf-source: page=159; block=6; confidence=0.81 -->
**Proof.** Encode the Boolean outputs by signs in `{−1,1}`. The initial BLR analysis rewrites the acceptance hypothesis as

`θ ≤ 𝔼_{x∼uniform, y∼φ}[f(x)f(y)f(x+y)] = 𝔼_{y∼φ}[f(y)(f*f)(y)]`.

<a id="pdf-ffbe9c7b3306-p160-b001"></a>
<!-- pdf-source: page=160; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p160-b002"></a>
<!-- pdf-source: page=160; block=2; confidence=0.99 -->
The section studies how small-bias distributions fool low-degree functions.

<a id="pdf-ffbe9c7b3306-p160-b003"></a>
<!-- pdf-source: page=160; block=3; confidence=0.98 -->
**Definition 6.46.** For a density \(\phi:\mathbb F_2^n\to\mathbb R_{\ge0}\) and a class \(\mathcal C\) of functions on \(\mathbb F_2^n\), say that \(\phi\) \(\varepsilon\)-fools \(\mathcal C\) if every \(f\in\mathcal C\) satisfies \(\left|\mathbb E_{y\sim\phi}[f(y)]-\mathbb E_{x\sim\mathbb F_2^n}[f(x)]\right|\le\varepsilon\).

<a id="pdf-ffbe9c7b3306-p160-b004"></a>
<!-- pdf-source: page=160; block=4; confidence=0.95 -->
Theorem 6.30 gives an \(\varepsilon\)-fooling distribution for degree-one functions using \(O(\log(n/\varepsilon))\) independent random bits. Small bias alone does not extend to degree two: the uniform distribution on the support of \(IP_n\) is roughly \(2^{-n/2}\)-biased, yet has expectation 1 on \(IP_n\), whereas the uniform-cube expectation is approximately \(1/2\).

<a id="pdf-ffbe9c7b3306-p161-b001"></a>
<!-- pdf-source: page=161; block=1; confidence=0.95 -->
Earlier constructions used \(\exp(O(d\log(n/d)+\log(1/\varepsilon)))\) random bits; later bounds improved the degree-two and degree-three cases. Lovett showed that convolution of \(2d\) independent samples from an \(\varepsilon\)-biased density fools degree-\(d\) functions with error \(O(\varepsilon^{1/4d})\).

<a id="pdf-ffbe9c7b3306-p161-b002"></a>
<!-- pdf-source: page=161; block=2; confidence=0.98 -->
**Viola’s Theorem.** Let \(\phi\) be an \(\varepsilon\)-biased density on \(\mathbb F_2^n\), with \(0\le\varepsilon\le1\), and let \(d\ge1\). Define \(\varepsilon_d=9\varepsilon^{1/2^{d-1}}\). Then every \(f:\mathbb F_2^n\to\{-1,1\}\) of degree at most \(d\) satisfies
\[
\left|\mathbb E_{y^{(1)},\ldots,y^{(d)}\sim\phi}\left[f\left(y^{(1)}+\cdots+y^{(d)}\right)\right]-\mathbb E_{x\sim\mathbb F_2^n}[f(x)]\right|\le 9\varepsilon^{1/2^{d-1}}.
\]
Equivalently, the \(d\)-fold convolution \(\phi^{*d}\) \(\varepsilon_d\)-fools degree-at-most-\(d\) functions. Combined with Theorem 6.30, this yields a stated randomness bound of \(O(d\log n)+O(d2^d\log(1/\varepsilon))\) bits.

<a id="pdf-ffbe9c7b3306-p161-b003"></a>
<!-- pdf-source: page=161; block=3; confidence=0.99 -->
The proof inducts on degree, reducing degree by taking directional derivatives.

<a id="pdf-ffbe9c7b3306-p161-b004"></a>
<!-- pdf-source: page=161; block=4; confidence=0.99 -->
**Definition 6.48.** For \(f:\mathbb F_2^n\to\mathbb F_2\) and \(y\in\mathbb F_2^n\), define \(\Delta_yf(x)=f(x+y)-f(x)\); over \(\mathbb F_2\), subtraction equals addition, so this is also \(f(x+y)+f(x)\).

<a id="pdf-ffbe9c7b3306-p161-b005"></a>
<!-- pdf-source: page=161; block=5; confidence=0.99 -->
**Fact 6.49.** For every \(f:\mathbb F_2^n\to\mathbb F_2\) and \(y\in\mathbb F_2^n\), \(\deg(\Delta_yf)\le\deg(f)-1\).

<a id="pdf-ffbe9c7b3306-p162-b001"></a>
<!-- pdf-source: page=162; block=1; confidence=0.99 -->
**Proposition 6.50.** If \(f:\mathbb F_2^n\to\mathbb F_2\) has degree \(d\), then for any \(y,y'\in\mathbb F_2^n\), the function \(g(x)=f(x+y)-f(x+y')\) has degree at most \(d-1\).

<a id="pdf-ffbe9c7b3306-p162-b002"></a>
<!-- pdf-source: page=162; block=2; confidence=0.99 -->
**Proof.** In the polynomial representation, a degree-\(d\) monomial \(x^S\) becomes \((x+y)^S-(x+y')^S\); the degree-\(d\) terms cancel, leaving degree at most \(d-1\).

<a id="pdf-ffbe9c7b3306-p162-b003"></a>
<!-- pdf-source: page=162; block=3; confidence=0.99 -->
**Proof.** Induct on \(d\). The base case \(d=1\) follows from \(\varepsilon\)-bias. For degree \(d+1\), split according to whether \((\mathbb E f)^2>\varepsilon_d\) or \((\mathbb E f)^2\le\varepsilon_d\).

<a id="pdf-ffbe9c7b3306-p162-b004"></a>
<!-- pdf-source: page=162; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p162-b005"></a>
<!-- pdf-source: page=162; block=5; confidence=0.90 -->
If \((\mathbb E f)^2\le\varepsilon_d\), the proof aims to show \(\mathbb E_{w\sim\phi^{*(d+1)}}[f(w)]^2\) is also small. It writes this as an expectation over \(z\sim\phi^{*d}\) of \((\mathbb E_{y\sim\phi}f(z+y))^2\), then applies Cauchy–Schwarz to bound it by \(\mathbb E_{y,y'\sim\phi}\mathbb E_{z\sim\phi^{*d}}[f(z+y)f(z+y')]\).

<a id="pdf-ffbe9c7b3306-p163-b001"></a>
<!-- pdf-source: page=163; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p163-b002"></a>
<!-- pdf-source: page=163; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p163-b003"></a>
<!-- pdf-source: page=163; block=3; confidence=0.99 -->
The section presents exercises 6.1–6.3.

<a id="pdf-ffbe9c7b3306-p163-b004"></a>
<!-- pdf-source: page=163; block=4; confidence=0.82 -->
For $f$ as in Proposition 6.1, compute $\operatorname{Var}[\widehat f(S)]$ for every $S\subseteq[n]$.

<a id="pdf-ffbe9c7b3306-p163-b005"></a>
<!-- pdf-source: page=163; block=5; confidence=0.99 -->
Prove Fact 6.8.

<a id="pdf-ffbe9c7b3306-p163-b006"></a>
<!-- pdf-source: page=163; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p164-b001"></a>
<!-- pdf-source: page=164; block=1; confidence=0.78 -->
If $\phi:\{\pm1\}^n\to\mathbb R_{\ge0}$ is an $\varepsilon$-biased density, prove that for each positive integer $d$, its $d$-fold convolution $\phi^{*d}$ is $\varepsilon^d$-biased.

<a id="pdf-ffbe9c7b3306-p164-b002"></a>
<!-- pdf-source: page=164; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p164-b003"></a>
<!-- pdf-source: page=164; block=3; confidence=0.86 -->
Let $(J,J^c)$ partition $[n]$. (a) For uniform random $z\in\{\pm1\}^J$, express $\operatorname{Var}_z[\mathbb E[f\mid z]]$ using the Fourier coefficients of $f$ (hint: Corollary 3.22). (b) Use this identity and the probabilistic method to give another proof of the second assertion of Proposition 6.12.

<a id="pdf-ffbe9c7b3306-p164-b004"></a>
<!-- pdf-source: page=164; block=4; confidence=0.74 -->
For the density associated with the uniform distribution on the support of $\operatorname{IP}_n:\{0,1\}^n\to\{0,1\}$, prove that it is $\varepsilon$-biased for $\varepsilon=2^{-n/2}/(1-2^{-n/2})$, but not for any smaller bias parameter.

<a id="pdf-ffbe9c7b3306-p164-b005"></a>
<!-- pdf-source: page=164; block=5; confidence=0.99 -->
Prove Proposition 6.13.

<a id="pdf-ffbe9c7b3306-p164-b006"></a>
<!-- pdf-source: page=164; block=6; confidence=0.84 -->
Find the $\mathbb F_2$-polynomial representation of $\operatorname{Equ}_n:\{0,1\}^n\to\{0,1\}$, where the output is $1$ exactly when all input bits are equal.

<a id="pdf-ffbe9c7b3306-p164-b007"></a>
<!-- pdf-source: page=164; block=7; confidence=0.94 -->
Let $f:\{0,1\}^n\to\mathbb R$ have unique multilinear representation $q(x)=\sum_{S\subseteq[n]}c_Sx_S$. (a) Prove Möbius inversion: $c_S=\sum_{R\subseteq S}(-1)^{|S|-|R|}f(R)$, identifying each subset with its indicator string. (b) Prove Proposition 6.21.

<a id="pdf-ffbe9c7b3306-p165-b001"></a>
<!-- pdf-source: page=165; block=1; confidence=0.83 -->
For nonzero $f:\{\pm1\}^n\to\mathbb F_2$ with $\deg_2(f)\le k$, prove $\Pr[f(x)\ne0]\ge2^{-k}$; use induction on $n$.

<a id="pdf-ffbe9c7b3306-p165-b002"></a>
<!-- pdf-source: page=165; block=2; confidence=0.89 -->
For Boolean $f:\{\pm1\}^n\to\{0,1\}$, (a) prove $\deg_2(f)\le\log_2(\operatorname{sparsity}(\widehat f))$, using Exercises 3.7 and 1.3 and Corollary 6.22; (b) if $\widehat f$ is $2^{-k}$-granular, prove the stronger bound $\deg_2(f)\le k$, using Exercise 3.32.

<a id="pdf-ffbe9c7b3306-p165-b003"></a>
<!-- pdf-source: page=165; block=3; confidence=0.89 -->
For bent $f:\{\pm1\}^n\to\{\pm1\}$ with $n>2$, prove $\deg_2(f)\le n/2$; Exercise 6.12(b) gives the weaker bound $n/2+1$.

<a id="pdf-ffbe9c7b3306-p165-b004"></a>
<!-- pdf-source: page=165; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p165-b005"></a>
<!-- pdf-source: page=165; block=5; confidence=0.78 -->
Explore sharpness of Siegenthaler’s theorem and Theorem 6.25: (a) for $k<n-1$, find a $k$-resilient Boolean function on $n$ bits with degree $n-k-1$; (b) for $n\ge3$, find a first-order correlation-immune Boolean function of degree $n-1$; (c) when $3\mid n$, find a biased Boolean function that is $(2n/3-1)$-st-order correlation immune.

<a id="pdf-ffbe9c7b3306-p165-b006"></a>
<!-- pdf-source: page=165; block=6; confidence=0.99 -->
Prove Proposition 6.27.

<a id="pdf-ffbe9c7b3306-p165-b007"></a>
<!-- pdf-source: page=165; block=7; confidence=0.97 -->
**Exercise 6.17.** If \(f:\mathbb F_2^n\to\{-1,1\}\) is bent, show that \(2^{n/2}\widehat f\) is also a bent function.

<a id="pdf-ffbe9c7b3306-p165-b008"></a>
<!-- pdf-source: page=165; block=8; confidence=0.95 -->
**Exercise 6.18.** For a permutation \(\pi\) on \(\mathbb F_2^n\), show that \(f(x,y)=\mathrm{IP}_{2n}(x,\pi(y))g(y)\) is bent.

<a id="pdf-ffbe9c7b3306-p165-b009"></a>
<!-- pdf-source: page=165; block=9; confidence=0.68 -->
Dickson’s theorem states that any degree-at-most-two polynomial $p:\mathbb F_2^n\to\mathbb F_2$ can be written $p(x)=\ell_0(x)+\sum_{j=1}^k\ell_j(x)\ell'_j(x)$ (6.8), where $\ell_0$ is affine and the $2k$ linear functions are linearly independent; $k$ is the rank of $p$. For even $n$, prove that $g(x)=\chi(p(x))$ is bent exactly when $k=n/2$, equivalently when $g$ comes from $\operatorname{IP}_n$ as in Proposition 6.28.

<a id="pdf-ffbe9c7b3306-p166-b001"></a>
<!-- pdf-source: page=166; block=1; confidence=1.00 -->
## 6. Pseudorandomness and 2-polynomials

<a id="pdf-ffbe9c7b3306-p166-b002"></a>
<!-- pdf-source: page=166; block=2; confidence=0.98 -->
Prove without Dickson’s theorem that the complete quadratic polynomial \(x\mapsto\sum_{1\le i<j\le n}x_ix_j\) has the representation in (6.8) with \(k=\lfloor n/2\rfloor\); use induction with separate parity cases.

<a id="pdf-ffbe9c7b3306-p166-b003"></a>
<!-- pdf-source: page=166; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p166-b004"></a>
<!-- pdf-source: page=166; block=4; confidence=0.97 -->
In Theorem 6.30, show that for any fixed \(r,s\), each bit \(y_i\) can be computed deterministically in time polynomial in \(\ell\).

<a id="pdf-ffbe9c7b3306-p166-b005"></a>
<!-- pdf-source: page=166; block=5; confidence=0.87 -->
(a) Modify Theorem 6.30’s construction to obtain a \((2^{-t}-2^{-\ell})\)-biased density, arranging that \(p_\gamma\) has degree at most \(n-1\). (b) For a basis \(v_1,\ldots,v_\ell\) of the \(2^\ell\)-element vector space over \(\mathbb F_2\), modify the construction to a density on \(\mathbb F_2^{n\ell}\) with \(y_{ij}=\langle\mathrm{enc}(v_jr_i),\mathrm{enc}(s)\rangle\); show it remains \(2^{-t}\)-biased.

<a id="pdf-ffbe9c7b3306-p166-b006"></a>
<!-- pdf-source: page=166; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p166-b007"></a>
<!-- pdf-source: page=166; block=7; confidence=0.94 -->
For verifying a proposed matrix product \(C'=AB\), (a) give an algorithm using \(n\) random bits and time \(O(n^2)\) that accepts if \(C'=AB\) and otherwise accepts with probability at most \(1/2\), using a random \(x\in\mathbb F_2^n\) to compare \(C'x\) and \(ABx\). (b) Reduce randomness to \(O(\log n)\), allowing false acceptance probability \(2/3\) while retaining time \(O(n^2)\); use the computation bound from Theorem 6.30.

<a id="pdf-ffbe9c7b3306-p166-b008"></a>
<!-- pdf-source: page=166; block=8; confidence=0.97 -->
For \(k=2\), simplify Theorem 6.32 and Corollary 6.33 and show that one may take \(m=\ell\).

<a id="pdf-ffbe9c7b3306-p167-b001"></a>
<!-- pdf-source: page=167; block=1; confidence=1.00 -->
## 6.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p167-b002"></a>
<!-- pdf-source: page=167; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p167-b003"></a>
<!-- pdf-source: page=167; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p167-b004"></a>
<!-- pdf-source: page=167; block=4; confidence=0.96 -->
If \(\mathcal C\) is closed under translations on \(\mathbb F_2^n\), and \(\psi\) is a density that \(\varepsilon\)-fools \(\mathcal C\), show that \(\psi*\varphi\) also \(\varepsilon\)-fools \(\mathcal C\) for every density \(\varphi\). Example: functions of degree at most \(d\).

<a id="pdf-ffbe9c7b3306-p167-b005"></a>
<!-- pdf-source: page=167; block=5; confidence=0.94 -->
For integer \(\ell\ge1\), generalize Exercise 3.43 to exactly learn degree-at-most-\(\ell\) polynomials \(p:\mathbb F_2^n\to\mathbb F_2\). (a) With \(m\ge C2^\ell(n^\ell+\log(1/\delta))\) independent uniform examples, prove with failure probability at most \(\delta\) that the only degree-at-most-\(\ell\) polynomial agreeing with \(p\) on all samples is \(p\). (b) Give a random-example learner with zero error and runtime \(O(n)^{3\ell}\), or \(O(n)^{\omega\ell}\) with matrix multiplication exponent \(\omega\). (c) Extend it to success probability at least \(1-\delta\) in time \(O(n)^{3\ell}\log(1/\delta)\).

<a id="pdf-ffbe9c7b3306-p167-b006"></a>
<!-- pdf-source: page=167; block=6; confidence=0.99 -->
Prove Lemma 6.37; its subparts continue on page 168.

<a id="pdf-ffbe9c7b3306-p168-b001"></a>
<!-- pdf-source: page=168; block=1; confidence=0.92 -->
(a) Given random examples from a \(k\)-junta \(f:\mathbb F_2^n\to\mathbb F_2\), give a learner running in \(\operatorname{poly}(n,2^k)\log(1/\delta)\) time that, with failure probability at most \(\delta\), determines whether \(f\) is constant and its value if so. (b) Given relevant-coordinate set \(P\) and assignment \(z\in\mathbb F_2^P\), obtain \(M\) independent random examples from the restricted \((k-|P|)\)-junta \(f_{P|z}\) in time \(\operatorname{poly}(n,2^k)M\log(1/\delta)\), except with probability at most \(\delta\). (c) Complete Lemma 6.37’s proof using a depth-\(k\) decision tree.

<a id="pdf-ffbe9c7b3306-p168-b002"></a>
<!-- pdf-source: page=168; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p168-b003"></a>
<!-- pdf-source: page=168; block=3; confidence=0.88 -->
Strengthen Theorem 6.44 by roughly a factor of 2 when acceptance is near 1: if \(f\) passes the Derandomized BLR Test with probability \(1-\delta\), show some \(\gamma^*\in\mathbb F_2^n\) satisfies \(|\widehat f(\gamma^*)|\ge\sqrt{(1-2\delta-\varepsilon)/(1-\varepsilon)}\).

<a id="pdf-ffbe9c7b3306-p168-b004"></a>
<!-- pdf-source: page=168; block=4; confidence=0.98 -->
**Definition.** For integer \(k\ge1\), functions \(f_s:\mathbb F_2^n\to\mathbb R\) indexed by \(s\in\{0,1\}^k\), define
\[
\langle(f_s)_s\rangle_{U^k}=\mathbb E_{x,y_1,\ldots,y_k}\prod_{s\in\{0,1\}^k} f_s\!\left(x+\sum_{i:s_i=1}y_i\right),
\]
where \(x,y_1,\ldots,y_k\) are independent uniform vectors. For \(f:\mathbb F_2^n\to\mathbb R\), define \(\|f\|_{U^k}=\langle(f,f,\ldots,f)\rangle_{U^k}^{1/2^k}\).

<a id="pdf-ffbe9c7b3306-p168-b005"></a>
<!-- pdf-source: page=168; block=5; confidence=0.98 -->
Verify \(\langle f_0,f_1\rangle_{U^1}=\mathbb E[f_0]\mathbb E[f_1]\), hence \(\|f\|_{U^1}^2=(\mathbb E f)^2\).

<a id="pdf-ffbe9c7b3306-p168-b006"></a>
<!-- pdf-source: page=168; block=6; confidence=0.95 -->
Verify \(\langle f_{00},f_{10},f_{01},f_{11}\rangle_{U^2}=\sum_{\gamma\in\mathbb F_2^n}\widehat f_{00}(\gamma)\widehat f_{10}(\gamma)\widehat f_{01}(\gamma)\widehat f_{11}(\gamma)\), hence \(\|f\|_{U^2}^4=\|\widehat f\|_4^4\).

<a id="pdf-ffbe9c7b3306-p168-b007"></a>
<!-- pdf-source: page=168; block=7; confidence=0.88 -->
**Claim.** Show
\[
\langle(f_s)_s\rangle_{U^k}=\mathbb E_{y_1,\ldots,y_{k-1}}\left[\mathbb E_x\prod_{s:s_k=0}f_s\!\left(x+\sum_{i:s_i=1}y_i\right)\;\mathbb E_{x'}\prod_{s:s_k=1}f_s\!\left(x'+\sum_{i:s_i=1}y_i\right)\right],\tag{6.9}
\]
where \(x'\) is independent uniform, as are \(x,y_1,\ldots,y_{k-1}\).

<a id="pdf-ffbe9c7b3306-p169-b001"></a>
<!-- pdf-source: page=169; block=1; confidence=1.00 -->
## 6.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p169-b002"></a>
<!-- pdf-source: page=169; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p169-b003"></a>
<!-- pdf-source: page=169; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p169-b004"></a>
<!-- pdf-source: page=169; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p169-b005"></a>
<!-- pdf-source: page=169; block=5; confidence=0.96 -->
**Exercise 6.34(g).** For fixed \(f:\mathbb F_2^n\to\mathbb R\), show \(\|f\|_{U^k}\le\|f\|_{U^{k+1}}\).

<a id="pdf-ffbe9c7b3306-p169-b006"></a>
<!-- pdf-source: page=169; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p169-b007"></a>
<!-- pdf-source: page=169; block=7; confidence=0.92 -->
Show that \(\|\cdot\|_{U^k}\) is a norm for every \(k\geq2\): if \(\|f\|_{U^k}=0\), then \(f=0\).

<a id="pdf-ffbe9c7b3306-p169-b008"></a>
<!-- pdf-source: page=169; block=8; confidence=0.82 -->
The 2-polynomial representation of a Boolean function is also called its algebraic normal form and is credited here to Zhegalkin (1927). The notion of \(\leq\)-regularity as pseudorandomness, and an equivalent combinatorial condition in Proposition 6.7, are attributed to Chung–Graham; related quasirandom graph ideas are attributed to Thomason and Chung–Graham–Wilson. Viewing functions with small stable influences as generic is traced to Kahn–Kalai–Linial and later hardness-of-approximation work.

<a id="pdf-ffbe9c7b3306-p169-b009"></a>
<!-- pdf-source: page=169; block=9; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p170-b001"></a>
<!-- pdf-source: page=170; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p170-b002"></a>
<!-- pdf-source: page=170; block=2; confidence=0.90 -->
Correlation immunity, identified with condition (2) of Corollary 6.14, is attributed to Siegenthaler. Resilience and its connection to \((0,k)\)-regularity of the Fourier spectrum, including Corollary 6.14, are attributed to Chor et al.; Corollary 6.14 is also called the Xiao–Massey Theorem in cryptography. The notes connect the same work to Theorem 6.25 and the example in Example 6.16.

<a id="pdf-ffbe9c7b3306-p170-b003"></a>
<!-- pdf-source: page=170; block=3; confidence=0.91 -->
Explicit small-support \(k\)-wise distributions are linked to orthogonal arrays, coding theory, and derandomization. Theorem 6.32, and a stronger construction in Exercise 6.27, are attributed to Alon–Babai–Itai using dual BCH codes. The lower bound in Exercise 6.28 is attributed to Rao and independent proofs.

<a id="pdf-ffbe9c7b3306-p170-b004"></a>
<!-- pdf-source: page=170; block=4; confidence=0.98 -->
Siegenthaler’s theorem captures the tradeoff between correlation immunity and \(\mathbb F_2\)-degree. The parity function is maximally correlation-immune, but its \(\mathbb F_2\)-linearity makes it unsuitable as an LFSR combining function.

<a id="pdf-ffbe9c7b3306-p170-b005"></a>
<!-- pdf-source: page=170; block=5; confidence=0.85 -->
Bent functions are credited to Rothaus, with earlier related work also noted; their applications include cryptography and coding theory. The basic constructions in Section 6.3 are attributed to Rothaus, and the family in Exercise 6.18 is named Maiorana–McFarland. Dickson's Theorem is cited as a 1901 result.

<a id="pdf-ffbe9c7b3306-p171-b001"></a>
<!-- pdf-source: page=171; block=1; confidence=1.00 -->
## 6.6. Exercises and notes

<a id="pdf-ffbe9c7b3306-p171-b002"></a>
<!-- pdf-source: page=171; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p171-b003"></a>
<!-- pdf-source: page=171; block=3; confidence=0.88 -->
Exercise 6.11 is attributed to Muller; deriving Exercise 6.30 from it and work of Blumer et al. is described as folklore. Exercise 6.12(a) is credited to Bernasconi–Codenotti, Exercise 6.13 to MacWilliams–Sloane, and Exercise 6.25(a,b) to Freivalds and Naor–Naor, respectively. The Gowers norm and Exercise 6.34 are attributed to Gowers; the proof of the second statement in Proposition 6.12 is credited to Noam Lifshitz.

<a id="pdf-ffbe9c7b3306-p173-b001"></a>
<!-- pdf-source: page=173; block=1; confidence=0.99 -->
This chapter studies property testing, PCPs, and CSPs, centered on testing whether an unknown Boolean function is a dictator. It extends the BLR test to a 3-query dictator tester, introduces PCP systems and CSPs, and sketches complexity applications and Håstad’s hardness results.

<a id="pdf-ffbe9c7b3306-p173-b002"></a>
<!-- pdf-source: page=173; block=2; confidence=0.98 -->
Introduces property testing for Boolean functions, building on the BLR test for linearity over \(\mathbb F_2\). A property is a collection of Boolean functions, also called a concept class; testing can precede learning to check whether the unknown function belongs to the class.

<a id="pdf-ffbe9c7b3306-p174-b001"></a>
<!-- pdf-source: page=174; block=1; confidence=0.99 -->
**Definition 7.1.** An \(r\)-query testing algorithm for Boolean functions \(f:\{0,1\}^n\to\{0,1\}\) randomly selects at most \(r\) inputs \(x^{(1)},\ldots,x^{(r)}\in\{0,1\}^n\), queries \(f\) there, and deterministically accepts or rejects based on the answers.

<a id="pdf-ffbe9c7b3306-p174-b002"></a>
<!-- pdf-source: page=174; block=2; confidence=0.97 -->
**Definition 7.2.** For a property \(C\) of functions \(\{0,1\}^n\to\{0,1\}\), a tester is a local tester with rejection rate \(\lambda>0\) if (i) every \(f\in C\) is accepted with probability 1, and (ii) for every \(0\le\varepsilon\le1\), if \(\operatorname{dist}(f,C)>\varepsilon\), then it rejects \(f\) with probability greater than \(\lambda\varepsilon\). Equivalently, acceptance probability at least \(1-\lambda\varepsilon\) implies that some \(g\in C\) satisfies \(\operatorname{dist}(f,g)\le\varepsilon\). At \(\varepsilon=0\), this yields an exact characterization; the quantitative condition also ensures that near-certain acceptance implies closeness to \(C\).

<a id="pdf-ffbe9c7b3306-p174-b003"></a>
<!-- pdf-source: page=174; block=3; confidence=0.99 -->
**Example 7.3.** By Theorem 1.30, the BLR test is a 3-query local tester for \(\mathcal C=\{f:\mathbb F_2^n\to\mathbb F_2:f\text{ is linear}\}\), with rejection rate 1.

<a id="pdf-ffbe9c7b3306-p174-b004"></a>
<!-- pdf-source: page=174; block=4; confidence=0.90 -->
The BLR tester is a family indexed by \(n\), as commonly needed for property families \((C_n)_{n\ge1}\); typically the testers share a uniform form and have a rejection-rate constant independent of \(n\). The chapter restricts to nonadaptive testers and to rejection probability linear in distance, rather than weaker rates such as \(\Omega(\varepsilon^2)\) or \(\Omega(\varepsilon/\log n)\).

<a id="pdf-ffbe9c7b3306-p175-b001"></a>
<!-- pdf-source: page=175; block=1; confidence=1.00 -->
## 7.1. Dictator testing

<a id="pdf-ffbe9c7b3306-p175-b002"></a>
<!-- pdf-source: page=175; block=2; confidence=0.98 -->
A property tester may use a query bound depending on the distance parameter and is required to reject functions far from the property with probability at least $1/2$.

<a id="pdf-ffbe9c7b3306-p175-b003"></a>
<!-- pdf-source: page=175; block=3; confidence=0.99 -->
**Definition.** The dictator property is $D=\{f:\{0,1\}^n\to\{0,1\}\mid f(x)=x_i\text{ for some }i\in[n]\}$.

<a id="pdf-ffbe9c7b3306-p175-b004"></a>
<!-- pdf-source: page=175; block=4; confidence=0.98 -->
Testing linearity alone does not test dictatorship: non-dictator parity functions are at distance $1/2$ from $D$ yet pass a linearity test. An earlier approach combines a linearity test with an AND test checking $f(x\wedge y)=f(x)\wedge f(y)$ for independent uniform $x,y$; parity functions satisfying this test perfectly are dictators or constant zero.

<a id="pdf-ffbe9c7b3306-p175-b005"></a>
<!-- pdf-source: page=175; block=5; confidence=0.97 -->
The robust form of Arrow’s theorem motivates testing an election rule on three correlated inputs drawn under impartial culture.

<a id="pdf-ffbe9c7b3306-p175-b006"></a>
<!-- pdf-source: page=175; block=6; confidence=0.99 -->
**NAE Test.** For query access to $f:\{-1,1\}^n\to\{-1,1\}$, independently for each coordinate choose $(x_i,y_i,z_i)$ uniformly from the six triples in $\{-1,1\}^3$ satisfying $\operatorname{NAE}_3=1$. Query $f(x),f(y),f(z)$.

<a id="pdf-ffbe9c7b3306-p176-b001"></a>
<!-- pdf-source: page=176; block=1; confidence=0.99 -->
Accept precisely when $\operatorname{NAE}_3(f(x),f(y),f(z))=1$. A dictator passes with probability $1$.

<a id="pdf-ffbe9c7b3306-p176-b002"></a>
<!-- pdf-source: page=176; block=2; confidence=0.96 -->
**Theorem 7.5 (restatement of Corollary 2.60).** If the NAE Test accepts $f$ with probability at least $1-\varepsilon$, then $W_1[f]\ge 1-\frac{9}{2}\varepsilon$. Consequently, by FKN, $f$ is $O(\varepsilon)$-close to some $\pm\chi_i$.

<a id="pdf-ffbe9c7b3306-p176-b003"></a>
<!-- pdf-source: page=176; block=3; confidence=0.99 -->
The NAE conclusion permits negated dictators and invokes FKN. Combining it with BLR testing addresses both limitations.

<a id="pdf-ffbe9c7b3306-p176-b004"></a>
<!-- pdf-source: page=176; block=4; confidence=0.99 -->
**Theorem 7.6.** Running both the BLR Test and the NAE Test gives a 6-query local tester for dictators with rejection rate $0.1$.

<a id="pdf-ffbe9c7b3306-p176-b005"></a>
<!-- pdf-source: page=176; block=5; confidence=0.96 -->
**Proof.** A dictator passes both tests with probability $1$. For $0\le\varepsilon\le1$, suppose the combined test accepts with probability at least $1-0.1\varepsilon$. Each test then accepts with probability at least $1-0.1\varepsilon$. The NAE bound gives $W_1[f]\ge1-\frac92(0.1\varepsilon)=1-0.45\varepsilon$. BLR (Theorem 1.30) implies $f$ is $0.1\varepsilon$-close to a parity function, so for some $S^*\subseteq[n]$, $\widehat f(S^*)^2\ge(1-0.2\varepsilon)^2$. If $|S^*|\ne1$, Parseval would imply
\[
1=\sum_{k=0}^n W_k[f]\ge (1-0.45\varepsilon)+(1-0.2\varepsilon)^2\ge2-0.85\varepsilon>1,
\]
a contradiction. Thus $|S^*|=1$, and $f$ is $0.1\varepsilon$-close to the corresponding dictator.

<a id="pdf-ffbe9c7b3306-p176-b006"></a>
<!-- pdf-source: page=176; block=6; confidence=0.99 -->
A randomized choice between the two tests reduces the query count from six to three while retaining a positive constant rejection rate.

<a id="pdf-ffbe9c7b3306-p176-b007"></a>
<!-- pdf-source: page=176; block=7; confidence=0.99 -->
**BLR+NAE Test.** The test is introduced here; its two branches are specified on the next page.

<a id="pdf-ffbe9c7b3306-p177-b001"></a>
<!-- pdf-source: page=177; block=1; confidence=0.99 -->
**BLR+NAE Test.** With probability $1/2$, run the BLR Test on $f$; with probability $1/2$, run the NAE Test on $f$.

<a id="pdf-ffbe9c7b3306-p177-b002"></a>
<!-- pdf-source: page=177; block=2; confidence=0.99 -->
**Theorem 7.7.** The BLR+NAE Test is a 3-query local tester for dictators with rejection rate $0.05$.

<a id="pdf-ffbe9c7b3306-p177-b003"></a>
<!-- pdf-source: page=177; block=3; confidence=0.98 -->
**Proof.** If the combined test accepts with probability at least $1-0.05\varepsilon$, then each branch’s test accepts with probability at least $1-0.1\varepsilon$. Theorem 7.6’s analysis then yields the required conclusion.

<a id="pdf-ffbe9c7b3306-p177-b004"></a>
<!-- pdf-source: page=177; block=4; confidence=0.99 -->
**Remark 7.8.** For $t=O(1)$ tests using $r_i$ queries, choosing one uniformly at random gives a test using at most $\max_i r_i$ queries. If it accepts with probability at least $1-(\lambda/t)\varepsilon$, every component test accepts with probability at least $1-\lambda\varepsilon$.

<a id="pdf-ffbe9c7b3306-p177-b005"></a>
<!-- pdf-source: page=177; block=5; confidence=0.99 -->
A dictator tester can be combined with a test for membership in any subclass of dictators to obtain a 3-query tester for that subclass.

<a id="pdf-ffbe9c7b3306-p177-b006"></a>
<!-- pdf-source: page=177; block=6; confidence=0.99 -->
**Theorem 7.9.** For any $S\subseteq[n]$, let $\mathcal S=\{\chi_i:\{0,1\}^n\to\{0,1\}\mid i\in S\}$. There is a 3-query local tester for $\mathcal S$ with rejection rate $0.01$.

<a id="pdf-ffbe9c7b3306-p177-b007"></a>
<!-- pdf-source: page=177; block=7; confidence=0.98 -->
**Proof.** Let $1_S\in\{0,1\}^n$ be the indicator string of $S$. With probability $1/2$, run BLR+NAE on $f$; otherwise apply Proposition 1.31’s local correcting routine to $f$ at $1_S$ and accept exactly when its output is $1$. This uses two or three queries and accepts every $f\in\mathcal S$ with probability $1$. For $0\le\varepsilon\le1$, assume acceptance probability at least $1-\lambda\varepsilon$, where $\lambda=0.01$. The proof aims to show that $f$ is $\varepsilon$-close to some $\chi_i$ with $i\in S$. The first consequence stated is that BLR+NAE accepts with probability at least $1-2\lambda\varepsilon$; the remainder continues beyond the supplied pages.

<a id="pdf-ffbe9c7b3306-p178-b001"></a>
<!-- pdf-source: page=178; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p178-b002"></a>
<!-- pdf-source: page=178; block=2; confidence=1.00 -->
## 7.2. Probabilistically Checkable Proofs of Proximity

<a id="pdf-ffbe9c7b3306-p178-b003"></a>
<!-- pdf-source: page=178; block=3; confidence=0.96 -->
The section introduces testing arbitrary string properties, then considers constant-query testing aided by an additional proof string.

<a id="pdf-ffbe9c7b3306-p178-b004"></a>
<!-- pdf-source: page=178; block=4; confidence=0.98 -->
**Definition 7.10.** An $r$-query tester for $w\in\{0,1\}^n$ randomly chooses at most $r$ indices in $[n]$, queries the corresponding bits, and decides acceptance deterministically from the answers. The definition extends to strings over any finite alphabet $\Omega$.

<a id="pdf-ffbe9c7b3306-p179-b001"></a>
<!-- pdf-source: page=179; block=1; confidence=0.98 -->
**Definition 7.11.** For a property $C\subseteq\{0,1\}^n$, a tester has rejection rate $\lambda>0$ if it accepts every $w\in C$ with probability $1$, and for every $0\le\epsilon\le1$, rejects $w$ with probability greater than $\lambda\epsilon$ whenever $\operatorname{dist}(w,C)>\epsilon$. Equivalently, acceptance probability at least $1-\lambda\epsilon$ implies $\operatorname{dist}(w,C)\le\epsilon$.

<a id="pdf-ffbe9c7b3306-p179-b002"></a>
<!-- pdf-source: page=179; block=2; confidence=0.94 -->
For the all-zero property, querying one uniformly random bit and accepting iff it is zero gives rejection rate $1$. For the constant-string property $E=\{0^n,1^n\}$, querying two independent uniform coordinates and accepting iff they agree gives rejection probability $\frac12-\frac12(1-2\epsilon)^2\ge\epsilon$ when the distance is $\epsilon$. The odd-parity property requires $n$ queries for any local tester (claimed as an exercise).

<a id="pdf-ffbe9c7b3306-p179-b003"></a>
<!-- pdf-source: page=179; block=3; confidence=0.97 -->
Most string properties do not have constant-query local testers. The text motivates allowing an auxiliary proof string that a tester can inspect along with the input.

<a id="pdf-ffbe9c7b3306-p179-b004"></a>
<!-- pdf-source: page=179; block=4; confidence=0.94 -->
**Definition 7.13.** A property $C\subseteq\{0,1\}^n$ has an $r$-query, length-$\ell$ PCPP system with rejection rate $\lambda>0$ if there is an $r$-query tester $T$ on pairs $(w,\Pi)\in\{0,1\}^n\times\{0,1\}^{\ell}$ satisfying completeness and soundness conditions stated on the next page.

<a id="pdf-ffbe9c7b3306-p180-b001"></a>
<!-- pdf-source: page=180; block=1; confidence=0.99 -->
**Definition 7.13.** (Completeness) For each $w\in C$, some proof $\Pi\in\{0,1\}^{\ell}$ makes $T$ accept with probability $1$. (Soundness) For all $0\le\epsilon\le1$, if $\operatorname{dist}(w,C)>\epsilon$, then every proof makes $T$ reject with probability greater than $\lambda\epsilon$. Equivalently, if some proof yields acceptance probability at least $1-\lambda\epsilon$, then $w$ is $\epsilon$-close to $C$. PCPPs are also called assisted testers, locally testable proofs, or assignment testers.

<a id="pdf-ffbe9c7b3306-p180-b002"></a>
<!-- pdf-source: page=180; block=2; confidence=0.97 -->
**Remark 7.14.** The usual goal is a small universal query bound (such as $r=3$), relatively short proof length (for example, polynomial in $n$), and any positive universal rejection rate.

<a id="pdf-ffbe9c7b3306-p180-b003"></a>
<!-- pdf-source: page=180; block=3; confidence=0.99 -->
For the odd-parity property, the proof stores partial sums \(\Pi_j=\sum_{i=1}^{j+1}w_i\pmod2\) and randomly checks one of \(\Pi_1=w_1+w_2,\Pi_2=\Pi_1+w_3,\ldots,\Pi_{n-1}=\Pi_{n-2}+w_n,\Pi_{n-1}=1\). The tester uses at most 3 queries. If \(w\) is outside the property, at least one of the \(n\) checks fails; since its distance from the property is \(1/n\), the rejection rate is 1.

<a id="pdf-ffbe9c7b3306-p181-b001"></a>
<!-- pdf-source: page=181; block=1; confidence=1.00 -->
## 7.2. Probabilistically Checkable Proofs of Proximity

<a id="pdf-ffbe9c7b3306-p181-b002"></a>
<!-- pdf-source: page=181; block=2; confidence=1.00 -->
The section extends the prior result to arbitrary properties, with very large proof length.

<a id="pdf-ffbe9c7b3306-p181-b003"></a>
<!-- pdf-source: page=181; block=3; confidence=0.98 -->
**Theorem 7.16.** For every class $C\subseteq\{0,1\}^n$, there is a 3-query PCPP system for $C$ with proof length $2^{2^n}$ and rejection rate $0.001$.

<a id="pdf-ffbe9c7b3306-p181-b004"></a>
<!-- pdf-source: page=181; block=4; confidence=0.99 -->
**Theorem 7.16.** Every property \(\mathcal C\subseteq\{0,1\}^n\) has a 3-query PCPP system of proof length \(2^{2^n}\) and rejection rate \(.001\). The proof interprets \(\{0,1\}^n\) as indices in a set of size \(2^n\), and the proof as a Boolean function on that set.

<a id="pdf-ffbe9c7b3306-p182-b001"></a>
<!-- pdf-source: page=182; block=1; confidence=0.90 -->
Since overall acceptance is at least $1-\lambda\varepsilon$, subtest (1) accepts with probability at least $1-2\lambda\varepsilon$. Theorem 7.9 then gives some $w'\in C$ such that $\Pi$ is $200\lambda\varepsilon$-close to $\chi_{\iota(w')}$. As dictators are parity functions, Proposition 1.31 implies, for every $j$,
\[
\Pr[\text{local correction of }\Pi\text{ on }X^{(j)}\text{ outputs }\chi_{\iota(w')}(X^{(j)})=w'_j]\ge 1-400\lambda\varepsilon\ge\tfrac12.\tag{7.1}
\]
The last inequality uses $400\lambda\varepsilon\le400\lambda=0.4<1/2$.

<a id="pdf-ffbe9c7b3306-p182-b002"></a>
<!-- pdf-source: page=182; block=2; confidence=0.99 -->
Subtest (2) rejects with probability at most \(2\lambda\varepsilon\), so \(\mathbb E_{j\sim[n]}[\Pr[\text{local correction on }X^{(j)}\text{ does not output }w_j]]\le2\lambda\varepsilon\). Markov’s inequality implies that for all but a \(4\lambda\varepsilon\) fraction of coordinates, this failure probability is less than \(1/2\). Combining with (7.1) yields \(w_j=w'_j\) outside that fraction; hence \(\operatorname{dist}(w,\mathcal C)\le4\lambda\varepsilon\le\varepsilon\).

<a id="pdf-ffbe9c7b3306-p182-b003"></a>
<!-- pdf-source: page=182; block=3; confidence=0.96 -->
The text motivates studying properties represented by modest-size circuits, whose PCPP proof lengths may be much smaller than $2^{2^n}$. For an $n$-input circuit $C$, its accepted strings define the property
\[
C=\{w\in\{0,1\}^n:C(w)=1\}.\tag{7.2}
\]

<a id="pdf-ffbe9c7b3306-p182-b004"></a>
<!-- pdf-source: page=182; block=4; confidence=0.98 -->
**Definition 7.17.** A PCPP reduction is an algorithm that takes a circuit $C$ as input and outputs a PCPP system for the property in (7.2), where $n$ is the number of inputs to $C$. If the output system always uses $r$ queries, has proof length $\ell(n,\operatorname{size}(C))$ for some function $\ell$, and rejection rate $\lambda>0$, the reduction has those parameters; it must run in time $\operatorname{poly}(\operatorname{size}(C),\ell)$.

<a id="pdf-ffbe9c7b3306-p183-b001"></a>
<!-- pdf-source: page=183; block=1; confidence=0.95 -->
A system description specifies the queried bits and acceptance predicate for each random outcome. The preceding constructions yield reductions: the first has a simple tester description, and the second can enumerate a circuit's truth table within the allowed time.

<a id="pdf-ffbe9c7b3306-p183-b002"></a>
<!-- pdf-source: page=183; block=2; confidence=0.99 -->
**Theorem 7.18.** There exists a 3-query PCPP reduction with proof length $2^{2^n}$ and rejection rate $0.001$.

<a id="pdf-ffbe9c7b3306-p183-b003"></a>
<!-- pdf-source: page=183; block=3; confidence=1.00 -->
**Theorem 7.19.** There exists a 3-query PCPP reduction with proof length \(2^{\operatorname{poly}(\operatorname{size}(C))}\) and positive rejection rate.

<a id="pdf-ffbe9c7b3306-p183-b004"></a>
<!-- pdf-source: page=183; block=4; confidence=0.99 -->
**The PCPP Theorem.** There exists a 3-query PCPP reduction with proof length $\operatorname{poly}(\operatorname{size}(C))$ and positive rejection rate.

<a id="pdf-ffbe9c7b3306-p183-b005"></a>
<!-- pdf-source: page=183; block=5; confidence=0.99 -->
**Theorem 7.20.** There exists a 3-query PCPP reduction with proof length $\operatorname{size}(C)\cdot\operatorname{polylog}(\operatorname{size}(C))$ and positive rejection rate.

<a id="pdf-ffbe9c7b3306-p183-b006"></a>
<!-- pdf-source: page=183; block=6; confidence=1.00 -->
## 7.3. CSPs and computational complexity

<a id="pdf-ffbe9c7b3306-p183-b007"></a>
<!-- pdf-source: page=183; block=7; confidence=1.00 -->
This section concerns the computational complexity of constraint satisfaction problems (CSPs) and applications of Boolean-function analysis.

<a id="pdf-ffbe9c7b3306-p184-b001"></a>
<!-- pdf-source: page=184; block=1; confidence=1.00 -->
# 7. Property testing, PCPPs, and CSPs

<a id="pdf-ffbe9c7b3306-p184-b002"></a>
<!-- pdf-source: page=184; block=2; confidence=1.00 -->
A CSP assigns labels from a domain to variables and evaluates local constraints on them; the section introduces the needed definitions.

<a id="pdf-ffbe9c7b3306-p184-b003"></a>
<!-- pdf-source: page=184; block=3; confidence=0.99 -->
**Example 7.21.** Max-3-Sat maximizes satisfied clauses of width at most 3. Max-Cut maximizes crossing edges. Max-E3-Lin maximizes satisfied equations over \(\mathbb F_2\), each involving exactly three variables. Max-3-Coloring maximizes bichromatic edges using three colors.

<a id="pdf-ffbe9c7b3306-p184-b004"></a>
<!-- pdf-source: page=184; block=4; confidence=1.00 -->
**Definition 7.22.** A CSP over domain Ω is specified by a finite set Ψ of predicates ψ: Ωʳ → {0,1}, with arity r allowed to vary by predicate. The CSP arity is the maximum predicate arity.

<a id="pdf-ffbe9c7b3306-p184-b005"></a>
<!-- pdf-source: page=184; block=5; confidence=0.99 -->
Max-3-Sat uses Boolean labels and 14 OR predicates: eight on three literals, four on two, and two on one. The remaining examples’ predicate families continue on the next page.

<a id="pdf-ffbe9c7b3306-p185-b001"></a>
<!-- pdf-source: page=185; block=1; confidence=1.00 -->
# 7.3. CSPs and computational complexity

<a id="pdf-ffbe9c7b3306-p185-b002"></a>
<!-- pdf-source: page=185; block=2; confidence=0.96 -->
For Max-E3-Lin, \(\Psi\) contains the two predicates \((x_1,x_2,x_3)\mapsto x_1+x_2+x_3\) and \((x_1,x_2,x_3)\mapsto x_1+x_2+x_3+1\), interpreted as \(\mathbb F_2\)-valued indicators of whether the corresponding equation is satisfied.

<a id="pdf-ffbe9c7b3306-p185-b003"></a>
<!-- pdf-source: page=185; block=3; confidence=0.98 -->
**Remark 7.23.** Boolean CSPs have |Ω|=2. For ψ:{−1,1}ʳ→{0,1}, Max-ψ denotes constraints applying ψ to signed variables, with Ψ={ψ(±v₁,…,±vᵣ)}. Max-E3-Lin is also called Max-χ[3]; Max-3-Lin permits equations with one or two variables as well, while Max-E3-Sat restricts clauses to exactly three literals and is also called Max-OR3.

<a id="pdf-ffbe9c7b3306-p185-b004"></a>
<!-- pdf-source: page=185; block=4; confidence=1.00 -->
**Definition 7.24.** An instance P of Max-CSP(Ψ) on variable set V is a list (multiset) of constraints C=(S,ψ), where ψ∈Ψ and S=(v₁,…,vᵣ) is a tuple of distinct variables, with r the arity of ψ. Every variable in V must occur in some scope. For n=|V| and fixed |Ω|, |Ψ|, and maximum arity, the encoding size is between n and O(|P| log n).

<a id="pdf-ffbe9c7b3306-p185-b005"></a>
<!-- pdf-source: page=185; block=5; confidence=1.00 -->
**Remark 7.25.** For Max-Cut, multiset constraints allow parallel edges, distinct variables in each scope exclude self-loops, and requiring every variable to occur excludes isolated vertices; disconnected graphs are allowed.

<a id="pdf-ffbe9c7b3306-p185-b006"></a>
<!-- pdf-source: page=185; block=6; confidence=1.00 -->
An assignment’s score is normalized as the fraction of constraints satisfied, equivalently the probability of satisfaction for a uniformly sampled constraint. Duplicate constraints allow repeated weighting. The instance can be treated as a distribution over constraints; arbitrary nonnegative weights summing to 1 could generalize this, but finite representation concerns are avoided.

<a id="pdf-ffbe9c7b3306-p186-b001"></a>
<!-- pdf-source: page=186; block=1; confidence=1.00 -->
**Definition 7.26.** An assignment for P is a map F:V→Ω. For C=(S,ψ), F satisfies C when ψ(F(S))=1, where F(S)=(F(v₁),…,F(vᵣ)) if S=(v₁,…,vᵣ). Its value is
\[
\operatorname{Val}_P(F)=\mathbb{E}_{(S,\psi)\sim P}[\psi(F(S))]\in[0,1]. \tag{7.3}
\]
The optimum is \(\operatorname{Opt}(P)=\max_{F:V\to\Omega}\{\operatorname{Val}_P(F)\}\); P is satisfiable when Opt(P)=1.

<a id="pdf-ffbe9c7b3306-p186-b002"></a>
<!-- pdf-source: page=186; block=2; confidence=0.99 -->
**Remark 7.27.** To distinguish variable names from assigned values, constraints are written explicitly through F; for example, the three equations become F(x₁)+F(x₂)+F(x₃)=0, F(x₁)+F(x₅)+F(x₆)=0, and F(x₃)+F(x₄)+F(x₆)=1.

<a id="pdf-ffbe9c7b3306-p186-b003"></a>
<!-- pdf-source: page=186; block=3; confidence=1.00 -->
**Definition 7.28.** Max-CSP(Ψ) takes an instance P as input and asks for an assignment F of maximum value.

<a id="pdf-ffbe9c7b3306-p186-b004"></a>
<!-- pdf-source: page=186; block=4; confidence=1.00 -->
The text begins to connect CSPs with string-testing algorithms from the preceding section.

<a id="pdf-ffbe9c7b3306-p187-b001"></a>
<!-- pdf-source: page=187; block=1; confidence=0.99 -->
A CSP assignment can be viewed as a string: sampling a constraint and querying its variables gives a tester whose acceptance probability equals the assignment’s CSP value. Conversely, enumerating a tester’s random outcomes yields CSP constraints with the same acceptance probability; the CSP arity is at most the tester’s maximum query count. This correspondence is used to define outputting a PCPP system’s description.

<a id="pdf-ffbe9c7b3306-p187-b002"></a>
<!-- pdf-source: page=187; block=2; confidence=0.93 -->
The PCPP system from Example 7.15 for strings satisfying \(w_1+\cdots+w_n=1\) is a Max-3-Lin instance on \(2n-1\) variables \(w_1,\ldots,w_n,\Pi_1,\ldots,\Pi_{n-1}\). The BLR linearity tester on functions \(\{0,1\}^n\to\{0,1\}\) likewise gives a Max-3-Lin instance on \(2^n\) variables. For \(n=2\), its 16 constraints are the displayed equations of the form \(F(x)+F(y)+F(x+y)=0\) over \(\mathbb F_2\), with repeated-variable and duplicate constraints retained.

<a id="pdf-ffbe9c7b3306-p187-b003"></a>
<!-- pdf-source: page=187; block=3; confidence=0.99 -->
The section turns to the complexity of finding high-value CSP assignments, equivalently strings accepted by a tester with high probability.

<a id="pdf-ffbe9c7b3306-p188-b001"></a>
<!-- pdf-source: page=188; block=1; confidence=0.99 -->
Brute force finds an optimal cut in about \(2^n\) time, while polynomial time is the usual efficiency benchmark. Some graph classes admit efficient exact algorithms, but general Max-Cut optimization is stated to be NP-hard.

<a id="pdf-ffbe9c7b3306-p188-b002"></a>
<!-- pdf-source: page=188; block=2; confidence=0.99 -->
**Theorem 7.30.** Finding a maximum cut in an input graph is NP-hard.

<a id="pdf-ffbe9c7b3306-p188-b003"></a>
<!-- pdf-source: page=188; block=3; confidence=0.98 -->
NP-hardness is informally described as being at least as difficult as Circuit-Sat: decide whether an input Boolean circuit \(C\) has some satisfying input \(w\in\{0,1\}^n\), meaning \(C(w)=1\). The text notes the conjecture that Circuit-Sat has no polynomial-time algorithm and the stronger believed absence of a \(2^{o(n)}\)-time algorithm. Exact optimization is NP-hard for essentially all CSPs, motivating approximation.

<a id="pdf-ffbe9c7b3306-p188-b004"></a>
<!-- pdf-source: page=188; block=4; confidence=0.99 -->
**Definition 7.31.** For \(0\le \alpha\le\beta\le1\), an algorithm is an \((\alpha,\beta)\)-approximation for Max-CSP\((\Psi)\) if, on every instance with optimum at least \(\beta\), it returns an assignment of value at least \(\alpha\). For randomized algorithms, the guarantee is on expected output value.

<a id="pdf-ffbe9c7b3306-p188-b005"></a>
<!-- pdf-source: page=188; block=5; confidence=0.98 -->
For Max-E3-Lin, returning whichever of the constant assignments \(F\equiv0\) and \(F\equiv1\) has greater value guarantees at least \(1/2\), so this is an efficient \((1/2,\beta)\)-approximation for every \(\beta\). When \(\beta=1\), Gaussian elimination gives an efficient \((1,1)\)-approximation, also for Max-\(r\)-Lin.

<a id="pdf-ffbe9c7b3306-p189-b001"></a>
<!-- pdf-source: page=189; block=1; confidence=0.99 -->
Goemans and Williamson’s algorithm gives an efficient randomized \((.878\beta,\beta)\)-approximation for Max-Cut for every \(\beta\).

<a id="pdf-ffbe9c7b3306-p189-b002"></a>
<!-- pdf-source: page=189; block=2; confidence=0.99 -->
Max-E3-Sat remains hard to optimize even on satisfiable instances; in contrast, exact-value approximation is efficient for Max-3-Lin and Max-Cut. The cited standard hardness results also imply the following approximation-hardness statements.

<a id="pdf-ffbe9c7b3306-p189-b003"></a>
<!-- pdf-source: page=189; block=3; confidence=0.99 -->
**Theorem 7.33.** Finding an optimum on satisfiable instances, i.e. \((1,1)\)-approximating Max-E3-Sat, is NP-hard. The same holds for Max-3-Coloring.

<a id="pdf-ffbe9c7b3306-p189-b004"></a>
<!-- pdf-source: page=189; block=4; confidence=0.99 -->
**Theorem 7.34.** For every fixed \(\beta\in(1/2,1)\), \((\beta,\beta)\)-approximating Max-E3-Lin is NP-hard; the same is true of Max-Cut.

<a id="pdf-ffbe9c7b3306-p189-b005"></a>
<!-- pdf-source: page=189; block=5; confidence=0.99 -->
**Theorem 7.35.** There is a universal constant \(\delta_0>0\) such that \((1-\delta_0,1)\)-approximating Max-E3-Sat is NP-hard.

<a id="pdf-ffbe9c7b3306-p189-b006"></a>
<!-- pdf-source: page=189; block=6; confidence=0.99 -->
The text states that Theorem 7.35 is equivalent to the PCP Theorem and sketches its derivation from the PCPP Theorem.

<a id="pdf-ffbe9c7b3306-p189-b007"></a>
<!-- pdf-source: page=189; block=7; confidence=0.99 -->
**Proof sketch.** Let \(\delta_0\) be the PCPP rejection rate. Assuming an efficient \((1-\delta_0,1)\)-approximation algorithm \(A\) for Max-E3-Sat, construct an efficient Circuit-Sat algorithm \(B\). Given circuit \(C\), apply the PCPP reduction to obtain an arity-3 CSP \(P\) on variables \(w_1,\ldots,w_n,\Pi_1,\ldots,\Pi_\ell\), where \(\ell\le\operatorname{poly}(\operatorname{size}(C))\); assume by Exercise 7.12 that \(P\) is Max-E3-Sat. The PCPP guarantees \(\operatorname{Opt}(P)=1\) if \(C\) is satisfiable, and \(\operatorname{Opt}(P)<1-\delta_0\) otherwise. Run \(A\) on \(P\) and declare \(C\) satisfiable exactly when the returned assignment has value at least \(1-\delta_0\).

<a id="pdf-ffbe9c7b3306-p190-b001"></a>
<!-- pdf-source: page=190; block=1; confidence=1.00 -->
## 7.4. Highlight: Håstad’s hardness theorems

<a id="pdf-ffbe9c7b3306-p190-b002"></a>
<!-- pdf-source: page=190; block=2; confidence=1.00 -->
A uniformly random assignment satisfies each three-literal OR constraint with probability $7/8$, giving an expected $7/8$ fraction satisfied. The text notes this guarantee can be derandomized.

<a id="pdf-ffbe9c7b3306-p190-b003"></a>
<!-- pdf-source: page=190; block=3; confidence=0.99 -->
**Proposition 7.36.** The algorithm returning a uniformly random assignment is a $(7/8,\beta)$-approximation for every $\beta$.

<a id="pdf-ffbe9c7b3306-p190-b004"></a>
<!-- pdf-source: page=190; block=4; confidence=1.00 -->
**Proof.** Every constraint is an OR of exactly three literals, so a uniform assignment satisfies it with probability $7/8$. By linearity of expectation, the expected satisfied fraction is $7/8$.

<a id="pdf-ffbe9c7b3306-p190-b005"></a>
<!-- pdf-source: page=190; block=5; confidence=0.99 -->
**Håstad’s 3-Sat Hardness.** For every constant \(\delta>0\), it is NP-hard to \((7/8+\delta,1)\)-approximate Max-E3-Sat.

<a id="pdf-ffbe9c7b3306-p190-b006"></a>
<!-- pdf-source: page=190; block=6; confidence=0.99 -->
**Håstad’s 3-Lin Hardness.** For every constant \(\delta>0\), it is NP-hard to \((1/2+\delta,1-\delta)\)-approximate Max-E3-Lin.

<a id="pdf-ffbe9c7b3306-p190-b007"></a>
<!-- pdf-source: page=190; block=7; confidence=0.96 -->
The section sketches the hardness results, focusing on 3-Lin. The earlier approximation gap’s constant comes from the PCPP rejection rate; the dictator test in the PCPP construction controls both that rate and the predicates produced. This motivates seeking a high-rejection local dictatorship test whose decisions use three-variable linear equations.

<a id="pdf-ffbe9c7b3306-p191-b001"></a>
<!-- pdf-source: page=191; block=1; confidence=0.95 -->
Bellare, Goldreich, and Sudan obtained an explicit Max-E3-Sat gap with $\delta_0=0.026$. Håstad’s approach relaxes dictator testing: dictators are accepted with probability one (or nearly so), while functions unlike dictators need only be rejected substantially when they have no notable coordinates, potentially allowing a larger rejection rate.

<a id="pdf-ffbe9c7b3306-p191-b002"></a>
<!-- pdf-source: page=191; block=2; confidence=0.99 -->
**Definition 7.37.** Let \(\Psi\) be a finite set of predicates over \(\Omega=\{-1,1\}\), let \(0<\alpha<\beta\le1\), and let \(\lambda:[0,1]\to[0,1]\) satisfy \(\lambda(\varepsilon)\to0\) as \(\varepsilon\to0\). Suppose each \(n\) has a local tester such that dictators pass with probability at least \(\beta\), while functions satisfying \(\operatorname{Inf}^{(1-\varepsilon)}_i[f]\le\varepsilon\) for all \(i\) pass with probability at most \(\alpha+\lambda(\varepsilon)\), and its decision uses predicates in \(\Psi\).

<a id="pdf-ffbe9c7b3306-p191-b003"></a>
<!-- pdf-source: page=191; block=3; confidence=0.97 -->
**Remark 7.38.** The definition has minor technical amendments: one strengthens the second condition to include functions valued in $[-1,1]$ (explained in Exercise 7.22); another amendment is specified on the following page.

<a id="pdf-ffbe9c7b3306-p192-b001"></a>
<!-- pdf-source: page=192; block=1; confidence=1.00 -->
**Remark 7.38 (continued).** A tester may apply a predicate $\psi\in\Psi$ to queried values $f(x^{(1)}),\ldots,f(x^{(r)})$ even when some query strings coincide.

<a id="pdf-ffbe9c7b3306-p192-b002"></a>
<!-- pdf-source: page=192; block=2; confidence=1.00 -->
**Remark 7.39.** The error term $\lambda(\varepsilon)=o_{\varepsilon}(1)$ must be independent of $n$; its convergence rate otherwise is not important.

<a id="pdf-ffbe9c7b3306-p192-b003"></a>
<!-- pdf-source: page=192; block=3; confidence=1.00 -->
**Theorem 7.40.** Fix a CSP over $\Omega=\{-1,1\}$ with predicate set $\Psi$. If an $(\alpha,\beta)$ Dictator-vs.-No-Notables test using $\Psi$ exists, then for every $\delta>0$ it is UG-hard to $(\alpha+\delta,\beta-\delta)$-approximate Max-CSP$(\Psi)$.

<a id="pdf-ffbe9c7b3306-p192-b004"></a>
<!-- pdf-source: page=192; block=4; confidence=0.97 -->
The theorem transfers the test’s distinguishing parameters to UG-hardness, reducing the computational problem to Fourier analysis. It yields UG-hardness rather than NP-hardness and loses $\delta$ in the completeness parameter; Håstad’s more elaborate constructions remove these limitations. The text states the following test existence results.

<a id="pdf-ffbe9c7b3306-p192-b005"></a>
<!-- pdf-source: page=192; block=5; confidence=0.99 -->
**Theorem 7.41.** For every $0<\delta<1/8$, there exists a $(7/8+\delta,1)$ Dictator-vs.-No-Notables test whose predicates are ORs of three literals.

<a id="pdf-ffbe9c7b3306-p192-b006"></a>
<!-- pdf-source: page=192; block=6; confidence=0.99 -->
**Theorem 7.42.** For every $0<\delta<1/2$, there exists a $(1/2,1-\delta)$ Dictator-vs.-No-Notables test using three-variable 2-linear equations as predicates.

<a id="pdf-ffbe9c7b3306-p193-b001"></a>
<!-- pdf-source: page=193; block=1; confidence=1.00 -->
## 7.4. Highlight: Håstad’s hardness theorems

<a id="pdf-ffbe9c7b3306-p193-b002"></a>
<!-- pdf-source: page=193; block=2; confidence=0.95 -->
Theorem 7.42 is proved in the text; Theorem 7.41 is assigned to Exercise 7.29. Theorem 7.40 yields weakened hardness results: for every $\delta>0$, it is UG-hard to $(7/8+\delta,1-\delta)$-approximate Max-E3-Sat (Corollary 7.43), and $(1/2+\delta,1-\delta)$-approximate Max-E3-Lin (Corollary 7.44). For Max-E3-Lin, the loss in completeness is acceptable because the test accepts dictators with probability $1-\delta$; Theorem 7.42’s completeness cannot be improved to $1$ (Exercise 7.7). The BLR test suggests a three-variable linear-predicate test, but constant and large-parity functions pass it perfectly despite having no notable coordinates; the odd variant addresses the constant function.

<a id="pdf-ffbe9c7b3306-p193-b003"></a>
<!-- pdf-source: page=193; block=3; confidence=0.98 -->
**Odd BLR Test.** Given query access to \(f:\mathbb F_2^n\to\mathbb F_2\), choose independent uniform \(x,y\in\math F_2^n\), choose uniform \(b\in\mathbb F_2\), set \(z=x+y+(b,b,\ldots,b)\), and accept iff \(f(x)+f(y)+f(z)=b\).

<a id="pdf-ffbe9c7b3306-p193-b004"></a>
<!-- pdf-source: page=193; block=4; confidence=0.98 -->
**Proposition 7.46.** The Odd BLR Test accepts \(f:\{-1,1\}^n\to\{-1,1\}\) with probability \[\frac12+\frac12\sum_{S\subseteq[n],\ |S|\text{ odd}}\widehat f(S)^3\le\frac12+\frac12\max_{S\subseteq[n],\ |S|\text{ odd}}\widehat f(S).\]

<a id="pdf-ffbe9c7b3306-p194-b001"></a>
<!-- pdf-source: page=194; block=1; confidence=0.97 -->
Noise at rate $\delta/2$ in each coordinate preserves dictator acceptance up to probability loss $\delta/2$ while suppressing large parities; small odd parities may still pass, but have notable coordinates.

<a id="pdf-ffbe9c7b3306-p194-b002"></a>
<!-- pdf-source: page=194; block=2; confidence=1.00 -->
**Proof of Theorem 7.42.** For $0<\delta<1$, define the following Max-E3-Lin test, called Håstad$_\delta$.

<a id="pdf-ffbe9c7b3306-p194-b003"></a>
<!-- pdf-source: page=194; block=3; confidence=0.98 -->
**Håstad$_\delta$ Test.** Given query access to $f:\{-1,1\}^n\to\{-1,1\}$, choose independent uniform $x,y\in\{-1,1\}^n$ and uniform $b\in\{-1,1\}$. Set $z=b\cdot(x\circ y)$, where $\circ$ is coordinatewise multiplication; sample $z'\sim N_{1-\delta}(z)$; accept iff $f(x)f(y)f(z')=b$.

<a id="pdf-ffbe9c7b3306-p194-b004"></a>
<!-- pdf-source: page=194; block=4; confidence=0.90 -->
Conditioning first on $b=1$, use the noise operator and Fourier expansion to obtain
$$\Pr[\mathrm{accept}\mid b=1]=\frac12+\frac12\mathbb E[f(x)f(y)T_{1-\delta}f(x\circ y)]=\frac12+\frac12\sum_{S\subseteq[n]}(1-\delta)^{|S|}\widehat f(S)^3.$$
For $b=-1$, $z'$ has distribution $N_{-(1-\delta)}(x\circ y)$, giving
$$\Pr[\mathrm{accept}\mid b=-1]=\frac12-\frac12\sum_{S\subseteq[n]}(-1)^{|S|}(1-\delta)^{|S|}\widehat f(S)^3.$$
Averaging yields equation (7.4):
$${\Pr[\mathrm{accept}]}=\frac12+\frac12\sum_{|S|\text{ odd}}(1-\delta)^{|S|}\widehat f(S)^3.\tag{7.4}$$
Setting $\delta=0$ also proves Proposition 7.46. A dictator $f=\chi_S$ with $|S|=1$ is accepted with probability $1-\delta/2$.

<a id="pdf-ffbe9c7b3306-p195-b001"></a>
<!-- pdf-source: page=195; block=1; confidence=0.99 -->
Assume \(\operatorname{Inf}^{(1-\varepsilon)}_i[f]=\sum_{S\ni i}(1-\varepsilon)^{|S|-1}\widehat f(S)^2\le\varepsilon\) for every \(i\). For \(\varepsilon\le\delta\), the Håstad test accepts with probability at most \(\frac12+\frac12\sqrt{\max_i\operatorname{Inf}^{(1-\delta)}_i[f]}\le\frac12+\frac12\sqrt\varepsilon\).

<a id="pdf-ffbe9c7b3306-p195-b002"></a>
<!-- pdf-source: page=195; block=2; confidence=1.00 -->
## 7.5. Exercises and notes

<a id="pdf-ffbe9c7b3306-p195-b003"></a>
<!-- pdf-source: page=195; block=3; confidence=0.96 -->
**Exercise 7.1.** Repeat an \(r\)-query local tester with rejection rate \(\lambda\) independently enough times to get perfect acceptance on members and acceptance at most \(\delta\) on functions \(\varepsilon\)-far from the property, using \(O(r\log(1/\delta)/(\lambda\varepsilon))\) nonadaptive queries.

<a id="pdf-ffbe9c7b3306-p196-b001"></a>
<!-- pdf-source: page=196; block=1; confidence=0.99 -->
## 7.5–7.20. Exercises and notes

<a id="pdf-ffbe9c7b3306-p196-b002"></a>
<!-- pdf-source: page=196; block=2; confidence=0.99 -->
For the odd-weight strings $O\subseteq\{0,1\}^n$, prove that any $(n-1)$-query tester accepting every member of $O$ with probability $1$ must accept every string with probability $1$, so testing $O$ requires $n$ queries.

<a id="pdf-ffbe9c7b3306-p196-b003"></a>
<!-- pdf-source: page=196; block=3; confidence=0.99 -->
Show that a 2-query tester for functions $\{-1,1\}^n\to\{-1,1\}$ that accepts all dictators with probability $1$ also accepts every odd-size majority $\mathrm{Maj}_{n'}$ for odd $n'\le n$. This rules out 2-query dictatorship testing for $n>2$.

<a id="pdf-ffbe9c7b3306-p196-b004"></a>
<!-- pdf-source: page=196; block=4; confidence=0.99 -->
For every $\alpha<1$, prove there is no $(\alpha,1)$ Dictator-vs.-No-Notables test using Max-E3-Lin predicates; the suggested approach uses large odd parities.

<a id="pdf-ffbe9c7b3306-p196-b005"></a>
<!-- pdf-source: page=196; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p196-b006"></a>
<!-- pdf-source: page=196; block=6; confidence=0.99 -->
Construct a 3-query dictatorship tester by combining the Odd BLR Test with the test in part (a).

<a id="pdf-ffbe9c7b3306-p196-b007"></a>
<!-- pdf-source: page=196; block=7; confidence=0.99 -->
Optimize the rejection rate in Theorem 7.7, using Fourier expressions from Theorems 1.30 and 2.56 and Exercise 1.28; also consider running BLR and NAE tests with probabilities other than $1/2$.

<a id="pdf-ffbe9c7b3306-p196-b008"></a>
<!-- pdf-source: page=196; block=8; confidence=0.99 -->
**Definition.** An $(\alpha,\beta)$-distinguishing algorithm for Max-CSP$(\Psi)$ outputs YES on instances of value at least $\beta$ and NO on instances of value strictly below $\alpha$; either output is allowed for values in $[\alpha,\beta)$. Show that an efficient $(\alpha,\beta)$-approximation algorithm yields an efficient $(\alpha,\beta)$-distinguishing algorithm.

<a id="pdf-ffbe9c7b3306-p196-b009"></a>
<!-- pdf-source: page=196; block=9; confidence=0.99 -->
For a predicate class $\Psi$ closed under restrictions to nonconstant functions, show that an efficient $(1,1)$-distinguishing algorithm for Max-CSP$(\Psi)$ implies an efficient $(1,1)$-approximation algorithm; the hint suggests trying all labels for the first variable.

<a id="pdf-ffbe9c7b3306-p196-b010"></a>
<!-- pdf-source: page=196; block=10; confidence=0.99 -->
Given a width-$w$ CNF $\varphi$ of size $s$, where $w\ge3$, construct an equivalent width-3 CNF $\varphi'$ of size at most $(w-2)s$, using the original variables and at most $(w-3)s$ auxiliary variables. Equivalence means each satisfying assignment to $\varphi$ extends to one satisfying $\varphi'$, while each falsifying assignment to $\varphi$ falsifies $\varphi'$ for every auxiliary assignment.

<a id="pdf-ffbe9c7b3306-p197-b001"></a>
<!-- pdf-source: page=197; block=1; confidence=0.99 -->
## 7.5. Exercises and notes

<a id="pdf-ffbe9c7b3306-p197-b002"></a>
<!-- pdf-source: page=197; block=2; confidence=0.99 -->
Extend the width-3 CNF construction so every clause has width exactly 3, with size increasing by at most $O(s)$.

<a id="pdf-ffbe9c7b3306-p197-b003"></a>
<!-- pdf-source: page=197; block=3; confidence=0.98 -->
From an $r$-query PCPP reduction $R_1$ with rejection rate $\lambda$, construct a 3-query reduction $R_2$ with rejection rate at least $\lambda/(r2^r)$. Its proof length should be at most $r2^r m$ plus the proof length of $R_1$, where $m$ is the description size of $R_1$'s output; each output predicate is an OR of exactly three literals.

<a id="pdf-ffbe9c7b3306-p197-b004"></a>
<!-- pdf-source: page=197; block=4; confidence=0.99 -->
Give a polynomial-time reduction from a Boolean circuit $C$ to a width-3 CNF $\varphi$ such that $C$ is satisfiable iff $\varphi$ is satisfiable; introduce a variable for each gate.

<a id="pdf-ffbe9c7b3306-p197-b005"></a>
<!-- pdf-source: page=197; block=5; confidence=0.99 -->
Use the reduction to justify that $(1,1)$-distinguishing Max-3-Sat is NP-hard: a polynomial-time $(1,1)$ distinguisher or approximation algorithm for Max-3-Sat would put Circuit-Sat in polynomial time.

<a id="pdf-ffbe9c7b3306-p197-b006"></a>
<!-- pdf-source: page=197; block=6; confidence=0.99 -->
Prove Theorem 7.33, using Exercise 7.11(b).

<a id="pdf-ffbe9c7b3306-p197-b007"></a>
<!-- pdf-source: page=197; block=7; confidence=0.99 -->
Describe an efficient $(1,1)$-approximation algorithm for Max-Cut.

<a id="pdf-ffbe9c7b3306-p197-b008"></a>
<!-- pdf-source: page=197; block=8; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p197-b009"></a>
<!-- pdf-source: page=197; block=9; confidence=0.99 -->
Generalize the tester to an affine subspace of $\mathbb F_2^n$.

<a id="pdf-ffbe9c7b3306-p197-b010"></a>
<!-- pdf-source: page=197; block=10; confidence=0.97 -->
For any affine subspace $A\subseteq\mathbb F_2^n$, construct a 3-query, length-$2^n$ PCPP with positive universal rejection rate. The proof is expected to encode the truth table of $\chi_w$ for $w\in\mathbb F_2^n$; use Exercise 7.15 and check consistency by locally correcting at a uniformly random $e_i$.

<a id="pdf-ffbe9c7b3306-p197-b011"></a>
<!-- pdf-source: page=197; block=11; confidence=0.99 -->
Construct a 3-query, length-$O(n)$ PCPP with positive universal rejection rate for $\{w\in\mathbb F_2^n: IP_n(w)=1\}$, where $n$ is even.

<a id="pdf-ffbe9c7b3306-p197-b012"></a>
<!-- pdf-source: page=197; block=12; confidence=0.99 -->
Construct the corresponding 3-query, length-$O(n)$ PCPP for the complete quadratic function $CQ_n$, using Exercise 4.13.

<a id="pdf-ffbe9c7b3306-p197-b013"></a>
<!-- pdf-source: page=197; block=13; confidence=0.99 -->
For nonzero $D\in\mathbb F_2^{n\times n}$ and independent uniform $x,y\in\mathbb F_2^n$, prove $\Pr[y^\mathsf{T}Dx\ne0]\ge\frac14$.

<a id="pdf-ffbe9c7b3306-p198-b001"></a>
<!-- pdf-source: page=198; block=1; confidence=0.99 -->
For $\gamma\in\mathbb F_2^n$ and independent uniform $x,y\in\mathbb F_2^n$, $\Gamma\in\mathbb F_2^{n\times n}$, show that $\Pr[(\gamma^\mathsf{T}x)(\gamma^\mathsf{T}y)=\Gamma\bullet(xy^\mathsf{T})]$ equals 1 when $\Gamma=\gamma\gamma^\mathsf{T}$ and is at most $3/4$ otherwise. Here $B\bullet C=\sum_{i,j}B_{ij}C_{ij}$.

<a id="pdf-ffbe9c7b3306-p198-b002"></a>
<!-- pdf-source: page=198; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p198-b003"></a>
<!-- pdf-source: page=198; block=3; confidence=0.94 -->
For a list $L$ of homogeneous quadratic equations $\sum_{i,j}c_{ij}w_iw_j=b$ over $w\in\mathbb F_2^n$, define the solution property $\{w:L(w)\text{ holds}\}$. Construct a 4-query PCPP of length $2^n+2^{n^2}$ and positive universal rejection rate. Its proof should encode the truth tables of $\chi_w$ and $\chi_{ww^\mathsf{T}}$; use part (c) and Exercise 7.15 on $q$.

<a id="pdf-ffbe9c7b3306-p198-b004"></a>
<!-- pdf-source: page=198; block=4; confidence=0.99 -->
Complete the proof of Theorem 7.19 by encoding a circuit computation's gate values $\bar w$ and the truth tables of $\chi_{\bar w}$ and $\chi_{\bar w\bar w^\mathsf{T}}$. Express validity of $\bar w$ as homogeneous quadratic equations, check consistency with input $w$ by local correction, then reduce to 3 queries using Exercise 7.12.

<a id="pdf-ffbe9c7b3306-p198-b005"></a>
<!-- pdf-source: page=198; block=5; confidence=0.99 -->
Verify the stated connection between $\operatorname{Opt}(P)$ and circuit satisfiability in the proof sketch of Theorem 7.35, using that every string is 1-far from the empty property.

<a id="pdf-ffbe9c7b3306-p198-b006"></a>
<!-- pdf-source: page=198; block=6; confidence=0.99 -->
**Definition.** A randomized assignment $F$ maps each CSP variable to a probability distribution on domain $\Omega$. For a constraint $(S,\psi)$ with $S=(v_1,\ldots,v_r)$, $\psi(F(S))$ is the expected predicate value under independent draws from the assigned distributions, equivalently the probability the constraint is satisfied. Define $\operatorname{Val}_P(F)=\mathbb E_{(S,\psi)\sim P}[\psi(F(S))]$.

<a id="pdf-ffbe9c7b3306-p198-b007"></a>
<!-- pdf-source: page=198; block=7; confidence=0.99 -->
Given a deterministic algorithm producing a randomized assignment of value $\alpha$ on instance $P$, modify it into a randomized algorithm that outputs an ordinary assignment whose value has expectation $\alpha$.

<a id="pdf-ffbe9c7b3306-p199-b001"></a>
<!-- pdf-source: page=199; block=1; confidence=0.99 -->
Exercises and notes on randomized assignments, testing, and CSP approximation.

<a id="pdf-ffbe9c7b3306-p199-b002"></a>
<!-- pdf-source: page=199; block=2; confidence=0.99 -->
For the algorithm assigning each variable an independent uniform bit, show it is a \((7/8,\beta)\)-approximation for Max-E3-Sat for every \(\beta\), and a \((1/2,\beta)\)-approximation for Max-3-Lin.

<a id="pdf-ffbe9c7b3306-p199-b003"></a>
<!-- pdf-source: page=199; block=3; confidence=0.99 -->
For domain \(\{-1,1\}\), represent a randomized assignment by its mean function \(f:V\to[-1,1]\). Show that constraint \((S,\psi)\), with \(S=(v_1,\ldots,v_r)\), has value \(\psi(f(v_1),\ldots,f(v_r))\), interpreting \(\psi\) by its multilinear Fourier expansion.

<a id="pdf-ffbe9c7b3306-p199-b004"></a>
<!-- pdf-source: page=199; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p199-b005"></a>
<!-- pdf-source: page=199; block=5; confidence=0.99 -->
Given a randomized assignment of value \(\alpha\) for a CSP instance, give an efficient deterministic procedure producing an ordinary assignment of value at least \(\alpha\), by successively choosing a label for each variable that maximizes the conditional expected value.

<a id="pdf-ffbe9c7b3306-p199-b006"></a>
<!-- pdf-source: page=199; block=6; confidence=0.96 -->
Interpret a Boolean local tester as a CSP tester on mean-valued functions \(f:\{-1,1\}^n\to[-1,1]\), where a query at \(x\) returns a random sign of mean \(f(x)\). Verify that the Håstad \(\delta\)-Test is a \((1/2,1-\delta)\)-Dictator-vs.-No-Notables test by extending (7.4) to this range; the later inequality that uses Boolean range also holds for \([-1,1]\)-valued functions.

<a id="pdf-ffbe9c7b3306-p199-b007"></a>
<!-- pdf-source: page=199; block=7; confidence=0.99 -->
For a finite predicate family on \(\{-1,1\}\) closed under negating variables, show Dictator-vs.-No-Notables tests may assume the tested function is odd, without loss of generality.

<a id="pdf-ffbe9c7b3306-p200-b001"></a>
<!-- pdf-source: page=200; block=1; confidence=0.98 -->
Starting with an \((\alpha,\beta)\)-test \(T\) for odd \([-1,1]\)-valued functions using \(\Psi\), modify each query at \(x\) to use \(-f(-x)\) with probability \(1/2\) and \(f(x)\) with probability \(1/2\). Show the modified test's acceptance probability on arbitrary \(f\) equals that of \(T\) on the odd part of \(f\).

<a id="pdf-ffbe9c7b3306-p200-b002"></a>
<!-- pdf-source: page=200; block=2; confidence=0.98 -->
Prove the modified test is an \((\alpha,\beta)\)-Dictator-vs.-No-Notables test for arbitrary functions \(f:\{-1,1\}^n\to[-1,1]\).

<a id="pdf-ffbe9c7b3306-p200-b003"></a>
<!-- pdf-source: page=200; block=3; confidence=0.98 -->
Suppose \(U\) is an \((\alpha,\beta)\)-test using arity-\(r\) predicates \(\Psi\), valid for functions of the form \(T_{1-\delta}h\). Modify each query at \(x\) to query \(f(y)\), where \(y\sim N_{1-\delta}(x)\). Show the resulting test's acceptance probability on arbitrary \(h\) equals that of \(U\) on \(T_{1-\delta}h\).

<a id="pdf-ffbe9c7b3306-p200-b004"></a>
<!-- pdf-source: page=200; block=4; confidence=0.98 -->
Show the modified test is an \((\alpha,\beta-r\delta/2)\)-Dictator-vs.-No-Notables test using \(\Psi\).

<a id="pdf-ffbe9c7b3306-p200-b005"></a>
<!-- pdf-source: page=200; block=5; confidence=0.98 -->
Give an alternative proof of Theorem 7.42 using the original BLR Test analysis together with Exercises 7.23 and 7.24.

<a id="pdf-ffbe9c7b3306-p200-b006"></a>
<!-- pdf-source: page=200; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p200-b007"></a>
<!-- pdf-source: page=200; block=7; confidence=0.95 -->
For \(q\in\mathbb{Z}_{>0}\), Unique-Games\((q)\) has domain \([q]\) and all binary predicates \(\psi(i,j)=1\iff\pi(j)=i\) for bijections \(\pi:[q]\to[q]\). Show exact \((1,1)\)-approximation is polynomial-time; the exercise also states the conjectured hardness of \((\delta,1-\delta)\)-approximation for some \(q\) at each \(\delta>0\).

<a id="pdf-ffbe9c7b3306-p200-b008"></a>
<!-- pdf-source: page=200; block=8; confidence=0.98 -->
For each equation \(v_1+v_2+v_3=0\) and \(v_1+v_2+v_3=1\) over \(\mathbb{F}_2\), construct four clauses that are all satisfied when the equation holds and at most three satisfied otherwise.

<a id="pdf-ffbe9c7b3306-p201-b001"></a>
<!-- pdf-source: page=201; block=1; confidence=0.99 -->
Assuming efficient \((7/8+\delta,1-\delta)\)-approximation for Max-E3-Sat at every \(\delta>0\), derive efficient \((1/2+\delta,1-\delta)\)-approximation for Max-E3-Lin.

<a id="pdf-ffbe9c7b3306-p201-b002"></a>
<!-- pdf-source: page=201; block=2; confidence=0.99 -->
Show how to convert any \((\alpha,\beta)\)-Dictator-vs.-No-Notables test using Max-E3-Lin predicates into a \((3/4+\alpha/4,\beta)\)-test using Max-E3-Sat predicates.

<a id="pdf-ffbe9c7b3306-p201-b003"></a>
<!-- pdf-source: page=201; block=3; confidence=0.99 -->
For small \(0<\delta<1\), construct a \((3/4+\delta/4,1)\)-test using OXR predicates, then convert it to a \((7/8+\delta/8,1)\)-test using Max-E3-Sat predicates.

<a id="pdf-ffbe9c7b3306-p201-b004"></a>
<!-- pdf-source: page=201; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p201-b005"></a>
<!-- pdf-source: page=201; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p201-b006"></a>
<!-- pdf-source: page=201; block=6; confidence=0.98 -->
Complete the proof that the test is \((3/4+\delta/4,1)\)-Dictator-vs.-No-Notables for odd \(f\).

<a id="pdf-ffbe9c7b3306-p201-b007"></a>
<!-- pdf-source: page=201; block=7; confidence=0.98 -->
To prove Theorem 7.40, assume an \((\alpha,\beta)\)-Dictator-vs.-No-Notables test \(T\) using predicates \(\Psi\) on \(\{-1,1\}\). Define an efficient reduction \(R\) from Unique-Games\((q)\) instance \(G\) to Max-CSP\((\Psi)\) instance \(P\). Regard vertices and constraints of \(G\) as vertices and edges, assume its underlying undirected graph is regular (per the cited result, without loss for the conjecture), and give \(P\) variable set \(V\times\{-1,1\}^q\).

<a id="pdf-ffbe9c7b3306-p202-b001"></a>
<!-- pdf-source: page=202; block=1; confidence=1.00 -->
## 7. Property testing, PCPPs, and CSPs

<a id="pdf-ffbe9c7b3306-p202-b002"></a>
<!-- pdf-source: page=202; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p202-b003"></a>
<!-- pdf-source: page=202; block=3; confidence=0.96 -->
The reduction in Exercise 7.30 can create repeated variables within a constraint. For integer $M>0$, modify it to $P'$ with variables $V\times[M]\times\{−1,1\}^q$, using independent copies $f_v^j$ and choosing a uniform copy each time $P$ queries $f_v(x)$. Show that $\operatorname{Opt}(P)=\operatorname{Opt}(P')$; deleting constraints whose scopes repeat variables changes the optimum by at most $r^2/M$, where $r$ is the maximum predicate arity; and the resulting instance is a valid $\operatorname{MaxCSP}(\Psi)$ instance. Taking $M$ large repairs the reduction.

<a id="pdf-ffbe9c7b3306-p203-b001"></a>
<!-- pdf-source: page=203; block=1; confidence=1.00 -->
## 7.5. Exercises and notes

<a id="pdf-ffbe9c7b3306-p203-b002"></a>
<!-- pdf-source: page=203; block=2; confidence=0.96 -->
Historical notes trace property testing to Rubinfeld–Sudan and Goldreich–Goldwasser–Ron, local testability to Friedl–Sudan, and dictatorship testing to Bellare–Goldreich–Sudan, with later work by Parnas–Ron–Samorodnitsky and Kalai. PCPPs arose from interactive-proof research; their definition and the PCPP theorem were independently developed by Ben-Sasson et al. and Dinur–Reingold, drawing on earlier reductions. The presentation of Theorem 7.16 is credited to Dinur.

<a id="pdf-ffbe9c7b3306-p204-b001"></a>
<!-- pdf-source: page=204; block=1; confidence=0.96 -->
A circuit of size \(O(n)\) checking a formal proof gives a string property accepted by the circuit; the theorem provides a 3-query test with an additional proof of length \(n\,\mathrm{polylog}(n)\). If the proof is correct, the test accepts surely; if it accepts with probability at least \(1-\gamma\), the submitted string is 1-close to the accepted set. The scan’s repeated-query count is not clear.

<a id="pdf-ffbe9c7b3306-p204-b002"></a>
<!-- pdf-source: page=204; block=2; confidence=0.88 -->
The notes summarize approximation hardness results: Håstad's results include NP-hardness of $(p+\delta,1−\delta)$ approximation for Max-E3-Lin$(\bmod p)$ and $(7/8,1)$ for Max-CSP$({\rm NAE}_4)$; the cited Max-Cut bound is $(11/16+\delta,3/4)$, and Unique-Games$(q)$ has a cited $(3/8+q^{−\Theta(1)},1/2)$ hardness bound. They identify the Unique Games Conjecture and its origins, attribute the generic Dictator-vs.-No-Notables implication (Theorem 7.40) to work of Khot et al. and an explicit proof to Austrin, and note Raghavendra's near-complete optimal-inapproximability theory under that conjecture.

<a id="pdf-ffbe9c7b3306-p205-b001"></a>
<!-- pdf-source: page=205; block=1; confidence=1.00 -->
## 7.5. Exercises and notes

<a id="pdf-ffbe9c7b3306-p205-b002"></a>
<!-- pdf-source: page=205; block=2; confidence=0.99 -->
Notes credit Exercise 7.8 to Bellare–Goldreich–Sudan and Parnas–Ron–Samorodnitsky; Exercise 7.21 uses conditional expectations, Exercise 7.23 relates to PCP folding, and Exercise 7.31’s bug and remedy are noted as uncommon in the literature.

<a id="pdf-ffbe9c7b3306-p207-b001"></a>
<!-- pdf-source: page=207; block=1; confidence=1.00 -->
# Chapter 8: Generalized domains

<a id="pdf-ffbe9c7b3306-p207-b002"></a>
<!-- pdf-source: page=207; block=2; confidence=0.98 -->
Much of Boolean-function analysis extends to functions on product probability spaces $\Omega_1\times\cdots\times\Omega_n$ with distribution $\pi_1\otimes\cdots\otimes\pi_n$. The derivative $D_i$ does not extend when $|\Omega_i|>2$, though the Laplacian $L_i$ does; hypercontractivity depends strongly on the coordinate distributions. The chapter assumes a common space and measure for all coordinates to simplify notation, including biased-cube and abelian-group cases. Range generalization is deferred to Exercise 8.33.

<a id="pdf-ffbe9c7b3306-p207-b003"></a>
<!-- pdf-source: page=207; block=3; confidence=1.00 -->
## 8.1. Fourier bases for product spaces

<a id="pdf-ffbe9c7b3306-p207-b004"></a>
<!-- pdf-source: page=207; block=4; confidence=1.00 -->
The section begins the study of functions on finite product probability spaces.

<a id="pdf-ffbe9c7b3306-p207-b005"></a>
<!-- pdf-source: page=207; block=5; confidence=1.00 -->
**Definition 8.1.** Let \((\Omega,\pi)\) be a finite probability space with \(|\Omega|\ge2\) and full support. Define \(L^2(\Omega^n,\pi^{\otimes n})\) to be the real inner-product space of functions \(f:\Omega^n\to\mathbb R\), with \(\langle f,g\rangle=\mathbb E_{x\sim\pi^{\otimes n}}[f(x)g(x)]\).

<a id="pdf-ffbe9c7b3306-p208-b001"></a>
<!-- pdf-source: page=208; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p208-b002"></a>
<!-- pdf-source: page=208; block=2; confidence=1.00 -->
Example domain: three abstract points with uniform probability 1/3 each.

<a id="pdf-ffbe9c7b3306-p208-b003"></a>
<!-- pdf-source: page=208; block=3; confidence=1.00 -->
Use \(\pi_{1/2}\) for the uniform probability distribution on \(\{-1,1\}\); then \(L^2(\{-1,1\}^n)\) abbreviates \(L^2(\{-1,1\}^n,\pi_{1/2}^{\otimes n})\). The usual \(L^p\)-norms and restriction notation extend to \(L^2(\Omega^n,\pi^{\otimes n})\).

<a id="pdf-ffbe9c7b3306-p208-b004"></a>
<!-- pdf-source: page=208; block=4; confidence=0.98 -->
The chapter seeks useful Fourier-type bases for product spaces, generalizing the parity basis. For $S\subseteq[n]$, write $\chi_S(x)=\prod_{i=1}^n\phi_{S_i}(x_i)$ using the indicator-vector encoding of $S$, with $\phi_0\equiv1$ and $\phi_1=\mathrm{id}$.

<a id="pdf-ffbe9c7b3306-p208-b005"></a>
<!-- pdf-source: page=208; block=5; confidence=1.00 -->
**Definition 8.5.** For finite $\Omega$ of size $m$, the indicator (standard) basis of $L^2(\Omega,\pi)$ consists of $\mathbf 1_x$ for $x\in\Omega$, where $\mathbf 1_x(y)=1$ if $y=x$ and $0$ otherwise.

<a id="pdf-ffbe9c7b3306-p208-b006"></a>
<!-- pdf-source: page=208; block=6; confidence=0.99 -->
**Fact 8.6.** The indicator functions are nonzero, pairwise orthogonal, and spanning; hence they form a basis and $\dim L^2(\Omega,\pi)=m$.

<a id="pdf-ffbe9c7b3306-p208-b007"></a>
<!-- pdf-source: page=208; block=7; confidence=0.98 -->
For $\Omega^n$, the indicator basis is indexed by points of $\Omega^n$ and the space has dimension $m^n$. A function expands as $f=\sum_{x\in\Omega^n}f(x)\mathbf 1_x$; these coefficients merely record its values.

<a id="pdf-ffbe9c7b3306-p209-b001"></a>
<!-- pdf-source: page=209; block=1; confidence=1.00 -->
## 8.1. Fourier bases for product spaces

<a id="pdf-ffbe9c7b3306-p209-b002"></a>
<!-- pdf-source: page=209; block=2; confidence=0.97 -->
A basis $\phi_0,\ldots,\phi_{m-1}$ of $L^2(\Omega,\pi)$ induces a basis of $L^2(\Omega^n,\pi^{\otimes n})$ from all coordinate products $\prod_{j=1}^n\phi_{i_j}(x_j)$. If the original basis is orthonormal, the product basis is orthonormal by product measure factorization. Parseval then gives $\mathbb E[f^2]=\sum_{i=0}^{m-1}c_i^2$ when $f=\sum_i c_i\phi_i$.

<a id="pdf-ffbe9c7b3306-p209-b003"></a>
<!-- pdf-source: page=209; block=3; confidence=0.99 -->
If an orthonormal basis has $\phi_0\equiv1$, then $\mathbb E[\phi_i]=0$ for $i>0$. Thus for $f=\sum_{i=0}^{m-1}c_i\phi_i$, $\mathbb E[f]=c_0$ and $\operatorname{Var}(f)=\sum_{i>0}c_i^2$.

<a id="pdf-ffbe9c7b3306-p209-b004"></a>
<!-- pdf-source: page=209; block=4; confidence=1.00 -->
**Definition 8.7.** A Fourier basis of $L^2(\Omega,\pi)$ is an orthonormal basis $\phi_0,\ldots,\phi_{m-1}$ with $\phi_0\equiv1$.

<a id="pdf-ffbe9c7b3306-p209-b005"></a>
<!-- pdf-source: page=209; block=5; confidence=0.99 -->
**Example 8.8.** The parity functions form a Fourier basis for the uniform Boolean cube. **Remark 8.9.** Such bases exist by extending $\{1\}$ to a basis and applying Gram–Schmidt, but need not be unique; for the one-bit space, both $\{1,\mathrm{id}\}$ and $\{1,-\mathrm{id}\}$ work.

<a id="pdf-ffbe9c7b3306-p209-b006"></a>
<!-- pdf-source: page=209; block=6; confidence=0.96 -->
**Example 8.10.** For uniform $\Omega=\{a,b,c\}$, one Fourier basis has $\phi_0\equiv1$, $\phi_1(a)=\sqrt2$, $\phi_1(b)=\phi_1(c)=-\sqrt2/2$, and $\phi_2(a)=0$, $\phi_2(b)=\sqrt6/2$, $\phi_2(c)=-\sqrt6/2$.

<a id="pdf-ffbe9c7b3306-p210-b001"></a>
<!-- pdf-source: page=210; block=1; confidence=1.00 -->
A Fourier basis on $L^2(\Omega,\pi)$ yields a Fourier basis on each product space by taking coordinatewise products.

<a id="pdf-ffbe9c7b3306-p210-b002"></a>
<!-- pdf-source: page=210; block=2; confidence=0.99 -->
**Definition 8.11.** An \(n\)-dimensional multi-index is \(\alpha\in\mathbb N^n\). Write \(\operatorname{supp}(\alpha)=\{i:\alpha_i\ne0\}\), \(\#\alpha=|\operatorname{supp}(\alpha)|\), and \(|\alpha|=\sum_i\alpha_i\). Write \(\alpha\in\mathbb N^n_{<m}\) to emphasize each coordinate is in \(\{0,1,\ldots,m-1\}\).

<a id="pdf-ffbe9c7b3306-p210-b003"></a>
<!-- pdf-source: page=210; block=3; confidence=0.99 -->
**Definition 8.12.** Given $\phi_0,\ldots,\phi_{m-1}\in L^2(\Omega,\pi)$ and $\alpha\in[m]^n$, set $\phi_\alpha(x)=\prod_{i=1}^n\phi_{\alpha_i}(x_i)$.

<a id="pdf-ffbe9c7b3306-p210-b004"></a>
<!-- pdf-source: page=210; block=4; confidence=0.99 -->
**Proposition 8.13.** If $\phi_0,\ldots,\phi_{m-1}$ is a Fourier basis of $L^2(\Omega,\pi)$, then $(\phi_\alpha)_{\alpha\in[m]^n}$ is a Fourier basis of $L^2(\Omega^n,\pi^{\otimes n})$; the zero multi-index gives the constant function $1$.

<a id="pdf-ffbe9c7b3306-p210-b005"></a>
<!-- pdf-source: page=210; block=5; confidence=1.00 -->
**Proof.** For $\alpha,\beta\in[m]^n$, product factorization and orthonormality give $\langle\phi_\alpha,\phi_\beta\rangle=\prod_{i=1}^n\mathbb E_{x_i\sim\pi}[\phi_{\alpha_i}(x_i)\phi_{\beta_i}(x_i)]=\prod_{i=1}^n\mathbf1_{\alpha_i=\beta_i}=\mathbf1_{\alpha=\beta}$. Thus the products are orthonormal and linearly independent. There are $m^n$ of them, equal to the dimension of the product space, so they form a basis.

<a id="pdf-ffbe9c7b3306-p210-b006"></a>
<!-- pdf-source: page=210; block=6; confidence=0.99 -->
Every function in the product space expands in this basis; denote its coefficient on $\phi_\alpha$ by $\widehat f(\alpha)$.

<a id="pdf-ffbe9c7b3306-p211-b001"></a>
<!-- pdf-source: page=211; block=1; confidence=1.00 -->
## 8.2. Generalized Fourier formulas

<a id="pdf-ffbe9c7b3306-p211-b002"></a>
<!-- pdf-source: page=211; block=2; confidence=0.96 -->
**Definition 8.14.** For a fixed Fourier basis \(\phi_0,\ldots,\phi_{m-1}\) of \(L^2(\Omega,\pi)\), every \(f\in L^2(\Omega^n,\pi^{\otimes n})\) has a unique expansion \(f=\sum_{\alpha\in\{0,\ldots,m-1\}^n}\widehat f(\alpha)\phi_\alpha\), where \(\widehat f(\alpha)=\langle f,\phi_\alpha\rangle\).

<a id="pdf-ffbe9c7b3306-p211-b003"></a>
<!-- pdf-source: page=211; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p211-b004"></a>
<!-- pdf-source: page=211; block=4; confidence=0.98 -->
The section develops familiar probabilistic and combinatorial quantities as Fourier formulas that do not depend on the chosen product basis.

<a id="pdf-ffbe9c7b3306-p211-b005"></a>
<!-- pdf-source: page=211; block=5; confidence=0.94 -->
**Proposition 8.16.** For \(f,g\in L^2(\Omega^n,\pi^{\otimes n})\) and any fixed product Fourier basis,
\[
\mathbb E[f]=\widehat f(0),\qquad \mathbb E[f^2]=\sum_\alpha \widehat f(\alpha)^2\quad(\text{Parseval}),
\]
\[
\operatorname{Var}[f]=\sum_{\alpha\ne 0}\widehat f(\alpha)^2,\qquad
\langle f,g\rangle=\sum_\alpha\widehat f(\alpha)\widehat g(\alpha)\quad(\text{Plancherel}),
\]
\[
\operatorname{Cov}[f,g]=\sum_{\alpha\ne 0}\widehat f(\alpha)\widehat g(\alpha).
\]

<a id="pdf-ffbe9c7b3306-p212-b001"></a>
<!-- pdf-source: page=212; block=1; confidence=0.99 -->
**Proof.** Plancherel follows by expanding \(f\) and \(g\) in the product basis and using orthonormality:
\[
\langle f,g\rangle
=\left\langle\sum_\alpha\widehat f(\alpha)\phi_\alpha,\sum_\beta\widehat g(\beta)\phi_\beta\right\rangle
=\sum_\alpha\widehat f(\alpha)\widehat g(\alpha).
\]
The other identities follow from this and the basis expansion (Exercise 8.6).

<a id="pdf-ffbe9c7b3306-p212-b002"></a>
<!-- pdf-source: page=212; block=2; confidence=0.99 -->
**Definition 8.17.** For \(J\subseteq[n]\), let \(\bar J=[n]\setminus J\). Define \(f^{\subseteq J}(x)=\mathbb E_{x'\sim\pi^{\otimes\bar J}}[f(x_J,x')]\), where coordinates outside \(J\) are resampled independently from \(\pi\).

<a id="pdf-ffbe9c7b3306-p212-b003"></a>
<!-- pdf-source: page=212; block=3; confidence=0.95 -->
**Remark 8.18.** The singleton operator \(\mathbb E_i\) agrees with Definition 2.23; Exercise 8.7 asks for verification that \(\mathbb E_J\) is a self-adjoint linear projection.

<a id="pdf-ffbe9c7b3306-p212-b004"></a>
<!-- pdf-source: page=212; block=4; confidence=0.99 -->
**Proposition 8.19.** For \(J\subseteq[n]\), \(f\in L^2(\Omega^n,\pi^{\otimes n})\), and any fixed product Fourier basis,
\[
f^{\subseteq J}=\sum_{\operatorname{supp}(\alpha)\subseteq J}\widehat f(\alpha)\phi_\alpha.
\]

<a id="pdf-ffbe9c7b3306-p212-b005"></a>
<!-- pdf-source: page=212; block=5; confidence=0.94 -->
**Proof.** By linearity it suffices to apply \(\mathbb E_J\) to each basis function. If \(\operatorname{supp}(\alpha)\subseteq J\), then \(\phi_\alpha\) depends only on coordinates in \(J\), so \(\mathbb E_J\phi_\alpha=\phi_\alpha\). Otherwise, averaging a nonconstant coordinate factor outside \(J\) gives zero, hence \(\mathbb E_J\phi_\alpha=0\). The calculation continues on page 213.

<a id="pdf-ffbe9c7b3306-p213-b001"></a>
<!-- pdf-source: page=213; block=1; confidence=0.91 -->
**Proof (continued).** Writing the basis function as a product of its factors on and outside \(J\), a factor indexed outside \(J\) has mean zero when its index is nonzero. Thus if \(\operatorname{supp}(\alpha)\nsubseteq J\), then for every \(x\), \(\mathbb E_{x'\sim\pi^{\otimes\bar J}}[\phi_\alpha(x_J,x')]=0\), completing the basis-function calculation.

<a id="pdf-ffbe9c7b3306-p213-b002"></a>
<!-- pdf-source: page=213; block=2; confidence=0.99 -->
**Corollary 8.20.** If \(f\in L^2(\Omega^n,\pi^{\otimes n})\) depends only on coordinates in \(J\subseteq[n]\), then \(\widehat f(\alpha)=0\) whenever \(\operatorname{supp}(\alpha)\nsubseteq J\).

<a id="pdf-ffbe9c7b3306-p213-b003"></a>
<!-- pdf-source: page=213; block=3; confidence=0.99 -->
**Proof.** Since \(f=f^{\subseteq J}\), the claim follows from Proposition 8.19.

<a id="pdf-ffbe9c7b3306-p213-b004"></a>
<!-- pdf-source: page=213; block=4; confidence=0.98 -->
**Corollary 8.21.** For \(i\in[n]\) and \(f\in L^2(\Omega^n,\pi^{\otimes n})\), in any fixed product Fourier basis,
\[
\mathbb E_i f=\sum_{\alpha:\alpha_i=0}\widehat f(\alpha)\phi_\alpha.
\]

<a id="pdf-ffbe9c7b3306-p213-b005"></a>
<!-- pdf-source: page=213; block=5; confidence=0.96 -->
**Definition 8.22.** For \(i\in[n]\), the coordinate Laplacian is the self-adjoint projection \(L_i f=f-\mathbb E_i f\). Define
\[
\operatorname{Inf}_i[f]=\langle f,L_i f\rangle=\langle L_i f,L_i f\rangle,
\qquad I[f]=\sum_{i=1}^n\operatorname{Inf}_i[f].
\]
Here \(L_i f\) is the component depending on coordinate \(i\).

<a id="pdf-ffbe9c7b3306-p213-b006"></a>
<!-- pdf-source: page=213; block=6; confidence=0.98 -->
**Proposition 8.23.** For \(i\in[n]\), \(f\in L^2(\Omega^n,\pi^{\otimes n})\), and any fixed product Fourier basis,
\[
L_i f=\sum_{\alpha:\alpha_i\ne0}\widehat f(\alpha)\phi_\alpha,
\qquad \operatorname{Inf}_i[f]=\sum_{\alpha:\alpha_i\ne0}\widehat f(\alpha)^2,
\qquad I[f]=\sum_\alpha |\alpha|\,\widehat f(\alpha)^2,
\]
where \(|\alpha|\) is the number of nonzero coordinates of \(\alpha\).

<a id="pdf-ffbe9c7b3306-p213-b007"></a>
<!-- pdf-source: page=213; block=7; confidence=0.99 -->
**Proof.** The first identity follows from Corollary 8.21, the second from Plancherel, and the third by summing the coordinate influences over \(i\).

<a id="pdf-ffbe9c7b3306-p213-b008"></a>
<!-- pdf-source: page=213; block=8; confidence=0.98 -->
The text points to Exercise 2.21 for additional useful formulas; those formulas are not included on these pages.

<a id="pdf-ffbe9c7b3306-p214-b001"></a>
<!-- pdf-source: page=214; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p214-b002"></a>
<!-- pdf-source: page=214; block=2; confidence=0.98 -->
**Proposition 8.24.** For $i\in[n]$ and $f\in L^2(\Omega^n,\pi^{\otimes n})$, the influence is the expected variance over resampling coordinate $i$:
\[
\operatorname{Inf}_i[f]=\mathbb E_{x\sim\pi^{\otimes n}}\!\left[\operatorname{Var}_{x_i'\sim\pi}\big[f(x_1,\ldots,x_{i-1},x_i',x_{i+1},\ldots,x_n)\big]\right].
\]
If $f$ is $\{-1,1\}$-valued, then $\operatorname{Inf}_i[f]=\mathbb E[|L_i f|]=2\Pr[f(x)\ne f(x_{-i},x_i')]$, where $x\sim\pi^{\otimes n}$ and $x_i'\sim\pi$.

<a id="pdf-ffbe9c7b3306-p214-b003"></a>
<!-- pdf-source: page=214; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p214-b004"></a>
<!-- pdf-source: page=214; block=4; confidence=0.99 -->
The definitions of noise and noise stability are extended to finite product probability spaces.

<a id="pdf-ffbe9c7b3306-p214-b005"></a>
<!-- pdf-source: page=214; block=5; confidence=0.96 -->
**Definition 8.26.** For a finite product probability space $(\Omega^n,\pi^{\otimes n})$, $\rho\in[0,1]$, and $x\in\Omega^n$, the random point $y\sim N_\rho(x)$ is formed independently in each coordinate: retain $x_i$ with probability $1-\rho$, and draw from $\pi$ with probability $\rho$. If $x\sim\pi^{\otimes n}$ and $y\sim N_\rho(x)$, $(x,y)$ is a $\rho$-correlated pair; the joint law is symmetric.

<a id="pdf-ffbe9c7b3306-p214-b006"></a>
<!-- pdf-source: page=214; block=6; confidence=0.99 -->
**Definition 8.27.** The noise operator and stability are
\[
T_\rho f(x)=\mathbb E_{y\sim N_\rho(x)}[f(y)],\qquad
\operatorname{Stab}_\rho[f]=\langle f,T_\rho f\rangle=\mathbb E_{(x,y)\ \rho\text{-correlated}}[f(x)f(y)].
\]

<a id="pdf-ffbe9c7b3306-p214-b007"></a>
<!-- pdf-source: page=214; block=7; confidence=0.95 -->
**Proposition 8.28.** For any fixed product Fourier basis and $\rho\in[0,1]$,
\[
T_\rho f=\sum_{\alpha\in\Lambda^n}\rho^{|\alpha|}\widehat f(\alpha)\phi_\alpha,
\qquad
\operatorname{Stab}_\rho[f]=\sum_{\alpha\in\Lambda^n}\rho^{|\alpha|}\widehat f(\alpha)^2,
\]
where $|\alpha|$ denotes the number of nonzero coordinates of $\alpha$.

<a id="pdf-ffbe9c7b3306-p215-b001"></a>
<!-- pdf-source: page=215; block=1; confidence=1.00 -->
## 8.2. Generalized Fourier formulas

<a id="pdf-ffbe9c7b3306-p215-b002"></a>
<!-- pdf-source: page=215; block=2; confidence=0.97 -->
**Proof.** Choose a random subset $J\subseteq[n]$ by including each coordinate independently with probability $\rho$. By definition, $T_\rho f(x)=\mathbb E_J[f^{\subseteq J}(x)]$. Expanding $f^{\subseteq J}$ in the product Fourier basis and using $\Pr[\operatorname{supp}(\alpha)\subseteq J]=\rho^{|\alpha|}$ gives the operator formula. The stability identity follows by Plancherel.

<a id="pdf-ffbe9c7b3306-p215-b003"></a>
<!-- pdf-source: page=215; block=3; confidence=0.98 -->
The Fourier formula for $T_\rho f$ also defines the operator for $\rho$ outside $[0,1]$.

<a id="pdf-ffbe9c7b3306-p215-b004"></a>
<!-- pdf-source: page=215; block=4; confidence=0.98 -->
Stable influences are defined with a factor of $\rho^{-1}$ to agree with the Boolean-cube convention.

<a id="pdf-ffbe9c7b3306-p215-b005"></a>
<!-- pdf-source: page=215; block=5; confidence=0.95 -->
**Definition 8.30.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, $\rho\in(0,1]$, and $i\in[n]$, set
\[
\operatorname{Inf}^{(\rho)}_i[f]=\rho^{-1}\operatorname{Stab}_\rho[L_i f]=\sum_{\alpha:\alpha_i\ne0}\rho^{|\alpha|-1}\widehat f(\alpha)^2,
\qquad
I^{(\rho)}[f]=\sum_{i=1}^n\operatorname{Inf}^{(\rho)}_i[f].
\]

<a id="pdf-ffbe9c7b3306-p215-b006"></a>
<!-- pdf-source: page=215; block=6; confidence=0.98 -->
Stable influences identify notable coordinates, whose number admits a bound.

<a id="pdf-ffbe9c7b3306-p215-b007"></a>
<!-- pdf-source: page=215; block=7; confidence=0.99 -->
**Proposition 8.31.** Suppose \(\operatorname{Var}[f]\le1\). Given \(0<\delta<1\) and \(0<\varepsilon\le1\), let \(J=\{i\in[n]:\operatorname{Inf}^{(1-\delta)}_i[f]\ge\varepsilon\}\). Then \(|J|\le1/(\delta\varepsilon)\).

<a id="pdf-ffbe9c7b3306-p215-b008"></a>
<!-- pdf-source: page=215; block=8; confidence=0.98 -->
For general product spaces, degree is defined intrinsically through sums of functions depending on few coordinates.

<a id="pdf-ffbe9c7b3306-p215-b009"></a>
<!-- pdf-source: page=215; block=9; confidence=0.97 -->
**Definition 8.32.** For nonzero $f\in L^2(\Omega^n,\pi^{\otimes n})$, $\deg(f)$ is the least $k$ such that $f$ is a sum of $k$-juntas, each depending on at most $k$ coordinates.

<a id="pdf-ffbe9c7b3306-p215-b010"></a>
<!-- pdf-source: page=215; block=10; confidence=0.98 -->
**Proposition 8.33.** For nonzero $f$ and any fixed product Fourier basis,
\[
\deg(f)=\max\{|\alpha|:\widehat f(\alpha)\ne0\}.
\]

<a id="pdf-ffbe9c7b3306-p215-b011"></a>
<!-- pdf-source: page=215; block=11; confidence=0.98 -->
**Proof.** The Fourier expansion expresses $f$ as a sum of terms $\widehat f(\alpha)\phi_\alpha$, each depending on at most $|\alpha|$ coordinates. Hence $\deg(f)\le\max\{|\alpha|:\widehat f(\alpha)\ne0\}$.

<a id="pdf-ffbe9c7b3306-p216-b001"></a>
<!-- pdf-source: page=216; block=1; confidence=0.98 -->
If $f=g_1+\cdots+g_m$ with each $g_i$ depending on at most $k$ coordinates, Corollary 8.20 implies each $g_i$ has Fourier support only on indices with $|\alpha|\le k$. Since $\widehat f(\alpha)=\sum_i\widehat g_i(\alpha)$, the same support restriction holds for $f$, proving the reverse inequality.

<a id="pdf-ffbe9c7b3306-p216-b002"></a>
<!-- pdf-source: page=216; block=2; confidence=1.00 -->
## 8.3. Orthogonal decomposition

<a id="pdf-ffbe9c7b3306-p216-b003"></a>
<!-- pdf-source: page=216; block=3; confidence=0.99 -->
The orthogonal decomposition is \(f=\sum_{S\subseteq[n]}f^{=S}\), where each term is the contribution from coordinates in \(S\) beyond contributions from proper subsets of \(S\).

<a id="pdf-ffbe9c7b3306-p216-b004"></a>
<!-- pdf-source: page=216; block=4; confidence=0.98 -->
On the Boolean cube, define $f^{=S}=\widehat f(S)\chi_S$. These components sum to $f$, depend only on coordinates in $S$, and are orthogonal to every function of coordinates $T$ whenever $T\subsetneq S$; distinct components are mutually orthogonal.

<a id="pdf-ffbe9c7b3306-p216-b005"></a>
<!-- pdf-source: page=216; block=5; confidence=0.98 -->
For the Boolean-cube components, the projection onto coordinates $J$ satisfies
\[
f^{\subseteq J}=\sum_{S\subseteq J}f^{=S}. \tag{8.2}
\]
The text proposes inverting this identity to define the components without a Fourier basis.

<a id="pdf-ffbe9c7b3306-p216-b006"></a>
<!-- pdf-source: page=216; block=6; confidence=0.97 -->
For general $f\in L^2(\Omega^n,\pi^{\otimes n})$, the projection functions $f^{\subseteq J}$ are already defined probabilistically; the section begins applying the inversion of (8.2) to them.

<a id="pdf-ffbe9c7b3306-p217-b001"></a>
<!-- pdf-source: page=217; block=1; confidence=1.00 -->
## 8.3. Orthogonal decomposition

<a id="pdf-ffbe9c7b3306-p217-b002"></a>
<!-- pdf-source: page=217; block=2; confidence=0.98 -->
Set $f^{=\varnothing}=f^{\subseteq\varnothing}=\mathbb E[f]$. For a singleton, $f^{=\{j\}}=f^{\subseteq\{j\}}-f^{\subseteq\varnothing}$, so $f^{=\{j\}}(x)=\mathbb E[f\mid x_j]-\mathbb E[f]$. For two coordinates, $f^{=\{i,j\}}=f^{\subseteq\{i,j\}}-f^{\subseteq\{i\}}-f^{\subseteq\{j\}}+f^{\subseteq\varnothing}$. These cases motivate defining all components by inclusion–exclusion.

<a id="pdf-ffbe9c7b3306-p217-b003"></a>
<!-- pdf-source: page=217; block=3; confidence=0.99 -->
**Lemma 8.34.** If $f,g\in L^2(\Omega^n,\pi^{\otimes n})$, with $f$ depending only on coordinates in $I\subseteq[n]$ and $g$ only on coordinates in $J\subseteq[n]$, then $\langle f,g\rangle=\langle f^{\subseteq I\cap J},g^{\subseteq I\cap J}\rangle$.

<a id="pdf-ffbe9c7b3306-p217-b004"></a>
<!-- pdf-source: page=217; block=4; confidence=0.97 -->
**Proof.** Assume $I\cup J=[n]$ and split the input into the shared coordinates $x_{I\cap J}$ and the disjoint parts $x_{I\setminus J},x_{J\setminus I}$. Independence lets the expectation of $f(x_{I\cap J},x_{I\setminus J})g(x_{I\cap J},x_{J\setminus I})$ factor, conditional on $x_{I\cap J}$, into the product of the two conditional expectations. These are $f^{\subseteq I\cap J}$ and $g^{\subseteq I\cap J}$, giving the stated inner product.

<a id="pdf-ffbe9c7b3306-p217-b005"></a>
<!-- pdf-source: page=217; block=5; confidence=1.00 -->
The lemma is used to establish the orthogonal decomposition theorem.

<a id="pdf-ffbe9c7b3306-p218-b001"></a>
<!-- pdf-source: page=218; block=1; confidence=0.99 -->
**Theorem 8.35.** Every \(f\in L^2(\Omega^n,\pi^{\otimes n})\) has a unique decomposition \(f=\sum_{S\subseteq[n]}f^{=S}\) such that (1) \(f^{=S}\) depends only on coordinates in \(S\); (2) if \(T\subsetneq S\) and \(g\) depends only on coordinates in \(T\), then \(\langle f^{=S},g\rangle=0\). It also satisfies (3) this orthogonality whenever \(S\not\subseteq T\); (4) \(\langle f^{=S},f^{=T}\rangle=0\) for \(S\ne T\); (5) \(\sum_{S\subseteq T}f^{=S}=f^{\subseteq T}\); (6) the map \(f\mapsto f^{=S}\) is linear.

<a id="pdf-ffbe9c7b3306-p218-b002"></a>
<!-- pdf-source: page=218; block=2; confidence=0.99 -->
**Proof.** Define, for each $S\subseteq[n]$, $f^{=S}=\sum_{J\subseteq S}(-1)^{|S|-|J|}f^{\subseteq J}$. Since $f^{\subseteq J}$ depends only on $J$, property (1) holds. Inclusion–exclusion gives (5), and linearity of the maps $f\mapsto f^{\subseteq J}$ gives (6).

<a id="pdf-ffbe9c7b3306-p218-b003"></a>
<!-- pdf-source: page=218; block=3; confidence=0.98 -->
Suppose $T\subsetneq S$ and $g$ depends only on coordinates in $T$. Expand
$$\langle f^{=S},g\rangle=\sum_{J\subseteq S}(-1)^{|S|-|J|}\langle f^{\subseteq J},g\rangle. \tag{8.3}$$
Choose $i\in S\setminus T$ and pair each $J'$ not containing $i$ with $J''=J'\cup\{i\}$. Lemma 8.34 gives $\langle f^{\subseteq J''},g\rangle=\langle f^{\subseteq J''\cap T},g^{\subseteq T}\rangle=\langle f^{\subseteq J'\cap T},g^{\subseteq T}\rangle=\langle f^{\subseteq J'},g\rangle$. The paired signs are opposite, so the terms cancel and the inner product is zero.

<a id="pdf-ffbe9c7b3306-p218-b004"></a>
<!-- pdf-source: page=218; block=4; confidence=0.98 -->
Assuming (1), Lemma 8.34 reduces $\langle f^{=S},g\rangle$ to $\langle f^{=S},g^{\subseteq S\cap T}\rangle$. If $S\not\subseteq T$, then $S\cap T\subsetneq S$, so (2) implies (3). For $S\ne T$, either $S\not\subseteq T$ or $T\not\subseteq S$, yielding (4).

<a id="pdf-ffbe9c7b3306-p219-b001"></a>
<!-- pdf-source: page=219; block=1; confidence=0.95 -->
To prove uniqueness, subtract two decompositions satisfying (1) and (2), obtaining a decomposition of zero with those properties. Properties (1) and (2) imply (4), hence Parseval’s identity $\langle f,f\rangle=\sum_{S\subseteq[n]}\|f^{=S}\|_2^2$. Applying this to the zero function forces each component to vanish.

<a id="pdf-ffbe9c7b3306-p219-b002"></a>
<!-- pdf-source: page=219; block=2; confidence=1.00 -->
The orthogonal components can be described by grouping Fourier coefficients according to their support.

<a id="pdf-ffbe9c7b3306-p219-b003"></a>
<!-- pdf-source: page=219; block=3; confidence=0.97 -->
**Proposition 8.36.** If $f=\sum_{S\subseteq[n]}f^{=S}$ is its orthogonal decomposition and $\phi_0,\ldots,\phi_{m-1}$ is a Fourier basis for $L^2(\Omega,\pi)$, then
$$f^{=S}=\sum_{\substack{\alpha\in\{0,\ldots,m-1\}^n\\ \operatorname{supp}(\alpha)=S}}\widehat f(\alpha)\phi_\alpha. \tag{8.4}$$

<a id="pdf-ffbe9c7b3306-p219-b004"></a>
<!-- pdf-source: page=219; block=4; confidence=0.98 -->
**Proof.** Define the components by (8.4). Their sum is $f$, and each depends only on coordinates in $S$. If $g$ depends only on coordinates in $T\subsetneq S$, then Corollary 8.20 gives disjoint Fourier supports, so Plancherel’s identity implies $\langle f^{=S},g\rangle=0$. Theorem 8.35’s uniqueness identifies these as the orthogonal components.

<a id="pdf-ffbe9c7b3306-p219-b005"></a>
<!-- pdf-source: page=219; block=5; confidence=0.98 -->
In the example, \(f^{=\varnothing}=\mathbb E[f]=1/9\). For \(i=1,2\), \(f^{=\{i\}}\) equals \(2/9\) if \(x_i=c\) and \(-1/9\) otherwise. Finally, \(f^{=\{1,2\}}=f-f^{=\varnothing}-f^{=\{1\}}-f^{=\{2\}}\), giving \(4/9\) if both inputs are \(c\), \(-2/9\) if exactly one is \(c\), and \(1/9\) otherwise.

<a id="pdf-ffbe9c7b3306-p219-b006"></a>
<!-- pdf-source: page=219; block=6; confidence=0.98 -->
The Fourier identities can be expressed via the decomposition as
$$\langle f,g\rangle=\sum_{S\subseteq[n]}\langle f^{=S},g^{=S}\rangle,\qquad \operatorname{Inf}_i[f]=\sum_{S\ni i}\|f^{=S}\|_2^2,\qquad T_\rho f=\sum_{S\subseteq[n]}\rho^{|S|}f^{=S}.$$

<a id="pdf-ffbe9c7b3306-p220-b001"></a>
<!-- pdf-source: page=220; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p220-b002"></a>
<!-- pdf-source: page=220; block=2; confidence=0.97 -->
**Definition 8.38.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, define its degree-$k$ part by $f^{=k}=\sum_{|S|=k}f^{=S}$ and its degree-$k$ weight by $W_k[f]=\|f^{=k}\|_2^2$. Also, $f^{\le k}=\sum_{|S|\le k}f^{=S}$ and $W_{>k}[f]=\sum_{|S|>k}\|f^{=S}\|_2^2$.

<a id="pdf-ffbe9c7b3306-p220-b003"></a>
<!-- pdf-source: page=220; block=3; confidence=0.98 -->
## 8.4. $p$-biased analysis

The domain is $\{-1,1\}^n$ with independent coordinates distributed as $\pi_p(-1)=p$, $\pi_p(1)=q=1-p$. Its mean is $\mu=q-p=1-2p$; notation $\Pr_{\pi_p}$ and $\mathbb E_{\pi_p}$ abbreviates probability and expectation under $\pi_p^{\otimes n}$.

<a id="pdf-ffbe9c7b3306-p220-b004"></a>
<!-- pdf-source: page=220; block=4; confidence=0.98 -->
**Definition 8.39.** For $p$-biased analysis, define $\phi(x_i)=(x_i-\mu)/\sigma$, where $\mu=\mathbb E_{x_i\sim\pi_p}[x_i]=q-p=1-2p$ and $\sigma=\operatorname{stddev}_{x_i\sim\pi_p}(x_i)=\sqrt{4pq}=2\sqrt{p(1-p)}$. Then $\sigma^2=1-\mu^2$, $\phi(1)=\sqrt{p/q}$, and $\phi(-1)=-\sqrt{q/p}$.

<a id="pdf-ffbe9c7b3306-p221-b001"></a>
<!-- pdf-source: page=221; block=1; confidence=0.99 -->
The functions $1,\phi$ form an orthonormal basis since $\mathbb E[\phi]=0$ and $\mathbb E[\phi^2]=1$.

<a id="pdf-ffbe9c7b3306-p221-b002"></a>
<!-- pdf-source: page=221; block=2; confidence=0.99 -->
**Definition 8.40.** In $L^2(\{-1,1\}^n,\pi_p^{\otimes n})$, define $\phi_S(x)=\prod_{i\in S}\phi(x_i)$ and $\widehat f(S)=\mathbb E_{x\sim\pi_p^{\otimes n}}[f(x)\phi_S(x)]$. Thus $f(x)=\sum_{S\subseteq[n]}\widehat f(S)\phi_S(x)$. In general, $\phi_S\phi_T\ne\phi_{S\triangle T}$.

<a id="pdf-ffbe9c7b3306-p221-b003"></a>
<!-- pdf-source: page=221; block=3; confidence=0.99 -->
For the dictator $\chi_i(x)=x_i$, the biased expansion follows from $x_i=\mu+\sigma\phi(x_i)$: $\widehat\chi_i(\varnothing)=\mu$, $\widehat\chi_i(\{i\})=\sigma$, and all other coefficients vanish.

<a id="pdf-ffbe9c7b3306-p221-b004"></a>
<!-- pdf-source: page=221; block=4; confidence=0.99 -->
Writing $\phi_i=\phi(x_i)$ gives the change of variables
\[
\phi_i=\frac{x_i-\mu}{\sigma}\quad\Longleftrightarrow\quad x_i=\mu+\sigma\phi_i.\tag{8.5}
\]
Substitution into the usual Fourier expansion yields the biased expansion.

<a id="pdf-ffbe9c7b3306-p221-b005"></a>
<!-- pdf-source: page=221; block=5; confidence=0.91 -->
For the selection function on three bits, $\operatorname{Sel}$ returns $x_2$ when $x_1=-1$ and $x_3$ when $x_1=1$. Substituting (8.5) into its usual expansion gives
\[
\operatorname{Sel}(x_1,x_2,x_3)=\mu+\left(\frac12+\frac12\mu\right)\sigma\phi_2+\left(\frac12-\frac12\mu\right)\sigma\phi_3-\frac12\sigma^2\phi_1\phi_2+\frac12\sigma^2\phi_1\phi_3.\tag{8.6}
\]

<a id="pdf-ffbe9c7b3306-p222-b001"></a>
<!-- pdf-source: page=222; block=1; confidence=0.94 -->
The nonzero coefficients of $\operatorname{Sel}^{(p)}$ are $\widehat{\operatorname{Sel}^{(p)}}(\varnothing)=\mu$, $\widehat{\operatorname{Sel}^{(p)}}(\{2\})=(\frac12+\frac12\mu)\sigma$, $\widehat{\operatorname{Sel}^{(p)}}(\{3\})=(\frac12-\frac12\mu)\sigma$, $\widehat{\operatorname{Sel}^{(p)}}(\{1,2\})=-\frac12\sigma^2$, and $\widehat{\operatorname{Sel}^{(p)}}(\{1,3\})=\frac12\sigma^2$. For example, $\mathbb E[\operatorname{Sel}^{(p)}]=\mu$ and $\operatorname{Inf}_1[\operatorname{Sel}^{(p)}]=\frac12\sigma^4$.

<a id="pdf-ffbe9c7b3306-p222-b002"></a>
<!-- pdf-source: page=222; block=2; confidence=0.99 -->
**Notation 8.43.** For $f:\{-1,1\}^n\to\mathbb R$ and $p\in(0,1)$, write $f^{(p)}$ for $f$ viewed in $L^2(\{-1,1\}^n,\pi_p^{\otimes n})$.

<a id="pdf-ffbe9c7b3306-p222-b003"></a>
<!-- pdf-source: page=222; block=3; confidence=0.98 -->
The desired derivative on the biased expansion acts as differentiation with respect to $\phi_i$; since $x_i=\mu+\sigma\phi_i$, the chain rule gives $\partial/\partial\phi_i=\sigma\,\partial/\partial x_i$.

<a id="pdf-ffbe9c7b3306-p222-b004"></a>
<!-- pdf-source: page=222; block=4; confidence=0.99 -->
**Definition 8.44.** For $i\in[n]$, define the discrete derivative on $L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ by
\[
D_i f(x)=\sigma\,\frac{f(x^{(i\mapsto 1)})-f(x^{(i\mapsto -1)})}{2}.
\]
This operator depends on $p$ and may be written $D_{\phi_i}=\sigma D_{x_i}$.

<a id="pdf-ffbe9c7b3306-p222-b005"></a>
<!-- pdf-source: page=222; block=5; confidence=0.99 -->
On the biased Fourier expansion, the derivative satisfies
\[
D_i f=\sum_{S\ni i}\widehat f(S)\phi_{S\setminus\{i\}}.\tag{8.7}
\]

<a id="pdf-ffbe9c7b3306-p222-b006"></a>
<!-- pdf-source: page=222; block=6; confidence=0.99 -->
The text proceeds to derive further influence identities, including a biased analogue of Proposition 2.21.

<a id="pdf-ffbe9c7b3306-p223-b001"></a>
<!-- pdf-source: page=223; block=1; confidence=1.00 -->
## 8.4. p-biased analysis

<a id="pdf-ffbe9c7b3306-p223-b002"></a>
<!-- pdf-source: page=223; block=2; confidence=0.98 -->
**Proposition 8.45.** For Boolean-valued $f\in L_2(\{-1,1\}^n,\pi_p^{\otimes n})$, each coordinate influence satisfies $\operatorname{Inf}_i[f]=\sigma^2\Pr_{x\sim\pi_p^{\otimes n}}[f(x)\ne f(x^{\oplus i})]$, and total influence satisfies $I[f]=\sigma^2\mathbb E_{x\sim\pi_p^{\otimes n}}[\operatorname{sens} f(x)]$. If $f$ is monotone, then $\operatorname{Inf}_i[f]=\sigma\widehat f(i)$.

<a id="pdf-ffbe9c7b3306-p223-b003"></a>
<!-- pdf-source: page=223; block=3; confidence=0.97 -->
**Proof.** Using $D_{\phi_i}f=\sigma D_{x_i}f$, $\operatorname{Inf}_i[f]=\mathbb E[(D_{\phi_i}f)^2]=\sigma^2\mathbb E[(D_{x_i}f)^2]$. Since $(D_{x_i}f)^2$ indicates that coordinate $i$ is pivotal, this gives the first identity; summing over $i$ gives the total-influence identity. For monotone $f$, $(D_{x_i}f)^2=D_{x_i}f$, so $\operatorname{Inf}_i[f]=\sigma^2\mathbb E[D_{x_i}f]=\sigma\mathbb E[D_{\phi_i}f]=\sigma\widehat f(i)$.

<a id="pdf-ffbe9c7b3306-p223-b004"></a>
<!-- pdf-source: page=223; block=4; confidence=1.00 -->
The section turns to threshold behavior of Boolean functions, motivated by random graph theory.

<a id="pdf-ffbe9c7b3306-p223-b005"></a>
<!-- pdf-source: page=223; block=5; confidence=0.98 -->
**Definition 8.46.** Encode an undirected graph on $v\ge2$ vertices as a string in $\{\mathrm{True},\mathrm{False}\}^{\binom v2}$ indicating present and absent edges. The distribution $G(v,p)=\pi_p^{\otimes\binom v2}$ is the Erdős–Rényi random graph model. A graph property is a Boolean function on these strings invariant under all permutations of the $v$ vertices; consequently, graph properties are transitive-symmetric functions.

<a id="pdf-ffbe9c7b3306-p223-b006"></a>
<!-- pdf-source: page=223; block=6; confidence=0.97 -->
The examples of graph properties include \(\mathrm{Conn}(G)\), 3-colorability, containing a clique on at least \(k\) vertices, majority on an odd number \(n=\binom v2\) of edges, and having an odd number of edges.

<a id="pdf-ffbe9c7b3306-p224-b001"></a>
<!-- pdf-source: page=224; block=1; confidence=0.96 -->
Graph properties form families indexed by $v$; the property that vertex 1 has a neighbor is not invariant under vertex permutations. Monotone properties include connectedness, containing a $k$-clique, and edge majority; the negation of 3-colorability is also monotone. For a monotone property, one studies its probability under $G(v,p)$ as $p$ varies. The same probability transition applies to any nonconstant monotone Boolean function.

<a id="pdf-ffbe9c7b3306-p224-b002"></a>
<!-- pdf-source: page=224; block=2; confidence=0.98 -->
A figure compares $\Pr_{\pi_p}[f(x)=\mathrm{True}]$ for a dictator, $\mathrm{AND}_2$, and $\mathrm{Maj}_{101}$; the majority curve is steep near $p=1/2$.

<a id="pdf-ffbe9c7b3306-p224-b003"></a>
<!-- pdf-source: page=224; block=3; confidence=0.98 -->
**Margulis–Russo Formula.** For \(f:\{-1,1\}^n\to\{-1,1\}\), with \(\mu=1-2p\), \[\frac{d}{d\mu}\mathbb E[f^{(p)}]=\frac1\sigma\sum_{i=1}^n\widehat f^{(p)}(i).\tag{8.8}\]

<a id="pdf-ffbe9c7b3306-p225-b001"></a>
<!-- pdf-source: page=225; block=1; confidence=0.96 -->
For monotone $f:\{-1,1\}^n\to\{-1,1\}$,
\[
\frac{d}{dp}\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=-1]=\frac{d}{d\mu}\mathbb E[f(p)]=\frac1{\sigma^2}I[f(p)].\tag{8.9}
\]

<a id="pdf-ffbe9c7b3306-p225-b002"></a>
<!-- pdf-source: page=225; block=2; confidence=0.98 -->
The multilinear extension gives \(\mathbb E[f^{(n)}]=T_\mu f(1,\ldots,1)=f(\mu,\ldots,\mu)\). Differentiating, \(\frac{d}{d\mu}f(\mu,\ldots,\mu)=\sum_{i=1}^nD_{x_i}f(\mu,\ldots,\mu)\), which proves (8.8).

<a id="pdf-ffbe9c7b3306-p225-b003"></a>
<!-- pdf-source: page=225; block=3; confidence=0.98 -->
**Remark 8.48.** For a nonconstant monotone Boolean function, $\Pr_{\pi_p}[f(x)=\mathrm{True}]$ is strictly increasing in $p$, since its total influence is positive.

<a id="pdf-ffbe9c7b3306-p225-b004"></a>
<!-- pdf-source: page=225; block=4; confidence=0.91 -->
The majority curve becomes increasingly step-like near $p=1/2$ as its dimension grows; its derivative there equals the uniform total influence, of order $\Theta(\sqrt n)$ by Theorem 2.33. Other examples of sharp thresholds follow.

<a id="pdf-ffbe9c7b3306-p225-b005"></a>
<!-- pdf-source: page=225; block=5; confidence=0.91 -->
**Example 8.49.** For every $\varepsilon>0$, there is a constant $C$ such that
\[
\Pr_{\pi_{1/2-C/\sqrt n}}[\mathrm{Maj}_n=\mathrm{True}]\le\varepsilon,\qquad
\Pr_{\pi_{1/2+C/\sqrt n}}[\mathrm{Maj}_n=\mathrm{True}]\ge1-\varepsilon.
\]

<a id="pdf-ffbe9c7b3306-p225-b006"></a>
<!-- pdf-source: page=225; block=6; confidence=0.96 -->
The clique threshold is \(\mathrm{Clique}_{\log v}(G)\). Its probability tends to 0 for \(p<1/4\) and to 1 for \(p>1/4\). For connectivity, the threshold lies around \(p=(\ln v)/v\), with the displayed lower and upper windows \(\frac{\ln v}{v}(1\mp\frac{\log\log v}{\log v})\).

<a id="pdf-ffbe9c7b3306-p226-b001"></a>
<!-- pdf-source: page=226; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p226-b002"></a>
<!-- pdf-source: page=226; block=2; confidence=0.92 -->
For a nonconstant monotone Boolean function, the probability of output True crosses one half at its critical probability. The text relates sharp thresholds heuristically to large total influence at that probability, via the Margulis–Russo formula, and notes that small influence is connected to junta approximation; sparse critical probabilities require further results.

<a id="pdf-ffbe9c7b3306-p226-b003"></a>
<!-- pdf-source: page=226; block=3; confidence=0.91 -->
**Definition 8.50.** For monotone nonconstant $f:\{\mathrm{True},\mathrm{False}\}^n\to\{\mathrm{True},\mathrm{False}\}$, the critical probability $p_c\in(0,1)$ is the unique value such that $\Pr_{x\sim\pi_{p_c}^{\otimes n}}[f(x)=\mathrm{True}]=1/2$. Set $q_c=1-p_c$, $\mu_c=q_c-p_c=1-2p_c$, and $\sigma_c=\sqrt{4p_cq_c}$.

<a id="pdf-ffbe9c7b3306-p226-b004"></a>
<!-- pdf-source: page=226; block=4; confidence=0.88 -->
The Margulis–Russo formula is invoked to identify the derivative at $p_c$ with total influence scaled by $\sigma_c^{-2}$. Heuristically, a sharp threshold corresponds to superconstant total influence at criticality. The discussion notes that transitive monotone graph properties with $p_c=1/2$ cannot be close to juntas, while sparse critical probabilities are more difficult.

<a id="pdf-ffbe9c7b3306-p227-b001"></a>
<!-- pdf-source: page=227; block=1; confidence=0.98 -->
The characterization of functions with small total influence when $p=o_n(1)$ is described as harder, with work by Friedgut, Bourgain, and Hatami referenced.

<a id="pdf-ffbe9c7b3306-p227-b002"></a>
<!-- pdf-source: page=227; block=2; confidence=1.00 -->
## 8.5. Abelian groups

<a id="pdf-ffbe9c7b3306-p227-b003"></a>
<!-- pdf-source: page=227; block=3; confidence=0.94 -->
For domains with an algebraic addition operation, the uniform distribution on a finite abelian group yields a canonical Fourier basis from group characters; complex-valued functions are used.

<a id="pdf-ffbe9c7b3306-p227-b004"></a>
<!-- pdf-source: page=227; block=4; confidence=0.99 -->
**Definition 8.51.** For a finite abelian group \(G\) and positive integer \(n\), \(L^2(G^n)\) is the complex inner-product space of functions \(f:G^n\to\mathbb C\), with \(\langle f,g\rangle=\mathbb E_{x\sim G^n}[f(x)\overline{g(x)}]\).

<a id="pdf-ffbe9c7b3306-p227-b005"></a>
<!-- pdf-source: page=227; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p227-b006"></a>
<!-- pdf-source: page=227; block=6; confidence=0.96 -->
**Definition 8.52.** A character of a finite group $G$ is a homomorphism $\chi:G\to\mathbb C^\times$, so $\chi(x+y)=\chi(x)\chi(y)$. Since $G$ is finite, all character values are roots of unity; in particular $|\chi(x)|=1$ for every $x\in G$.

<a id="pdf-ffbe9c7b3306-p228-b001"></a>
<!-- pdf-source: page=228; block=1; confidence=0.80 -->
The next fact records closure of characters under complex conjugation and pointwise multiplication.

<a id="pdf-ffbe9c7b3306-p228-b002"></a>
<!-- pdf-source: page=228; block=2; confidence=1.00 -->
**Fact 8.53.** If \(\chi\) and \(\phi\) are characters of \(G\), then so are \(\overline\chi\) and \(\phi\chi\).

<a id="pdf-ffbe9c7b3306-p228-b003"></a>
<!-- pdf-source: page=228; block=3; confidence=0.98 -->
**Proposition 8.54.** For a character $\chi$ of $G$, either $\chi\equiv1$ or $\mathbb E_{x\sim G}[\chi(x)]=0$.

<a id="pdf-ffbe9c7b3306-p228-b004"></a>
<!-- pdf-source: page=228; block=4; confidence=0.98 -->
**Proof.** If $\chi$ is nonconstant, choose $y$ with $\chi(y)\ne1$. Translation preserves the uniform distribution, so $\mathbb E_x\chi(x)=\mathbb E_x\chi(x+y)=\chi(y)\mathbb E_x\chi(x)$. Thus the expectation is zero.

<a id="pdf-ffbe9c7b3306-p228-b005"></a>
<!-- pdf-source: page=228; block=5; confidence=0.98 -->
**Proposition 8.55.** The characters of $G$ form an orthonormal set, so there are at most $\dim L^2(G)=|G|$ distinct characters.

<a id="pdf-ffbe9c7b3306-p228-b006"></a>
<!-- pdf-source: page=228; block=6; confidence=0.94 -->
**Proof.** Each character has norm one because its values have modulus one. For distinct characters $\phi,\chi$, their inner product is the expectation of the character $\phi\overline\chi=\phi/\chi$, which is nonconstant; Proposition 8.54 makes that expectation zero.

<a id="pdf-ffbe9c7b3306-p228-b007"></a>
<!-- pdf-source: page=228; block=7; confidence=0.98 -->
The text proceeds to construct exactly $|G|$ characters, which together give a Fourier basis of $L^2(G)$. It first treats cyclic groups.

<a id="pdf-ffbe9c7b3306-p228-b008"></a>
<!-- pdf-source: page=228; block=8; confidence=0.97 -->
**Definition 8.56.** For integer $m\ge2$, let $\omega=\exp(2\pi i/m)$. For $0\le j<m$, define $\chi_j:\mathbb Z_m\to\mathbb C$ by $\chi_j(x)=\omega^{jx}$. These are distinct characters.

<a id="pdf-ffbe9c7b3306-p228-b009"></a>
<!-- pdf-source: page=228; block=9; confidence=0.97 -->
The characters $\chi_0,\ldots,\chi_{m-1}$ form a Fourier basis for $L^2(\mathbb Z_m)$. Products of these coordinate characters give the basis on $\mathbb Z_m^n$.

<a id="pdf-ffbe9c7b3306-p228-b010"></a>
<!-- pdf-source: page=228; block=10; confidence=0.99 -->
**Definition 8.57.** For \(\alpha\in\mathbb Z_m^n\), define \(\chi_\alpha:\mathbb Z_m^n\to\mathbb C\) by \(\chi_\alpha(x)=\prod_{j=1}^n\chi_{\alpha_j}(x_j)\). These are all characters of \(\mathbb Z_m^n\) and form a Fourier basis.

<a id="pdf-ffbe9c7b3306-p228-b011"></a>
<!-- pdf-source: page=228; block=11; confidence=0.97 -->
By the structure theorem for finite abelian groups, every such group is a product of cyclic groups; taking products of the corresponding characters gives all characters and hence a Fourier basis. The exercise is cited for verifying this construction.

<a id="pdf-ffbe9c7b3306-p229-b001"></a>
<!-- pdf-source: page=229; block=1; confidence=0.99 -->
For characters indexed by \(\widehat{\mathbb Z_m^n}\), multiplication adds indices and inversion negates them modulo \(m\).

<a id="pdf-ffbe9c7b3306-p229-b002"></a>
<!-- pdf-source: page=229; block=2; confidence=0.94 -->
**Fact 8.58.** The characters \((\chi_\alpha)_{\alpha\in\widehat{\mathbb Z_m^n}}\) form a group under multiplication: \(\chi_\alpha\chi_\beta=\chi_{\alpha+\beta}\) and \(1/\chi_\alpha=\overline{\chi_\alpha}=\chi_{-\alpha}\).

<a id="pdf-ffbe9c7b3306-p229-b003"></a>
<!-- pdf-source: page=229; block=3; confidence=0.99 -->
**Definition 8.59.** For \(f,g\in L^2(G)\), their convolution is \((f*g)(x)=\mathbb E_{y\sim G}[f(y)g(x-y)]=\mathbb E_{y\sim G}[f(x-y)g(y)]\).

<a id="pdf-ffbe9c7b3306-p229-b004"></a>
<!-- pdf-source: page=229; block=4; confidence=0.98 -->
**Theorem 8.60.** For \(f,g\in L^2(G)\), \(\widehat{f*g}(\alpha)=\widehat f(\alpha)\widehat g(\alpha)\).

<a id="pdf-ffbe9c7b3306-p229-b005"></a>
<!-- pdf-source: page=229; block=5; confidence=0.91 -->
When \(m=p\) is prime, \(\mathbb Z_p^n\) is an \(n\)-dimensional vector space over \(\mathbb Z_p\); its subgroups are subspaces, and affine-subspace Fourier methods extend to this setting.

<a id="pdf-ffbe9c7b3306-p229-b006"></a>
<!-- pdf-source: page=229; block=6; confidence=1.00 -->
## 8.6. Highlight: Randomized decision tree complexity

<a id="pdf-ffbe9c7b3306-p230-b001"></a>
<!-- pdf-source: page=230; block=1; confidence=0.98 -->
A deterministic decision tree adaptively queries input bits and outputs the function value; its depth is its worst-case query count. For \(\mathrm{Maj}_3\), querying two bits and querying the third only if they differ has depth 3.

<a id="pdf-ffbe9c7b3306-p230-b002"></a>
<!-- pdf-source: page=230; block=2; confidence=0.98 -->
Randomly querying two distinct coordinates first gives worst-case expected cost \((1/3)2+(2/3)3=8/3\) for \(\mathrm{Maj}_3\).

<a id="pdf-ffbe9c7b3306-p230-b003"></a>
<!-- pdf-source: page=230; block=3; confidence=0.99 -->
**Definition 8.61.** For \(f:\{-1,1\}^n\to\mathbb R\), a zero-error randomized decision tree computing \(f\) is a probability distribution over deterministic decision trees computing \(f\). Its cost on input \(x\) is the expected number of queries; its cost is the maximum over inputs, and \(\mathrm{RDT}(f)\) is the minimum cost over such trees.

<a id="pdf-ffbe9c7b3306-p230-b004"></a>
<!-- pdf-source: page=230; block=4; confidence=0.98 -->
For uniform random input to \(\mathrm{Maj}_3\), a deterministic tree uses 2 queries with probability \(1/2\) and 3 with probability \(1/2\), giving expected cost \(5/2\).

<a id="pdf-ffbe9c7b3306-p230-b005"></a>
<!-- pdf-source: page=230; block=5; confidence=0.99 -->
**Definition 8.62.** For randomized decision tree \(\mathcal T\), define \(\delta_i(\mathcal T)=\Pr_{x,\mathcal T}[\mathcal T\text{ queries }x_i]\) and \(\Delta(\mathcal T)=\sum_{i=1}^n\delta_i(\mathcal T)=\mathbb E_{x,\mathcal T}[\#\text{ coordinates queried on }x]\). For \(f:\{-1,1\}^n\to\mathbb R\), \(\Delta(f)\) is the minimum of \(\Delta(\mathcal T)\) over trees computing \(f\).

<a id="pdf-ffbe9c7b3306-p230-b006"></a>
<!-- pdf-source: page=230; block=6; confidence=0.91 -->
The definitions extend to \(f\in L^2(\Omega,\pi^{\otimes n})\), with decision-tree query nodes branching over \(\Omega\); the corresponding quantities are denoted \(\delta_i^{(\pi)}(T)\), \(\Delta^{(\pi)}(T)\), and \(\Delta^{(\pi)}(f)\).

<a id="pdf-ffbe9c7b3306-p231-b001"></a>
<!-- pdf-source: page=231; block=1; confidence=0.96 -->
By definition, \(\Delta^{(\pi)}(f)\leq\mathrm{RDT}(f)\leq\mathrm{DT}(f)\).

<a id="pdf-ffbe9c7b3306-p231-b002"></a>
<!-- pdf-source: page=231; block=2; confidence=0.93 -->
**Remark 8.63.** In minimizing \(\Delta^{(\pi)}(f)\), deterministic trees suffice: some tree in the support of any randomized tree has cost no greater than its average in (8.10).

<a id="pdf-ffbe9c7b3306-p231-b003"></a>
<!-- pdf-source: page=231; block=3; confidence=0.90 -->
**Example 8.64.** For \(\mathrm{Maj}_3\), \(\mathrm{RDT}(\mathrm{Maj}_3)=8/3\) and \(\Delta(\mathrm{Maj}_3)=5/2\). For recursive majority on \(n=3^d\) inputs, \(\mathrm{DT}(\mathrm{Maj}_3^{\otimes d})=3^d=n\), while \(\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d})\leq(8/3)^d=n^{\log_3(8/3)}\approx n^{0.89}\) and \(\Delta(\mathrm{Maj}_3^{\otimes d})\leq(5/2)^d=n^{\log_3(5/2)}\approx n^{0.83}\). The bounds are not known to be asymptotically sharp, particularly for \(\mathrm{RDT}\).

<a id="pdf-ffbe9c7b3306-p231-b004"></a>
<!-- pdf-source: page=231; block=4; confidence=0.84 -->
**Example 8.65.** For logical OR, \(\Delta^{(p)}(\mathrm{OR}_n)=1-(1-p)^n\); this is roughly 2 at \(p=1/2\) and asymptotic to \(n/(2\ln 2)\) at the critical probability \(p_c\).

<a id="pdf-ffbe9c7b3306-p231-b005"></a>
<!-- pdf-source: page=231; block=5; confidence=0.91 -->
For transitive-symmetric \(f\), a randomized tree can be symmetrized so every coordinate has equal query probability, \(\delta_i(T)=\Delta(f)/n\); some such functions can therefore be evaluated while querying only an \(n^{-\Theta(1)}\) fraction of bits in expectation.

<a id="pdf-ffbe9c7b3306-p231-b006"></a>
<!-- pdf-source: page=231; block=6; confidence=0.91 -->
**Yao’s Conjecture.** If \(f:\{−1,1\}^n\to\{−1,1\}\) is a nonconstant monotone graph property on \(v\) vertices, with \(n=\binom v2\), then \(\mathrm{RDT}(f)\geq\Omega(n)\).

<a id="pdf-ffbe9c7b3306-p231-b007"></a>
<!-- pdf-source: page=231; block=7; confidence=0.93 -->
The section introduces an O’Donnell–Saks–Schramm–Servedio lower bound that applies to transitive-symmetric functions and also lower-bounds \(\Delta^{(p_c)}(f)\).

<a id="pdf-ffbe9c7b3306-p232-b001"></a>
<!-- pdf-source: page=232; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p232-b002"></a>
<!-- pdf-source: page=232; block=2; confidence=0.98 -->
**Theorem 8.66.** If $f:\{-1,1\}^n\to\{-1,1\}$ is nonconstant, monotone, and transitive-symmetric, with critical probability $p_c$, then $\Delta^{(p_c)}(f)\ge (n/\sigma_c)^{2/3}$.

<a id="pdf-ffbe9c7b3306-p232-b003"></a>
<!-- pdf-source: page=232; block=3; confidence=0.97 -->
The bound is strongest up to constants when $p_c=\Theta(1/n)$ or $1-p_c=\Theta(1/n)$, and can be tight up to a logarithmic factor at $p_c=1/2$.

<a id="pdf-ffbe9c7b3306-p232-b004"></a>
<!-- pdf-source: page=232; block=4; confidence=0.98 -->
**Theorem 8.67 [BSW05].** There is an infinite family of monotone transitive-symmetric Boolean functions $f_n$ with critical probability $p_c=1/2$ and $\Delta(f_n)=O(n^{2/3}\log n)$.

<a id="pdf-ffbe9c7b3306-p232-b005"></a>
<!-- pdf-source: page=232; block=5; confidence=0.97 -->
**OS Inequality.** If \(f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})\), then \(\sum_{i=1}^n\widehat f(i)\le\|f\|_2\sqrt{\Delta^{(p)}(f)}\). In particular, for monotone Boolean \(f\), \(I[f]\le\sigma\sqrt{\Delta^{(p)}(f)}\).

<a id="pdf-ffbe9c7b3306-p232-b006"></a>
<!-- pdf-source: page=232; block=6; confidence=0.99 -->
**OSSS Inequality.** If $f\in L^2(\Omega^n,\pi^{\otimes n})$ has range $\{-1,1\}$ and $T$ is a randomized decision tree computing $f$, then $\operatorname{Var}[f]\le\sum_{i=1}^n\delta_i^{(\pi)}(T)\,\operatorname{Inf}_i[f]$.

<a id="pdf-ffbe9c7b3306-p232-b007"></a>
<!-- pdf-source: page=232; block=7; confidence=0.96 -->
These inequalities relate first-level Fourier information and variance to decision-tree complexity, with OSSS discounting coordinates according to their reveal probabilities.

<a id="pdf-ffbe9c7b3306-p232-b008"></a>
<!-- pdf-source: page=232; block=8; confidence=0.97 -->
**Proof of Theorem 8.66.** Regard $f$ as an element of $L^2(\{-1,1\}^n,\pi_{p_c}^{\otimes n})$ and take a randomized tree $T$ attaining $\Delta^{(p_c)}(f)$. Criticality gives $\operatorname{Var}[f]=1$, and transitive symmetry gives $\operatorname{Inf}_i[f]=I[f]/n$ for each $i$. Applying OSSS yields $1\le \sum_i\delta_i^{(p_c)}(T)I[f]/n$, hence $n\le\Delta^{(p_c)}(f)I[f]\le\sigma_c\Delta^{(p_c)}(f)^{3/2}$ by OS. Rearranging proves the bound.

<a id="pdf-ffbe9c7b3306-p233-b001"></a>
<!-- pdf-source: page=233; block=1; confidence=1.00 -->
## 8.6. Highlight: Randomized decision tree complexity

<a id="pdf-ffbe9c7b3306-p233-b002"></a>
<!-- pdf-source: page=233; block=2; confidence=0.92 -->
The proof now establishes OSSS, using a covariance decomposition for restrictions to a queried coordinate.

<a id="pdf-ffbe9c7b3306-p233-b003"></a>
<!-- pdf-source: page=233; block=3; confidence=0.99 -->
**Lemma 8.69.** For $f,g\in L^2(\Omega^n,\pi^{\otimes n})$ and coordinate $j$, let $f|_\omega$ and $g|_{\omega'}$ denote restrictions fixing coordinate $j$ to the indicated values. Then $\operatorname{Cov}[f,g]=\mathbb E_{\omega,\omega'\sim\pi\text{ independent}}[\operatorname{Cov}(f|_\omega,g|_{\omega'})]+\langle L_jf,L_jg\rangle$.

<a id="pdf-ffbe9c7b3306-p233-b004"></a>
<!-- pdf-source: page=233; block=4; confidence=0.97 -->
**Proof.** Adding constants does not affect covariance or Laplacians, so assume $\mathbb E f=\mathbb E g=0$. The expected restricted covariance equals $\langle E_jf,E_jg\rangle$. The claim then follows from $\langle f,g\rangle=\langle E_jf,E_jg\rangle+\langle L_jf,L_jg\rangle$.

<a id="pdf-ffbe9c7b3306-p233-b005"></a>
<!-- pdf-source: page=233; block=5; confidence=0.96 -->
**Proof of the OSSS Inequality.** Prove the stronger assertion that for Boolean-valued $f,g\in L^2(\Omega^n,\pi^{\otimes n})$ computed by the same randomized tree $T$, $\operatorname{Cov}[f,g]\le\sum_{i=1}^n\delta_i^{(\pi)}(T)\operatorname{Inf}_i[g]$ (8.11). Taking $g=f$ gives OSSS. By linearity in the reveal probabilities, it suffices to consider a deterministic tree. Induct on its structure: a depth-zero tree computes a constant, so covariance vanishes. Otherwise, if the root queries coordinate $j$, let $T_\omega$ be the subtree following outcome $\omega$; apply Lemma 8.69 and induction to the restricted functions.

<a id="pdf-ffbe9c7b3306-p234-b001"></a>
<!-- pdf-source: page=234; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p234-b002"></a>
<!-- pdf-source: page=234; block=2; confidence=0.97 -->
**Definition 8.70.** For a finite probability space $(\Omega,\pi)$ and deterministic decision tree $T$, the associated process samples each queried coordinate independently from $\pi$ while traversing the tree. If $J\subseteq[n]$ is the set queried, it then samples the unqueried coordinates from the product distribution, producing $x=(x_J,x_{\bar J})$. The resulting full string has distribution $\pi^{\otimes n}$.

<a id="pdf-ffbe9c7b3306-p234-b003"></a>
<!-- pdf-source: page=234; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p235-b001"></a>
<!-- pdf-source: page=235; block=1; confidence=0.92 -->
By Cauchy–Schwarz, \(\mathbb E_{J,x_J}[f(x_J)^2]\leq \mathbb E_{J,x_J}[(\sum_{i=1}^n 1_{\{i\in J\}}\phi(x_i))^2]\). The left side is \(\|f\|_2^2\), since the decision tree computes \(f\). Expanding the right side gives diagonal terms \(\sum_i\mathbb E[1_{\{i\in J\}}\phi(x_i)^2]=\sum_i\Pr[i\in J]=\Delta^{(p)}(f)\), using \(\mathbb E[\phi(x_i)^2\mid i\in J]=1\). For \(i\ne i'\), the cross term \(\mathbb E[1_{\{i,i'\in J\}}\phi(x_i)\phi(x_{i'})]\) vanishes: condition on both being queried and on which is queried later; its input still has law \(\pi_p\), so its \(\phi\)-mean is zero. Thus the squared sum has expectation \(\Delta^{(p)}(f)\), completing the proof.

<a id="pdf-ffbe9c7b3306-p235-b002"></a>
<!-- pdf-source: page=235; block=2; confidence=0.99 -->
## 8.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p235-b003"></a>
<!-- pdf-source: page=235; block=3; confidence=0.98 -->
Exercises ask for extensions of Sections 8.1–8.2 to finite product spaces; verification of the inner product in Definition 8.1, the formula in Definition 8.14, the Fourier basis in Example 8.10, and the expansion in Example 8.15; and completion of Proposition 8.16’s proof.

<a id="pdf-ffbe9c7b3306-p236-b001"></a>
<!-- pdf-source: page=236; block=1; confidence=0.84 -->
Exercises 8.7–8.16 concern properties of coordinate expectation and noise operators; decompositions using \(E_j,L_j\); influence bounds; extensions of product-space noise formulas to negative \(\rho\); continuity of influence at \(\delta=0\) and an extension to \(\delta=1\); conditions in Theorem 8.35; and the identity \((f_{=S})_{\subseteq T}=f_{=S}\) for \(S\subseteq T\), and zero otherwise.

<a id="pdf-ffbe9c7b3306-p236-b002"></a>
<!-- pdf-source: page=236; block=2; confidence=0.99 -->
Show that \(E_I\) is linear, idempotent, and self-adjoint on \(L^2(\Omega^n,\pi^{\otimes n})\); deduce that \(T_\rho\) is self-adjoint.

<a id="pdf-ffbe9c7b3306-p236-b003"></a>
<!-- pdf-source: page=236; block=3; confidence=0.99 -->
For \(f,g\in L^2(\Omega^n,\pi^{\otimes n})\) and \(j\in[n]\), prove \(f=E_jf+L_jf\) and \(\langle f,g\rangle=\langle E_jf,E_jg\rangle+\langle L_jf,L_jg\rangle\).

<a id="pdf-ffbe9c7b3306-p236-b004"></a>
<!-- pdf-source: page=236; block=4; confidence=0.99 -->
Prove Proposition 8.24, using Exercise 1.17 as a hint.

<a id="pdf-ffbe9c7b3306-p236-b005"></a>
<!-- pdf-source: page=236; block=5; confidence=0.91 -->
For \(f\) valued in \(\{-1,1\}\), Proposition 8.24 gives \(2=\mathrm{Inf}_i[f]/\|L_if\|_1=\|L_if\|_2\). Show (a) \(\|L_if\|_p^p\leq2^p\mathrm{Inf}_i[f]\) for \(p\geq1\); and (b) for \(1\leq p\leq2\), improve this to \(\|L_if\|_p^p\leq\mathrm{Inf}_i[f]\), using Hölder to bound the \(p\)-norm by the 1- and 2-norms.

<a id="pdf-ffbe9c7b3306-p236-b006"></a>
<!-- pdf-source: page=236; block=6; confidence=0.99 -->
Generalize Exercise 2.35 to \(L^2(\Omega^n,\pi^{\otimes n})\); restrict statements there concerning \(\rho\in[-1,1]\) to \(\rho\in[0,1]\).

<a id="pdf-ffbe9c7b3306-p236-b007"></a>
<!-- pdf-source: page=236; block=7; confidence=0.94 -->
For uniform \(\pi\) on an \(m\)-element set \(\Omega\), (a) derive \(\Pr[y_i=\omega]\) for \(y\sim N_\rho(x)\), distinguishing \(x_i=\omega\) from \(x_i\ne\omega\); (b) verify this defines probabilities for \(-1/(m-1)\leq\rho<0\), extending \(N_\rho\); (c) prove symmetry of \((x,y)\) when \(x\sim\pi^{\otimes n}\); (d) at \(\rho=-1/(m-1)\), show each \(y_i\) is uniform on \(\Omega\setminus\{x_i\}\); (e) extend Proposition 8.28’s formula for \(T_\rho\) to the negative range by polynomiality in \(\rho\).

<a id="pdf-ffbe9c7b3306-p236-b008"></a>
<!-- pdf-source: page=236; block=8; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p236-b009"></a>
<!-- pdf-source: page=236; block=9; confidence=0.97 -->
Prove condition 5 of Theorem 8.35 explicitly; prove condition 6 directly from uniqueness; and show directly from Theorem 8.35 that \((f_{=S})_{\subseteq T}=f_{=S}\) when \(S\subseteq T\), and equals zero otherwise.

<a id="pdf-ffbe9c7b3306-p237-b001"></a>
<!-- pdf-source: page=237; block=1; confidence=0.99 -->
## 8.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p237-b002"></a>
<!-- pdf-source: page=237; block=2; confidence=0.93 -->
For \(x\sim\pi^{\otimes n}\), (a) show \((f_{\subseteq[t]}(x))_{t=0}^n\) is a martingale with respect to its revealed-coordinate filtration, so \(\mathbb E[f_{\subseteq[t]}\mid f_{\subseteq[0]},\ldots,f_{\subseteq[t-1]}]=f_{\subseteq[t-1]}\); (b) for \(d_tf=f_{\subseteq[t]}-f_{\subseteq[t-1]}=\sum_{S\subseteq[n],\,\max(S)=t} f_{=S}\), show its conditional expectation given earlier reveals is zero. These are the Doob martingale and its differences.

<a id="pdf-ffbe9c7b3306-p237-b003"></a>
<!-- pdf-source: page=237; block=3; confidence=0.99 -->
For \(f,g\in L^2(\Omega^n,\pi^{\otimes n})\), prove \(\langle f,g\rangle=\sum_S\langle f^{=S},g^{=S}\rangle\), \(\operatorname{Inf}_i[f]=\sum_{S\ni i}\|f^{=S}\|_2^2\), \(I[f]=\sum_{k=0}^n kW^k[f]\), \(T_\rho(f^{=S})=(T_\rho f)^{=S}=\rho^{|S|}f^{=S}\), and \(\operatorname{Stab}_\rho[f]=\sum_{k=0}^n\rho^kW^k[f]\).

<a id="pdf-ffbe9c7b3306-p237-b004"></a>
<!-- pdf-source: page=237; block=4; confidence=0.99 -->
For \(f\in L^2(\Omega^n,\pi^{\otimes n})\) and \(S\subseteq[n]\), prove \(\|f_{=S}\|_\infty\leq2^{|S|}\|f\|_\infty\).

<a id="pdf-ffbe9c7b3306-p237-b005"></a>
<!-- pdf-source: page=237; block=5; confidence=0.99 -->
Check Proposition 8.36 explicitly for the functions in Examples 8.15 and 8.37.

<a id="pdf-ffbe9c7b3306-p237-b006"></a>
<!-- pdf-source: page=237; block=6; confidence=0.90 -->
If \(i\in S\subseteq[n]\), restrict \(f_{=S}\) at coordinate \(i\) to value \(\omega_i\), obtaining \(g=(f_{=S})|_{\omega_i}\); show \(g=g_{=S\setminus\{i\}}\). In particular, \(\mathbb E[g]=0\) when \(|S|\geq2\).

<a id="pdf-ffbe9c7b3306-p237-b007"></a>
<!-- pdf-source: page=237; block=7; confidence=0.99 -->
For symmetric \(f\), prove that \(\frac1{|S|}\mathrm{Var}[f_{\subseteq S}]\leq\frac1{|T|}\mathrm{Var}[f_{\subseteq T}]\) whenever \(1\leq|S|\leq|T|\leq n\).

<a id="pdf-ffbe9c7b3306-p237-b008"></a>
<!-- pdf-source: page=237; block=8; confidence=0.97 -->
Prove the sharp-threshold claim for majority from Example 8.49 using a Chernoff bound; this is the Condorcet Jury Theorem.

<a id="pdf-ffbe9c7b3306-p237-b009"></a>
<!-- pdf-source: page=237; block=9; confidence=0.99 -->
For \(p_1,\ldots,p_n\in(0,1)\), let \(\pi=\pi_{p_1}\otimes\cdots\otimes\pi_{p_n}\), \(\mu_i=1-2p_i\), and \(\sigma_i=2\sqrt{p_i(1-p_i)}\). Generalize Proposition 8.45 to \(L^2(\{-1,1\}^n,\pi)\).

<a id="pdf-ffbe9c7b3306-p238-b001"></a>
<!-- pdf-source: page=238; block=1; confidence=0.98 -->
For \(S=\{i_1,\ldots,i_k\}\), define \(D_{\phi_S}=D_{\phi_{i_1}}\cdots D_{\phi_{i_k}}\) and \(D_{x_S}=D_{x_{i_1}}\cdots D_{x_{i_k}}\). Show \(D_{\phi_S}=\prod_{i\in S}\sigma_i\,D_{x_S}\).

<a id="pdf-ffbe9c7b3306-p238-b002"></a>
<!-- pdf-source: page=238; block=2; confidence=0.90 -->
For \(S=\{i_1,\ldots,i_k\}\subseteq[n]\), establish \(D_S^\phi=\prod_{i\in S}\sigma_i\,D_S^x\), with the derivatives composed over the coordinates in \(S\).

<a id="pdf-ffbe9c7b3306-p238-b003"></a>
<!-- pdf-source: page=238; block=3; confidence=0.82 -->
Viewing \(f\) under the product measure as \(f(\mu_1,\ldots,\mu_n)\), show that its biased Fourier coefficient satisfies \(\widehat f^{(p)}(S)=\bigl(\prod_{i\in S}\sigma_i\bigr)D_S^x f(\mu_1,\ldots,\mu_n)\).

<a id="pdf-ffbe9c7b3306-p238-b004"></a>
<!-- pdf-source: page=238; block=4; confidence=0.91 -->
Show \(\|\widehat{f^{(\mu)}}\|_\infty\le\prod_{i\in S}\sigma_i\,\|f\|_\infty\), for the fixed set \(S\) in Exercise 8.25.

<a id="pdf-ffbe9c7b3306-p238-b005"></a>
<!-- pdf-source: page=238; block=5; confidence=0.98 -->
Extend pivotality and width-based influence bounds to the product-distribution setting.

<a id="pdf-ffbe9c7b3306-p238-b006"></a>
<!-- pdf-source: page=238; block=6; confidence=0.94 -->
For \(f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})\) with range \(\{-1,1\}\), show for each \(i\in[n]\), \(b\in\{-1,1\}\) that \(\Pr_{x\sim\pi_p^{\otimes n}}[i\text{ is }b\text{-pivotal for }f\text{ on }x]=\pi_p(b)\,\operatorname{Inf}_i[f]\).

<a id="pdf-ffbe9c7b3306-p238-b007"></a>
<!-- pdf-source: page=238; block=7; confidence=0.88 -->
If \(f:\{-1,1\}^n\to\{-1,1\}\) has DNF width at most \(w\), show \(I[f^{(p)}]\leq4qw\leq4w\); for CNF width at most \(w\), show \(I[f^{(p)}]\leq4pw\leq4w\).

<a id="pdf-ffbe9c7b3306-p238-b008"></a>
<!-- pdf-source: page=238; block=8; confidence=0.97 -->
For any \(\alpha\in(0,1)\) and nonconstant monotone Boolean function \(f\), show some \(p\in(0,1)\) satisfies \(\Pr_{x\sim\pi_p}[f(x)=\mathrm{True}]=\alpha\), using continuity and the intermediate value theorem.

<a id="pdf-ffbe9c7b3306-p238-b009"></a>
<!-- pdf-source: page=238; block=9; confidence=0.92 -->
Fix a small \(\varepsilon\in(0,1/2)\) and a nonconstant monotone Boolean function \(f\). Let \(p_0,p_c,p_1\) be the probabilities at which its true-output probability is respectively \(\varepsilon,1/2,1-\varepsilon\). Define \(\sigma_c^2=4p_c(1-p_c)\), threshold interval \([p_0,p_1]\), and width \(\delta=p_1-p_0\). For a sequence \((f_n)\), call the threshold sharp if \(\delta(n)/\sigma_c^2(n)\to0\), coarse otherwise; when \(p_c(n)\leq1/2\), sharpness is equivalently \(\delta(n)/p_c(n)\to0\).

<a id="pdf-ffbe9c7b3306-p238-b010"></a>
<!-- pdf-source: page=238; block=10; confidence=0.88 -->
Show that a coarse-threshold family admits a constant \(C<\infty\), an infinite subsequence \(n_1<n_2<\cdots\), and probabilities \(p(n_i)\) for which \(\varepsilon<\Pr_{\pi_{p(n_i)}}[f_{n_i}=\mathrm{True}]<1-\varepsilon\) and \(I[f_{n_i}^{(p(n_i))}]\leq C\) for every \(i\). Hint: Margulis–Russo formula and the mean value theorem.

<a id="pdf-ffbe9c7b3306-p238-b011"></a>
<!-- pdf-source: page=238; block=11; confidence=0.97 -->
A weak threshold estimate for a monotone Boolean function.

<a id="pdf-ffbe9c7b3306-p238-b012"></a>
<!-- pdf-source: page=238; block=12; confidence=0.90 -->
For nonconstant monotone \(f:\{-1,1\}^n\to\{-1,1\}\), set \(F(p)=\Pr_{\pi_p}[f(x)=-1]\), which is strictly increasing, and let \(p_c\) satisfy \(F(p_c)=1/2\). Assume \(p_c\leq1/2\), by replacing \(f\) by its dual if needed. The goal is to bound \(F(p)\) near and far below/above \(p_c\).

<a id="pdf-ffbe9c7b3306-p238-b013"></a>
<!-- pdf-source: page=238; block=13; confidence=0.96 -->
Using Margulis–Russo and Poincaré, prove \(F'(p)\geq F(p)(1-F(p))/(p(1-p))\) for \(0<p<1\).

<a id="pdf-ffbe9c7b3306-p238-b014"></a>
<!-- pdf-source: page=238; block=14; confidence=0.96 -->
For \(p\leq p_c\), deduce \(F'(p)\geq F(p)/(2p)\), hence \(\frac{d}{dp}\ln F(p)\geq1/(2p)\).

<a id="pdf-ffbe9c7b3306-p238-b015"></a>
<!-- pdf-source: page=238; block=15; confidence=0.85 -->
For \(0\leq p_0\leq p_c\), derive \(F(p_0)\leq\tfrac12\sqrt{p_0/p_c}\); in particular, \(F(p_0)\leq\varepsilon\) if \(p_0\leq(2\varepsilon)^2p_c\).

<a id="pdf-ffbe9c7b3306-p238-b016"></a>
<!-- pdf-source: page=238; block=16; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p239-b001"></a>
<!-- pdf-source: page=239; block=1; confidence=0.79 -->
If \(p_1=(2\varepsilon)^{-2}p_c\leq1/2\), show \(F(p_1)\geq1-\varepsilon\). If this condition fails, show at least \(F(1/2)\geq1-\sqrt{p_c/2}\). Hint: apply a logarithmic estimate to \(1-F(p)\).

<a id="pdf-ffbe9c7b3306-p239-b002"></a>
<!-- pdf-source: page=239; block=2; confidence=0.75 -->
Show \(F(1-\delta)\geq1-\sqrt{\delta/2}\), including when \(p_c=1/2\).

<a id="pdf-ffbe9c7b3306-p239-b003"></a>
<!-- pdf-source: page=239; block=3; confidence=0.98 -->
Study a monotone function formed by nesting majority functions.

<a id="pdf-ffbe9c7b3306-p239-b004"></a>
<!-- pdf-source: page=239; block=4; confidence=0.97 -->
For odd \(n\geq3\), define \(f_n(x)=\operatorname{Maj}_3(x_1,x_2,\operatorname{Maj}_{n-2}(x_3,\ldots,x_n))\). Show it is monotone and has critical probability \(p_c=1/2\).

<a id="pdf-ffbe9c7b3306-p239-b005"></a>
<!-- pdf-source: page=239; block=5; confidence=0.97 -->
Sketch the true-output probability \(\Pr_{\pi_p}[f_n(x)=\mathrm{True}]\) as a function of \(p\) for large \(n\).

<a id="pdf-ffbe9c7b3306-p239-b006"></a>
<!-- pdf-source: page=239; block=6; confidence=0.98 -->
Show that \(I[f_n]=\Theta(\sqrt n)\).

<a id="pdf-ffbe9c7b3306-p239-b007"></a>
<!-- pdf-source: page=239; block=7; confidence=0.95 -->
Assuming \(\varepsilon<1/4\), show \((f_n)\) has a coarse threshold under Exercise 8.28's definition.

<a id="pdf-ffbe9c7b3306-p239-b008"></a>
<!-- pdf-source: page=239; block=8; confidence=0.97 -->
Compare three equivalent ways of sampling a uniformly weighted Boolean string.

<a id="pdf-ffbe9c7b3306-p239-b009"></a>
<!-- pdf-source: page=239; block=9; confidence=0.97 -->
For strings in \(\{0,1\}^n\), prove these distributions agree: (1) choose a weight \(k\) uniformly from \(\{0,\ldots,n\}\), then choose uniformly among strings of weight \(k\); (2) choose a uniform permutation path from \(0^n\) to \(1^n\), then choose one of its \(n+1\) strings uniformly; (3) choose \(p\) uniformly from \([0,1]\), then sample from \(\pi_p^{\otimes n}\).

<a id="pdf-ffbe9c7b3306-p240-b001"></a>
<!-- pdf-source: page=240; block=1; confidence=0.96 -->
Let \(\nu_N\) be the distribution on \(\{0,1\}^N\) induced by part (a), for any finite coordinate set \(N\). For nonempty \(J\subseteq[n]\), show the restriction of \(x\sim\nu_n\) to coordinates \(J\) has law \(\nu_J\).

<a id="pdf-ffbe9c7b3306-p240-b002"></a>
<!-- pdf-source: page=240; block=2; confidence=0.95 -->
For \(f:\{0,1\}^n\to\mathbb R\), define the Shapley value \(\operatorname{Shap}_i[f]=\mathbb E_{x\sim\nu_n}[f(x^{(i\mapsto1)})-f(x^{(i\mapsto0)})]\).

<a id="pdf-ffbe9c7b3306-p240-b003"></a>
<!-- pdf-source: page=240; block=3; confidence=0.98 -->
Show \(\sum_{i=1}^n\operatorname{Shap}_i[f]=f(1,\ldots,1)-f(0,\ldots,0)\).

<a id="pdf-ffbe9c7b3306-p240-b004"></a>
<!-- pdf-source: page=240; block=4; confidence=0.90 -->
For monotone \(f:\{0,1\}^n\to\{0,1\}\), prove \(\operatorname{Shap}_i[f]=4\int_0^1\operatorname{Inf}_i[f^{(p)}]\,dp\).

<a id="pdf-ffbe9c7b3306-p240-b005"></a>
<!-- pdf-source: page=240; block=5; confidence=0.98 -->
Extend the definitions and results of Sections 8.1–8.2 to complex inner product valued functions, and verify the Fourier identities from Proposition 8.16.

<a id="pdf-ffbe9c7b3306-p240-b006"></a>
<!-- pdf-source: page=240; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p240-b007"></a>
<!-- pdf-source: page=240; block=7; confidence=0.98 -->
Extend the framework to real inner product valued functions and to finite-set-valued functions.

<a id="pdf-ffbe9c7b3306-p240-b008"></a>
<!-- pdf-source: page=240; block=8; confidence=0.96 -->
For \(f:\Omega^n\to V\), where \(V\) is a real inner product space, define Fourier coefficients in \(V\) and \(\langle f,g\rangle=\mathbb E_{x\sim\pi^{\otimes n}}\langle f(x),g(x)\rangle_V\). Generalize Sections 8.1–8.2 and verify Proposition 8.16, including Plancherel: \(\langle f,g\rangle=\sum_\alpha\langle\widehat f(\alpha),\widehat g(\alpha)\rangle_V\).

<a id="pdf-ffbe9c7b3306-p240-b009"></a>
<!-- pdf-source: page=240; block=9; confidence=0.93 -->
Identify probability distributions on a finite set \(\Sigma\), \(|\Sigma|=m\), with the simplex \(\{\mu\in\mathbb R^m:\sum_i\mu_i=1,\ \mu_i\geq0\}\), and its vertices with elements of \(\Sigma\). Treat \(f:\Omega^n\to\Sigma\) as an \(\mathbb R^m\)-valued function; show \(\operatorname{Stab}_\rho[f]=\Pr_{x\sim\pi^{\otimes n},\,y\sim N_\rho(x)}[f(x)=f(y)]\).

<a id="pdf-ffbe9c7b3306-p241-b001"></a>
<!-- pdf-source: page=241; block=1; confidence=1.00 -->
## 8.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p241-b002"></a>
<!-- pdf-source: page=241; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p241-b003"></a>
<!-- pdf-source: page=241; block=3; confidence=0.90 -->
**Exercise 8.34.** A linear threshold function on \(\Omega^n\) has the form \(f(x)=\operatorname{sgn}(\ell(x))\), where \(\ell:\Omega^n\to\mathbb R\) has degree at most one (Definition 8.32). (a) For independently sampled \(\omega^{(+1)},\omega^{(-1)}\sim\pi^{\otimes n}\), define \(\omega(x)=(\omega_i^{(x_i)})_{i=1}^n\). Show that if \((x,y)\) is a \(\rho\)-correlated pair of uniform sign strings, then \((\omega(x),\omega(y))\) is \(\rho\)-correlated under \(\pi^{\otimes n}\). (b) For such \(f\), show \(g_{\omega^{(+1)},\omega^{(-1)}}(x)=f(\omega(x))\) is a usual linear threshold function on the Boolean cube. (c) Deduce that Peres’s Theorem (Chapter 5.5) applies to these functions with the same bounds.

<a id="pdf-ffbe9c7b3306-p241-b004"></a>
<!-- pdf-source: page=241; block=4; confidence=0.93 -->
**Exercise 8.35.** For a finite abelian group \(G\cong\prod_{j=1}^n\mathbb Z_{m_j}\), with each \(m_j\) a prime power, define \(\chi_\alpha(x)=\prod_{j=1}^n\exp(2\pi i\alpha_jx_j/m_j)\). (a) Show these are distinct characters and form a Fourier basis of \(L^2(G)\). (b) Show they form a group under multiplication isomorphic to \(G\); this dual group is denoted \(\widehat G\), with characters identified by indices \(\alpha\).

<a id="pdf-ffbe9c7b3306-p241-b005"></a>
<!-- pdf-source: page=241; block=5; confidence=0.94 -->
**Exercise 8.36.** Verify that convolution on \(L^2(G)\) is associative and commutative and that \(\widehat{f*g}(\alpha)=\widehat f(\alpha)\widehat g(\alpha)\) for every \(\alpha\in\widehat G\).

<a id="pdf-ffbe9c7b3306-p241-b006"></a>
<!-- pdf-source: page=241; block=6; confidence=0.88 -->
**Exercise 8.37.** (a) If \(f\in L^2(\Omega^n,\pi^{\otimes n})\) is transitive-symmetric and \(T\) is a randomized decision tree computing it, show that averaging over \(\operatorname{Aut}(f)\) gives a tree \(T'\) with \(\Delta^{(\pi)}(T')=\Delta^{(\pi)}(T)\) and equal revealment probabilities \(\delta_i^{(\pi)}(T')\) for all coordinates. (b) Define \(\delta^{(\pi)}(T)=\max_i\delta_i^{(\pi)}(T)\) and \(\delta^{(\pi)}(f)=\min_{T\text{ computes }f}\delta^{(\pi)}(T)\). This is the revealment of \(f\); show for transitive-symmetric \(f\) that \(\delta^{(\pi)}(f)=\Delta^{(\pi)}(f)/n\).

<a id="pdf-ffbe9c7b3306-p242-b001"></a>
<!-- pdf-source: page=242; block=1; confidence=1.00 -->
## 8. Generalized domains

<a id="pdf-ffbe9c7b3306-p242-b002"></a>
<!-- pdf-source: page=242; block=2; confidence=0.91 -->
**Exercise 8.37(b), continuation.** The revealment identity is \(\delta^{(\pi)}(f)=\frac1n\Delta^{(\pi)}(f)\) for transitive-symmetric functions.

<a id="pdf-ffbe9c7b3306-p242-b003"></a>
<!-- pdf-source: page=242; block=3; confidence=0.94 -->
**Exercise 8.38.** (a) Show \(\operatorname{DT}(\operatorname{Maj}_3^{\otimes d})=3d\), \(\operatorname{RDT}(\operatorname{Maj}_3^{\otimes d})\le(8/3)d\), and \(\Delta(\operatorname{Maj}_3^{\otimes d})\le(5/2)d\). (b) Improve the bound for \(\operatorname{RDT}(\operatorname{Maj}_3^{\otimes2})\) to strictly less than \((8/3)^2\), and seek the best upper bound.

<a id="pdf-ffbe9c7b3306-p242-b004"></a>
<!-- pdf-source: page=242; block=4; confidence=0.89 -->
**Exercise 8.39.** (a) For every deterministic tree computing \(\mathrm{OR}_n\), show its expected cost under the product-\(p\) distribution is \(\Delta^{(p)}(T)=\sum_{k=1}^{n-1}k(1-p)^{k-1}p+n(1-p)^{n-1}=\frac{1-(1-p)^n}{p}\), and hence the same formula holds for optimal cost \(\Delta^{(p)}(\mathrm{OR}_n)\). (b) Show \(\Delta^{(p_c)}(\mathrm{OR}_n)\sim n/(2\ln 2)\) as \(n\to\infty\), where \(p_c\) is the critical probability for \(\mathrm{OR}_n\).

<a id="pdf-ffbe9c7b3306-p242-b005"></a>
<!-- pdf-source: page=242; block=5; confidence=0.98 -->
**Exercise 8.40(g).** Deduce \(\operatorname{RDT}(\mathrm{NAND}^{\otimes d})\le ((1+\sqrt{33})/4)^d\approx n^{0.754}\), where \(n=2^d\).

<a id="pdf-ffbe9c7b3306-p242-b006"></a>
<!-- pdf-source: page=242; block=6; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p242-b007"></a>
<!-- pdf-source: page=242; block=7; confidence=0.95 -->
**Exercise 8.42.** Verify by induction on tree structure that the decision-tree process of Definition 8.70 generates strings with distribution \(\pi^{\otimes n}\).

<a id="pdf-ffbe9c7b3306-p243-b001"></a>
<!-- pdf-source: page=243; block=1; confidence=1.00 -->
## 8.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p243-b002"></a>
<!-- pdf-source: page=243; block=2; confidence=0.94 -->
**Exercise 8.43.** For a deterministic decision tree of size \(s\), prove \(\Delta(T)\le\log s\), using the entropy of a random root-to-leaf path sampled by the decision-tree process.

<a id="pdf-ffbe9c7b3306-p243-b003"></a>
<!-- pdf-source: page=243; block=3; confidence=0.94 -->
**Exercise 8.44.** Let \(f\in L^2(\Omega^n,\pi^{\otimes n})\) be nonconstant with range \(\{-1,1\}\). (a) Show \(\operatorname{MaxInf}[f]\ge\operatorname{Var}[f]/\Delta^{(\pi)}(f)\). (b) For \(\Omega=\{-1,1\}\), show \(\operatorname{MaxInf}[f]\ge\operatorname{Var}[f]/\deg(f)^3\), using the cited Midrijanis result. (c) Show total influence \(I[f]\ge\operatorname{Var}[f]/\delta^{(\pi)}(f)\), with revealment as in Exercise 8.37(b).

<a id="pdf-ffbe9c7b3306-p243-b004"></a>
<!-- pdf-source: page=243; block=4; confidence=0.83 -->
**Exercise 8.45.** Let \(f\) be Boolean-valued on \(\Omega^n\). (a) For any randomized decision tree \(T\) computing \(f\), show \(\operatorname{Inf}_i[f]\le\delta_i^{(\pi)}(T)\). (b) If \(f\) is transitive-symmetric, show \(\Delta^{(\pi)}(f)\ge\operatorname{Var}[f]\,n/\log n\); the statement is noted to be sharp up to an \(O(\log n)\) factor in some cube examples with variance one.

<a id="pdf-ffbe9c7b3306-p243-b005"></a>
<!-- pdf-source: page=243; block=5; confidence=0.86 -->
**Exercise 8.46.** For Boolean-valued \(f\), define \(\operatorname{err}(T)=\Pr_{x\sim\pi^{\otimes n}}[T(x)\ne f(x)]\). (a) If a depth-\(k\) deterministic tree rooted at query \(i\) is followed along a random outgoing edge according to \(\pi\), show the resulting distribution \(\overline T\) on depth-at-most-\((k-1)\) trees satisfies \(\operatorname{err}(\overline T)\le\operatorname{err}(T)+\tfrac12\operatorname{Inf}_i[f]\). (b) For a depth-zero randomized tree, show error is at least \(\min\{\Pr[f=1],\Pr[f=-1]\}\). (c) Inductively prove \(\tfrac12\sum_{i=1}^n\delta_i^{(\pi)}(T)\operatorname{Inf}_i[f]\ge\min\{\Pr[f=1],\Pr[f=-1]\}-\operatorname{err}(T)\), and deduce the stated OSSS bounds.

<a id="pdf-ffbe9c7b3306-p243-b006"></a>
<!-- pdf-source: page=243; block=6; confidence=0.99 -->
Show that the OSSS inequality fails for functions \(f:\{-1,1\}^n\to\mathbb R\); the hint uses the decision-tree shape in Figure 8.2.

<a id="pdf-ffbe9c7b3306-p244-b001"></a>
<!-- pdf-source: page=244; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p244-b002"></a>
<!-- pdf-source: page=244; block=2; confidence=0.93 -->
The notes trace the decomposition from Hoeffding’s work on symmetric U-statistics, through Hájek projections and the Efron–Stein treatment of general product functions. Efron–Stein proved $\operatorname{Var}[f]\le I[f]$ for symmetric $f$; Steele extended this to nonsymmetric $f$ using a Fourier-basis approach.

<a id="pdf-ffbe9c7b3306-p244-b003"></a>
<!-- pdf-source: page=244; block=3; confidence=0.90 -->
The notes connect the $p$-biased cube to random graphs and percolation, and credit Russo with the Margulis–Russo formula and later work with developing biased Fourier analysis and threshold results, including the biased KKL theorem.

<a id="pdf-ffbe9c7b3306-p245-b001"></a>
<!-- pdf-source: page=245; block=1; confidence=0.89 -->
The notes attribute early theoretical-computer-science use of $p$-biased Fourier analysis to Furst, Jackson, and Smith; they cite Talagrand and Friedgut–Kalai for threshold results, and Matula and Erdős–Rényi for clique and connectivity sharp thresholds. Bollobás–Thomason proved weak-threshold results related to Exercise 8.29.

<a id="pdf-ffbe9c7b3306-p245-b002"></a>
<!-- pdf-source: page=245; block=2; confidence=0.95 -->
Finite and locally compact abelian group Fourier analysis is identified as a broader subject, with Rudin and Terras cited as references.

<a id="pdf-ffbe9c7b3306-p245-b003"></a>
<!-- pdf-source: page=245; block=3; confidence=0.99 -->
For recursive majority, \(\operatorname{RDT}(\mathrm{Maj}_3^{\otimes d})=o(3^d)\). The cited upper bound is \((8/3)^d\), which is not optimal; the best known upper and lower bounds are \(O(2.65^d)\) and \(\Omega(2.55^d)\), respectively.

<a id="pdf-ffbe9c7b3306-p245-b004"></a>
<!-- pdf-source: page=245; block=4; confidence=0.88 -->
The presented OSSS proof follows Lee; an alternate proof in Exercise 8.46 is due to Jain and Zhang. The notes give attributions for the Condorcet Jury Theorem, Shapley value, and several exercises; “revealment” is credited to Schramm and Steif.

<a id="pdf-ffbe9c7b3306-p245-b005"></a>
<!-- pdf-source: page=245; block=5; confidence=0.90 -->
The notes ask whether a result related to Exercise 8.44(b) extends to functions $f:\{-1,1\}^n\to[-1,1]$; the question is answered by stating a conjecture on the next page.

<a id="pdf-ffbe9c7b3306-p246-b001"></a>
<!-- pdf-source: page=246; block=1; confidence=0.98 -->
**Conjecture (Aaronson–Ambainis).** For $f:\{-1,1\}^n\to[-1,1]$, $\operatorname{MaxInf}[f]\ge \operatorname{poly}(\operatorname{Var}[f]/\deg(f))$.

<a id="pdf-ffbe9c7b3306-p246-b002"></a>
<!-- pdf-source: page=246; block=2; confidence=0.96 -->
The conjecture would have consequences for limits on efficient quantum computation. The cited best result in its direction is $\operatorname{MaxInf}[f]\ge \operatorname{poly}(\operatorname{Var}[f]/2^{\deg(f)})$.

<a id="pdf-ffbe9c7b3306-p247-b001"></a>
<!-- pdf-source: page=247; block=1; confidence=1.00 -->
# Chapter 9: Basics of hypercontractivity

<a id="pdf-ffbe9c7b3306-p247-b002"></a>
<!-- pdf-source: page=247; block=2; confidence=1.00 -->
**Hypercontractivity Theorem.** If \(f:\{-1,1\}^n\to\mathbb R\) and \(1\le p\le q\le\infty\), then \(\|T_\rho f\|_q\le\|f\|_p\) for \(0\le\rho\le\sqrt{(p-1)/(q-1)}\).

<a id="pdf-ffbe9c7b3306-p247-b003"></a>
<!-- pdf-source: page=247; block=3; confidence=1.00 -->
The chapter develops the Bonami lemma and the \((2,q)\)- and \((p,2)\)-hypercontractivity cases; the full theorem is deferred to Chapter 10.

<a id="pdf-ffbe9c7b3306-p247-b004"></a>
<!-- pdf-source: page=247; block=4; confidence=0.94 -->
**Lemma (Bonami).** If \(f:\{-1,1\}^n\to\mathbb R\) has degree \(k\), then \(\|f\|_4\le 3^{k/2}\|f\|_2\).

<a id="pdf-ffbe9c7b3306-p247-b005"></a>
<!-- pdf-source: page=247; block=5; confidence=1.00 -->
Low-degree cube polynomials have controlled distributions; the lemma supports applications including KKL and the Invariance Principle.

<a id="pdf-ffbe9c7b3306-p247-b006"></a>
<!-- pdf-source: page=247; block=6; confidence=1.00 -->
**\((2,q)\)-Hypercontractivity Theorem.** If \(f:\{-1,1\}^n\to\mathbb R\) and \(2\le q\le\infty\), then \(\|T_{1/\sqrt{q-1}}f\|_q\le\|f\|_2\). Consequently, if \(f\) has degree at most \(k\), \(\|f\|_q\le(q-1)^{k/2}\|f\|_2\).

<a id="pdf-ffbe9c7b3306-p247-b007"></a>
<!-- pdf-source: page=247; block=7; confidence=1.00 -->
This case quantifies the smoothing effect of \(T_\rho\) and yields level inequalities and tail bounds for low-degree polynomials.

<a id="pdf-ffbe9c7b3306-p248-b001"></a>
<!-- pdf-source: page=248; block=1; confidence=0.99 -->
**\((p,2)\)-Hypercontractivity Theorem.** For \(f:\{-1,1\}^n\to\mathbb R\) and \(1\le p\le2\), \(\|T_{\sqrt{p-1}}f\|_2\le\|f\|_p\). Equivalently, \(\operatorname{Stab}_\rho[f]\le\|f\|_{1+\rho}^2\) for \(0\le\rho\le1\).

<a id="pdf-ffbe9c7b3306-p248-b002"></a>
<!-- pdf-source: page=248; block=2; confidence=1.00 -->
By Hölder's inequality this result is equivalent to the \((2,q)\) case; for indicator functions it expresses small-set expansion of the noisy hypercube.

<a id="pdf-ffbe9c7b3306-p248-b003"></a>
<!-- pdf-source: page=248; block=3; confidence=1.00 -->
## 9.1. Low-degree polynomials are reasonable

<a id="pdf-ffbe9c7b3306-p248-b004"></a>
<!-- pdf-source: page=248; block=4; confidence=1.00 -->
The section studies moment conditions that rule out extreme behavior of random variables.

<a id="pdf-ffbe9c7b3306-p248-b005"></a>
<!-- pdf-source: page=248; block=5; confidence=1.00 -->
**Definition 9.1.** For \(B\ge1\), a real random variable \(X\) is \(B\)-reasonable if \(\mathbb E[X^4]\le B\,\mathbb E[X^2]^2\), equivalently \(\|X\|_4\le B^{1/4}\|X\|_2\).

<a id="pdf-ffbe9c7b3306-p248-b006"></a>
<!-- pdf-source: page=248; block=6; confidence=1.00 -->
If \(X\) is \(B\)-reasonable, then \(\mathbb E[|X|^3]\le\sqrt B\,\mathbb E[X^2]^{3/2}\), by Cauchy–Schwarz.

<a id="pdf-ffbe9c7b3306-p248-b007"></a>
<!-- pdf-source: page=248; block=7; confidence=0.96 -->
A uniform sign is 1-reasonable, a standard Gaussian is 3-reasonable, and a uniform random variable on \([-1,1]\) is \(9/5\)-reasonable. A Bernoulli variable with \(\Pr[y=1]=2^{-n}\) and \(\Pr[y=0]=1-2^{-n}\) requires \(B\ge2^n\).

<a id="pdf-ffbe9c7b3306-p249-b001"></a>
<!-- pdf-source: page=249; block=1; confidence=1.00 -->
The section illustrates tail and anticoncentration estimates that follow from the fourth-moment condition.

<a id="pdf-ffbe9c7b3306-p249-b002"></a>
<!-- pdf-source: page=249; block=2; confidence=1.00 -->
**Proposition 9.3.** If \(X\not\equiv0\) is \(B\)-reasonable, then for every \(t>0\), \(\Pr[|X|\ge t\|X\|_2]\le B/t^4\).

<a id="pdf-ffbe9c7b3306-p249-b003"></a>
<!-- pdf-source: page=249; block=3; confidence=0.98 -->
**Proof.** Markov's inequality gives \(\Pr[|X|\ge t\|X\|_2]=\Pr[X^4\ge t^4\|X\|_2^4]\le\mathbb E[X^4]/(t^4\mathbb E[X^2]^2)\le B/t^4\).

<a id="pdf-ffbe9c7b3306-p249-b004"></a>
<!-- pdf-source: page=249; block=4; confidence=1.00 -->
A fourth-moment bound also gives a lower bound on the probability that \(|X|\) is away from zero.

<a id="pdf-ffbe9c7b3306-p249-b005"></a>
<!-- pdf-source: page=249; block=5; confidence=0.97 -->
**Proposition 9.4.** If \(X\not\equiv0\) is \(B\)-reasonable, then for \(0\le t\le1\), \(\Pr[|X|>t\|X\|_2]\ge(1-t^2)^2/B\).

<a id="pdf-ffbe9c7b3306-p249-b006"></a>
<!-- pdf-source: page=249; block=6; confidence=0.98 -->
**Proof.** Applying Paley–Zygmund to \(X^2\), \(\Pr[|X|\ge t\|X\|_2]\ge(1-t^2)^2\mathbb E[X^2]^2/\mathbb E[X^4]\ge(1-t^2)^2/B\).

<a id="pdf-ffbe9c7b3306-p249-b007"></a>
<!-- pdf-source: page=249; block=7; confidence=1.00 -->
A generalization is deferred to Exercise 9.12.

<a id="pdf-ffbe9c7b3306-p249-b008"></a>
<!-- pdf-source: page=249; block=8; confidence=1.00 -->
For a discrete random variable, a positive lower bound on the probability of each attained value ensures reasonableness.

<a id="pdf-ffbe9c7b3306-p249-b009"></a>
<!-- pdf-source: page=249; block=9; confidence=1.00 -->
**Proposition 9.5.** For a discrete random variable \(X\) with mass function \(\pi\), let \(\lambda=\min_{x\in\operatorname{range}(X)}\Pr[X=x]\). Then \(X\) is \((1/\lambda)\)-reasonable.

<a id="pdf-ffbe9c7b3306-p249-b010"></a>
<!-- pdf-source: page=249; block=10; confidence=0.99 -->
**Proof.** Let \(M=\|X\|_\infty\). Since \(\Pr[|X|=M]\ge\lambda\), \(\mathbb E[X^2]\ge\lambda M^2\), hence \(M^2\le\mathbb E[X^2]/\lambda\). Therefore \(\mathbb E[X^4]\le M^2\mathbb E[X^2]\le(1/\lambda)\mathbb E[X^2]^2\).

<a id="pdf-ffbe9c7b3306-p250-b001"></a>
<!-- pdf-source: page=250; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p250-b002"></a>
<!-- pdf-source: page=250; block=2; confidence=0.94 -->
A normalized sum of independent uniform signs can be close to Gaussian and still have a very small smallest-atom probability. The text notes that constructing an unreasonable sign-valued polynomial appears to require many variables and high degree; Example 9.2 uses the degree-$n$ polynomial $y=\prod_{i=1}^n(1+x_i)/2$.

<a id="pdf-ffbe9c7b3306-p250-b003"></a>
<!-- pdf-source: page=250; block=3; confidence=1.00 -->
**Bonami Lemma.** If \(f:\{-1,1\}^n\to\mathbb R\) has degree at most \(k\), then \(\mathbb E[f^4]\le9^k(\mathbb E[f^2])^2\), equivalently \(\|f\|_4\le3^{k/2}\|f\|_2\).

<a id="pdf-ffbe9c7b3306-p250-b004"></a>
<!-- pdf-source: page=250; block=4; confidence=0.96 -->
The lemma is a basic hypercontractive estimate and suffices for applications such as KKL and the Invariance Principle.

<a id="pdf-ffbe9c7b3306-p250-b005"></a>
<!-- pdf-source: page=250; block=5; confidence=0.98 -->
**Proof.** Induct on $n$, with constant functions as the trivial cases $k=0$ or $n=0$. For $n\ge1$, decompose $f=x_n d+e$, where $d=D_nf$ has degree at most $k-1$, $e=E_nf$ has degree at most $k$, and both are independent of $x_n$. Using independence and the moments of a uniform sign gives
\[
\mathbb E[f^4]=\mathbb E[d^4]+6\mathbb E[d^2e^2]+\mathbb E[e^4].
\]
This proof continues on page 251.

<a id="pdf-ffbe9c7b3306-p251-b001"></a>
<!-- pdf-source: page=251; block=1; confidence=0.99 -->
## 9.1. Low-degree polynomials are reasonable

<a id="pdf-ffbe9c7b3306-p251-b002"></a>
<!-- pdf-source: page=251; block=2; confidence=0.99 -->
The decomposition gives \(\mathbb E[f^2]=\mathbb E[d^2]+\mathbb E[e^2]\). By induction, \(\mathbb E[d^4]\le9^{k-1}(\mathbb E[d^2])^2\) and \(\mathbb E[e^4]\le9^k(\mathbb E[e^2])^2\). Cauchy–Schwarz bounds the cross term, yielding \(\mathbb E[f^4]\le9^k(\mathbb E[f^2])^2\).

<a id="pdf-ffbe9c7b3306-p251-b003"></a>
<!-- pdf-source: page=251; block=3; confidence=0.95 -->
The same argument works when each independent input has mean zero, third moment zero, and fourth moment at most $9$, including standard Gaussians and uniform variables on $[-1,1]$.

<a id="pdf-ffbe9c7b3306-p251-b004"></a>
<!-- pdf-source: page=251; block=4; confidence=0.98 -->
**Corollary 9.6.** Let $x_1,\ldots,x_n$ be independent random variables, not necessarily identically distributed, with $\mathbb E[x_i]=\mathbb E[x_i^3]=0$, and suppose each is $B$-reasonable. If $f=F(x_1,\ldots,x_n)$ for a multilinear polynomial $F$ of degree at most $k$, then $f$ is $\max(B,9)^k$-reasonable.

<a id="pdf-ffbe9c7b3306-p251-b005"></a>
<!-- pdf-source: page=251; block=5; confidence=0.95 -->
Combining the Bonami Lemma with Proposition 9.4 gives a lower bound on the probability that a nonconstant low-degree function deviates from its mean.

<a id="pdf-ffbe9c7b3306-p251-b006"></a>
<!-- pdf-source: page=251; block=6; confidence=0.93 -->
**Theorem 9.7.** Let $f:\{-1,1\}^n\to\mathbb R$ be nonconstant of degree at most $k$. Set $\mu=\mathbb E[f]$ and $\sigma=\sqrt{\operatorname{Var}(f)}$. Then
\[
\Pr_{x\sim\{-1,1\}^n}\bigl[|f(x)-\mu|>\tfrac12\sigma\bigr]\ge \frac1{16}\,9^{1-k}.
\]

<a id="pdf-ffbe9c7b3306-p252-b001"></a>
<!-- pdf-source: page=252; block=1; confidence=0.97 -->
**Proof.** Let $g=(f-\mu)/\sigma$. Then $\deg(g)\le k$, $\|g\|_2=1$, and the Bonami Lemma makes $g$ $9^k$-reasonable. Proposition 9.4 applied with $t=1/2$ gives the stated probability bound.

<a id="pdf-ffbe9c7b3306-p252-b002"></a>
<!-- pdf-source: page=252; block=2; confidence=0.95 -->
The concentration theorem is applied to give a short proof of the FKN theorem: a Boolean function with first-level Fourier weight $1-\delta$ is $O(\delta)$-close to a signed coordinate.

<a id="pdf-ffbe9c7b3306-p252-b003"></a>
<!-- pdf-source: page=252; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p252-b004"></a>
<!-- pdf-source: page=252; block=4; confidence=0.99 -->
## 9.2. Small subsets of the hypercube are noise-sensitive

<a id="pdf-ffbe9c7b3306-p252-b005"></a>
<!-- pdf-source: page=252; block=5; confidence=0.98 -->
For each degree component \(f^{=k}\), the Bonami Lemma gives \(\|T_{1/3}f^{=k}\|_4=3^{-k/2}\|f^{=k}\|_4\le\|f^{=k}\|_2\).

<a id="pdf-ffbe9c7b3306-p253-b001"></a>
<!-- pdf-source: page=253; block=1; confidence=1.00 -->
## 9.2. Small subsets of the hypercube are noise-sensitive

<a id="pdf-ffbe9c7b3306-p253-b002"></a>
<!-- pdf-source: page=253; block=2; confidence=0.95 -->
**Theorem (2, 4)-Hypercontractivity.** For a function $f:\{-1,1\}^n\to\mathbb R$, $\|T_{1/\sqrt3}f\|_4\leq\|f\|_2$.

<a id="pdf-ffbe9c7b3306-p253-b003"></a>
<!-- pdf-source: page=253; block=3; confidence=0.88 -->
**Proof.** Induct on dimension, writing $f(x)=d(x')+x_ne(x')$ and $T=T_{1/\sqrt3}$. Expanding in the last coordinate and using Cauchy–Schwarz gives
$$\mathbb E[(Tf)^4]\leq \mathbb E[(Td)^4]+2\sqrt{\mathbb E[(Td)^4]\mathbb E[(Te)^4]}+\mathbb E[(Te)^4].$$
By induction this is at most $\mathbb E[d^2]^2+2\mathbb E[d^2]\mathbb E[e^2]+\mathbb E[e^2]^2=\mathbb E[f^2]^2$, proving the claim.

<a id="pdf-ffbe9c7b3306-p253-b004"></a>
<!-- pdf-source: page=253; block=4; confidence=0.90 -->
The operator is contractive from $L^2$ to $L^4$; this is viewed as a quantitative smoothing property. Self-adjointness and composition relate the $L^2$ norm of $T_{1/\sqrt3}f$ to the square root of the noise stability $\operatorname{Stab}_{1/3}[f]$, motivating a norm-transfer argument by Hölder’s inequality.

<a id="pdf-ffbe9c7b3306-p254-b001"></a>
<!-- pdf-source: page=254; block=1; confidence=1.00 -->
## 9. Basics of hypercontractivity

<a id="pdf-ffbe9c7b3306-p254-b002"></a>
<!-- pdf-source: page=254; block=2; confidence=0.95 -->
**Theorem (4/3, 2)-Hypercontractivity.** For $f:\{-1,1\}^n\to\mathbb R$,
$$\tag{9.5}\|T_{1/\sqrt3}f\|_2\leq\|f\|_{4/3}.$$
Equivalently,
$$\tag{9.6}\operatorname{Stab}_{1/3}[f]\leq\|f\|_{4/3}^2.$$

<a id="pdf-ffbe9c7b3306-p254-b003"></a>
<!-- pdf-source: page=254; block=3; confidence=0.95 -->
**Proof.** Set $T=T_{1/\sqrt3}$. By self-adjointness, Hölder’s inequality, and the (2, 4) theorem, $\|Tf\|_2^2=\langle f,T(Tf)\rangle\leq\|f\|_{4/3}\|T(Tf)\|_4\leq\|f\|_{4/3}\|Tf\|_2$. Divide by $\|Tf\|_2$ when it is nonzero; the zero case is immediate.

<a id="pdf-ffbe9c7b3306-p254-b004"></a>
<!-- pdf-source: page=254; block=4; confidence=0.90 -->
For Boolean indicators the right side of (9.5) depends on the set’s measure and yields a useful bound on the probability that noise keeps a point inside the set.

<a id="pdf-ffbe9c7b3306-p254-b005"></a>
<!-- pdf-source: page=254; block=5; confidence=0.97 -->
**Corollary 9.8.** If $A\subseteq\{-1,1\}^n$ has measure $\alpha$, then
$$\operatorname{Stab}_{1/3}[1_A]=\Pr_{x\sim\{-1,1\}^n,\,y\sim N_{1/3}(x)}[x\in A,\ y\in A]\leq\alpha^{3/2}.$$
Equivalently, for $\alpha>0$, $\Pr_{x\sim A,\,y\sim N_{1/3}(x)}[y\in A]\leq\alpha^{1/2}$.

<a id="pdf-ffbe9c7b3306-p254-b006"></a>
<!-- pdf-source: page=254; block=6; confidence=0.96 -->
**Proof.** Apply (9.5) to $1_A$: $\|1_A\|_{4/3}^2=(\mathbb E|1_A|^{4/3})^{3/2}=\alpha^{3/2}$.

<a id="pdf-ffbe9c7b3306-p254-b007"></a>
<!-- pdf-source: page=254; block=7; confidence=0.92 -->
For a codimension-$k$ subcube of measure $\alpha=2^{-k}$, the conditional probability that noise at rate $1/3$ stays in the subcube is $(2/3)^k=\alpha^{\log_2(3/2)}\leq\alpha^{1/2}$. The bound is described as essentially sharp for Hamming balls.

<a id="pdf-ffbe9c7b3306-p254-b008"></a>
<!-- pdf-source: page=254; block=8; confidence=0.92 -->
**Definition 9.10.** The $n$-dimensional $\rho$-stable hypercube graph is the complete directed graph on $\{-1,1\}^n$ whose edge $(x,y)$ has weight $\Pr[(X,Y)=(x,y)]$ for a $\rho$-correlated pair $(X,Y)$. For $\rho=1-2\delta$, it is also called the $\delta$-noisy hypercube graph; equivalently, $X$ is uniform and $Y$ is obtained by independently flipping each coordinate of $X$ with probability $\delta$.

<a id="pdf-ffbe9c7b3306-p255-b001"></a>
<!-- pdf-source: page=255; block=1; confidence=1.00 -->
## 9.2. Small subsets of the hypercube are noise-sensitive

<a id="pdf-ffbe9c7b3306-p255-b002"></a>
<!-- pdf-source: page=255; block=2; confidence=0.90 -->
The edge weights are nonnegative and sum to one; each vertex has total incoming and outgoing weight $2^{-n}$. The graph is symmetric, and can be viewed as the reversible Markov chain that sends $x$ to $N_\rho(x)$, with uniform stationary distribution. For $\rho\in[0,1]$, one step corresponds to continuous-time hypercube evolution for time $\ln(1/\rho)$.

<a id="pdf-ffbe9c7b3306-p255-b003"></a>
<!-- pdf-source: page=255; block=3; confidence=0.95 -->
Corollary 9.8 says that in the $1/3$-stable hypercube graph, a random outgoing edge from a uniformly chosen vertex in a set $A$ of measure $\alpha$ exits $A$ with probability at least $1-\sqrt\alpha$. The text points to a general-$\rho$ small-set expansion result later in the book.

<a id="pdf-ffbe9c7b3306-p255-b004"></a>
<!-- pdf-source: page=255; block=4; confidence=0.92 -->
The indicator result also applies to $g:\{-1,1\}^n\to\{-1,0,1\}$ with $\alpha=\Pr[g\ne0]=\mathbb E|g|=\mathbb E[g^2]$. Taking $g=D_i f$ for Boolean $f$ identifies $\operatorname{Stab}_{1/3}[g]$ with the $1/3$-stable influence of coordinate $i$; thus small influence implies still smaller stable influence.

<a id="pdf-ffbe9c7b3306-p255-b005"></a>
<!-- pdf-source: page=255; block=5; confidence=0.95 -->
**Corollary 9.12.** For $f:\{-1,1\}^n\to\{-1,1\}$ and every coordinate $i$, $\operatorname{Inf}^{(1/3)}_i[f]\leq(\operatorname{Inf}_i[f])^{3/2}$.

<a id="pdf-ffbe9c7b3306-p255-b006"></a>
<!-- pdf-source: page=255; block=6; confidence=0.83 -->
Summing the preceding inequality over coordinates is suggested as a route toward the KKL theorem. The section then begins to infer that a Boolean-valued function of small mean cannot place much Fourier weight on low degrees; the precise continuation is absent from the supplied page.

<a id="pdf-ffbe9c7b3306-p256-b001"></a>
<!-- pdf-source: page=256; block=1; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p256-b002"></a>
<!-- pdf-source: page=256; block=2; confidence=0.99 -->
Section 9.3 studies extensions of single-bit hypercontractivity from the (2,4) case to general (2,q) and (p,2) norms.

<a id="pdf-ffbe9c7b3306-p256-b003"></a>
<!-- pdf-source: page=256; block=3; confidence=0.99 -->
**Definition 9.13.** For 1 ≤ p ≤ q ≤ ∞ and 0 ≤ ρ < 1, a real random variable X with ‖X‖q < ∞ is (p,q,ρ)-hypercontractive if ‖a + ρbX‖q ≤ ‖a + bX‖p for every pair of real constants a,b.

<a id="pdf-ffbe9c7b3306-p256-b004"></a>
<!-- pdf-source: page=256; block=4; confidence=0.98 -->
By homogeneity it suffices to check the inequality with a = 1 or b = 1; validity at ρ implies validity for every smaller ρ′. Hypercontractivity forces E[X] = 0, but allowing arbitrary translations a supports induction arguments.

<a id="pdf-ffbe9c7b3306-p257-b001"></a>
<!-- pdf-source: page=257; block=1; confidence=0.99 -->
**Proposition 9.15.** If X and Y are independent (p,q,ρ)-hypercontractive random variables, then X + Y is also (p,q,ρ)-hypercontractive.

<a id="pdf-ffbe9c7b3306-p257-b002"></a>
<!-- pdf-source: page=257; block=2; confidence=0.96 -->
The one-bit (2,4) and (4/3,2) hypercontractivity results give ρ = 1/√3. The section generalizes to (2,q,ρ) and (p,2,ρ) for uniform ±1 bits, leaving other p,q and random-variable distributions to Chapter 10.

<a id="pdf-ffbe9c7b3306-p257-b003"></a>
<!-- pdf-source: page=257; block=3; confidence=0.99 -->
**Proposition 9.16.** For a uniform ±1 bit x, ‖a + ρbx‖6 ≤ ‖a + bx‖2 for all real a,b if and only if ρ ≤ 1/√5. Equivalently, x is (2,6,1/√5)-hypercontractive.

<a id="pdf-ffbe9c7b3306-p257-b004"></a>
<!-- pdf-source: page=257; block=4; confidence=0.99 -->
**Proof.** Raising to the sixth power gives (9.8): E[(a + ρbx)^6] ≤ E[(a + bx)^2]^3. The case a = 0 is immediate; otherwise homogeneity permits a = 1. Using E[x^k] = 0 for odd k and 1 for even k, (9.8) becomes (9.9): 1 + 15ρ²b² + 15ρ⁴b⁴ + ρ⁶b⁶ ≤ (1 + b²)^3 = 1 + 3b² + 3b⁴ + b⁶. The b² coefficient requires 15ρ² ≤ 3, or ρ ≤ 1/√5, and this condition suffices termwise. Letting b tend to zero shows necessity.

<a id="pdf-ffbe9c7b3306-p257-b005"></a>
<!-- pdf-source: page=257; block=5; confidence=0.92 -->
The analogous coefficient comparison for q = 8 gives the threshold ρ ≤ 1/√7, suggesting the general bound stated in Theorem 9.17.

<a id="pdf-ffbe9c7b3306-p257-b006"></a>
<!-- pdf-source: page=257; block=6; confidence=0.98 -->
**Theorem 9.17.** For a uniformly random sign \(x\), \(\|a+\rho bx\|_q\le\|a+bx\|_2\) for all real \(a,b\) whenever \(\rho\le1/\sqrt{q-1}\). Equivalently, \(x\) is \((2,q,1/\sqrt{q-1})\)-hypercontractive.

<a id="pdf-ffbe9c7b3306-p258-b001"></a>
<!-- pdf-source: page=258; block=1; confidence=0.98 -->
For even q, coefficient comparison as in Proposition 9.16 proves the result. For general real q, the direct binomial expansion is obstructed by negative coefficients on the right-hand side. The proof instead establishes the dual (p,2,ρ) inequality, then exchanges the norms across 2.

<a id="pdf-ffbe9c7b3306-p258-b002"></a>
<!-- pdf-source: page=258; block=2; confidence=0.99 -->
**Theorem 9.18.** For a uniform ±1 bit x and 1 ≤ p < 2, ‖a + ρbx‖2 ≤ ‖a + bx‖p for all real a,b whenever 0 ≤ ρ ≤ √(p − 1). Thus x is (p,2,√(p − 1))-hypercontractive.

<a id="pdf-ffbe9c7b3306-p258-b003"></a>
<!-- pdf-source: page=258; block=3; confidence=0.96 -->
**Proof.** By homogeneity and monotonicity in ρ, take a = 1 and ρ = √(p − 1). A standard reduction allows assuming 1 + bx ≥ 0 for both bit values, hence |b| ≤ 1; continuity reduces to |b| < 1. Write b = ε. The desired inequality is equivalent to (9.10): E[(1 + √(p−1) εx)^2]^(p/2) ≤ E[(1 + εx)^p]. The left side equals (1 + (p−1)ε²)^(p/2), bounded by 1 + p(p−1)ε²/2 as in (9.11), using (1+t)^θ ≤ 1 + θt for t ≥ 0 and 0 ≤ θ ≤ 1. Expand the right side by the generalized binomial theorem and use symmetry of x; its constant and quadratic terms are 1 + p(p−1)ε²/2, and its remaining even-power terms have coefficients p(p−1)…(p−(2k−1))/(2k)!, which are nonnegative for 1 ≤ p ≤ 2. This proves (9.10).

<a id="pdf-ffbe9c7b3306-p259-b001"></a>
<!-- pdf-source: page=259; block=1; confidence=0.92 -->
Theorem 9.17 follows from Theorem 9.18 by self-adjointness of the noise operator, which transfers the norm inequality across conjugate exponents.

<a id="pdf-ffbe9c7b3306-p259-b002"></a>
<!-- pdf-source: page=259; block=2; confidence=0.99 -->
**Proposition 9.19.** Let $T$ be self-adjoint on $L^2(\Omega,\pi)$, let $1\le p,q\le\infty$, and let $p',q'$ be the conjugate Hölder indices. If $\|Tf\|_q\le C\|f\|_p$ for every $f$, then $\|Tg\|_{p'}\le C\|g\|_{q'}$ for every $g$.

<a id="pdf-ffbe9c7b3306-p259-b003"></a>
<!-- pdf-source: page=259; block=3; confidence=0.99 -->
**Proof.** By sharp Hölder duality and self-adjointness, $\|Tg\|_{p'}=\sup_{\|f\|_p=1}\langle f,Tg\rangle=\sup_{\|f\|_p=1}\langle Tf,g\rangle\le\sup_{\|f\|_p=1}\|Tf\|_q\|g\|_{q'}\le C\|g\|_{q'}$, using Hölder's inequality and the assumed operator bound.

<a id="pdf-ffbe9c7b3306-p259-b004"></a>
<!-- pdf-source: page=259; block=4; confidence=0.94 -->
For a uniform sign bit, the preceding results establish the stated one-bit $(2,q)$ and $(p,2)$ hypercontractive bounds; the next section extends them to the $n$-bit cube by induction.

<a id="pdf-ffbe9c7b3306-p259-b005"></a>
<!-- pdf-source: page=259; block=5; confidence=1.00 -->
## 9.4. Two-function hypercontractivity and induction

<a id="pdf-ffbe9c7b3306-p259-b006"></a>
<!-- pdf-source: page=259; block=6; confidence=0.98 -->
For a uniform sign, the one-bit estimates are \(\|T_{\sqrt{p-1}}f\|_2\le\|f\|_p\) for \(p\le2\), and \(\|T_{1/\sqrt{q-1}}f\|_q\le\|f\|_2\) for \(q\ge2\). The section extends these facts to functions on the full cube by induction.

<a id="pdf-ffbe9c7b3306-p260-b001"></a>
<!-- pdf-source: page=260; block=1; confidence=0.91 -->
The one-bit result motivates a two-function extension of the noise-stability bound: for $0\le\rho\le1$, $\mathbb E_{\rho\text{-correlated}}[f(x)f(y)]\le\|f\|_{1+\rho}^2$.

<a id="pdf-ffbe9c7b3306-p260-b002"></a>
<!-- pdf-source: page=260; block=2; confidence=0.95 -->
For functions $f,g$ on the cube, the proposed two-function bound is $\mathbb E_{(x,y)\;\rho\text{-correlated}}[f(x)g(y)]\le\|f\|_{1+\rho}\|g\|_{1+\rho}$. (9.12)

<a id="pdf-ffbe9c7b3306-p260-b003"></a>
<!-- pdf-source: page=260; block=3; confidence=0.91 -->
For indicator functions, the bound controls transitions between sets in the $\rho$-stable hypercube; splitting the correlation parameter suggests allowing different norm exponents.

<a id="pdf-ffbe9c7b3306-p260-b004"></a>
<!-- pdf-source: page=260; block=4; confidence=0.78 -->
Choose $0\le r,s\le1$ with $\rho=rs$. The noise-operator identity and Cauchy–Schwarz give $\mathbb E_{\rho\text{-correlated}}[f(x)g(y)]=\mathbb E[T_{\sqrt r}f\cdot T_{\sqrt s}g]\le\|T_{\sqrt r}f\|_2\|T_{\sqrt s}g\|_2\le\|f\|_{1+r}\|g\|_{1+s}$. (9.13) The last inequality uses $(p,2)$ hypercontractivity, at this point established only for one bit.

<a id="pdf-ffbe9c7b3306-p260-b005"></a>
<!-- pdf-source: page=260; block=5; confidence=0.99 -->
**Weak Two-Function Hypercontractivity Theorem.** Let \(f,g:\{-1,1\}^n\to\mathbb R\), let \(0\le r,s\le1\), and suppose \(0\le\rho\le\sqrt{rs}\le1\). Then \(\mathbb E_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]\le\|f\|_{1+r}\|g\|_{1+s}\).

<a id="pdf-ffbe9c7b3306-p260-b006"></a>
<!-- pdf-source: page=260; block=6; confidence=0.93 -->
The restriction $r,s\le1$ is later removed; the theorem is now known for $n=1$, and the following induction extends it to all dimensions.

<a id="pdf-ffbe9c7b3306-p261-b001"></a>
<!-- pdf-source: page=261; block=1; confidence=0.93 -->
The two-function formulation extends to general dimension by induction on coordinate restrictions; a derivative-based extension is also mentioned as an exercise.

<a id="pdf-ffbe9c7b3306-p261-b002"></a>
<!-- pdf-source: page=261; block=2; confidence=0.99 -->
**Two-Function Hypercontractivity Induction Theorem.** Let \(0\le\rho\le1\) and suppose \(\mathbb E_{(x,y)\ \rho\text{-correlated}}[f(x)g(y)]\le\|f\|_p\|g\|_q\) holds for all \(f,g\in L^2(\Omega,\pi)\). Then it holds for all \(f,g\in L^2(\Omega^n,\pi^{\otimes n})\).

<a id="pdf-ffbe9c7b3306-p261-b003"></a>
<!-- pdf-source: page=261; block=3; confidence=0.97 -->
**Proof.** Induct on $n$, with the one-coordinate case as the hypothesis. For $n>1$, write $x=(x',x_n)$ and $y=(y',y_n)$ for a $\rho$-correlated pair under the product measure, and let $f_{x_n},g_{y_n}$ be the restrictions fixing the last coordinates. Conditioning first on $(x_n,y_n)$ and applying induction to $(x',y')$ yields $\mathbb E_{x,y}[f(x)g(y)]\le\mathbb E_{x_n,y_n}[\|f_{x_n}\|_p\|g_{y_n}\|_q]$. Set $F(x_n)=\|f_{x_n}\|_p$ and $G(y_n)=\|g_{y_n}\|_q$. The one-coordinate hypothesis bounds this by $\|F\|_p\|G\|_q$. By the product-measure definitions, $\|F\|_p=\|f\|_p$ and $\|G\|_q=\|g\|_q$, proving the claim.

<a id="pdf-ffbe9c7b3306-p261-b004"></a>
<!-- pdf-source: page=261; block=4; confidence=0.97 -->
**Remark 9.20.** If the inequality holds separately on each $(\Omega_i,\pi_i)$, for $i=1,\ldots,n$, it holds on their product $(\Omega_1\times\cdots\times\Omega_n,\pi_1\otimes\cdots\otimes\pi_n)$ by the same argument.

<a id="pdf-ffbe9c7b3306-p261-b005"></a>
<!-- pdf-source: page=261; block=5; confidence=0.96 -->
The weak two-function theorem yields the $(p,2)$ theorem by setting $g=f$ and $r=s=\rho$; Proposition 9.19 then gives the $(2,q)$ theorem on the cube.

<a id="pdf-ffbe9c7b3306-p262-b001"></a>
<!-- pdf-source: page=262; block=1; confidence=1.00 -->
## 9.5. Applications of hypercontractivity

<a id="pdf-ffbe9c7b3306-p262-b002"></a>
<!-- pdf-source: page=262; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p262-b003"></a>
<!-- pdf-source: page=262; block=3; confidence=0.94 -->
**Theorem 9.21.** If $ has degree at most $, then for every $, $.

<a id="pdf-ffbe9c7b3306-p262-b004"></a>
<!-- pdf-source: page=262; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p262-b005"></a>
<!-- pdf-source: page=262; block=5; confidence=0.91 -->
Theorem 9.21 also yields a degree-$ bound from $ to $ for $, though a different argument gives the stronger finite endpoint bound below. For linear forms, Theorems 9.21 and 9.22 imply Khintchine’s inequality: $, with positive constants depending only on $.

<a id="pdf-ffbe9c7b3306-p262-b006"></a>
<!-- pdf-source: page=262; block=6; confidence=0.98 -->
**Theorem 9.22.** If \(f:\{-1,1\}^n\to\mathbb R\) has degree at most \(k\), then \(\|f\|_2\le e^k\|f\|_1\). More generally, for \(1\le p\le2\), \(\|f\|_2\le(e^{2/p}-1)^{k/2}\|f\|_p\).

<a id="pdf-ffbe9c7b3306-p262-b007"></a>
<!-- pdf-source: page=262; block=7; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p262-b008"></a>
<!-- pdf-source: page=262; block=8; confidence=0.94 -->
Theorem 9.21 is introduced as a route to a degree-$ concentration bound, generalizing the exponential-square tail for linear forms.

<a id="pdf-ffbe9c7b3306-p263-b001"></a>
<!-- pdf-source: page=263; block=1; confidence=0.95 -->
The stated tail decay for degree-$k$ forms is of order $\exp(-\Theta(t^{2/k}))$.

<a id="pdf-ffbe9c7b3306-p263-b002"></a>
<!-- pdf-source: page=263; block=2; confidence=0.99 -->
**Theorem 9.23.** If \(f:\{-1,1\}^n\to\mathbb R\) has degree at most \(k\), then for \(t\ge(2e)^{k/2}\), \[\Pr[|f(x)|\ge t\|f\|_2]\le\exp\left(-\frac{k}{2e}t^{2/k}\right).\]

<a id="pdf-ffbe9c7b3306-p263-b003"></a>
<!-- pdf-source: page=263; block=3; confidence=0.95 -->
**Proof.** Normalize $. For $, Markov gives $. By Theorem 9.21, $. Choose $; then the bound is at most $.

<a id="pdf-ffbe9c7b3306-p263-b004"></a>
<!-- pdf-source: page=263; block=4; confidence=0.95 -->
Theorem 9.22 is used to bound below the probability that a nonconstant low-degree function exceeds its mean.

<a id="pdf-ffbe9c7b3306-p263-b005"></a>
<!-- pdf-source: page=263; block=5; confidence=0.99 -->
**Theorem 9.24.** If \(f:\{-1,1\}^n\to\mathbb R\) is nonconstant of degree at most \(k\), then \(\Pr[f(x)>\mathbb E[f]]\ge\frac14e^{-2k}\).

<a id="pdf-ffbe9c7b3306-p263-b006"></a>
<!-- pdf-source: page=263; block=6; confidence=0.98 -->
**Proof.** Subtract the mean so $. Then $. By Cauchy–Schwarz and Theorem 9.22, $, yielding the claimed lower bound.

<a id="pdf-ffbe9c7b3306-p263-b007"></a>
<!-- pdf-source: page=263; block=7; confidence=0.96 -->
The text next applies $ hypercontractivity to noise stability.

<a id="pdf-ffbe9c7b3306-p264-b001"></a>
<!-- pdf-source: page=264; block=1; confidence=0.99 -->
**Small-Set Expansion Theorem.** If \(A\subseteq\{-1,1\}^n\) has volume \(\alpha=\mathbb E[\mathbf1_A]\), then for \(0\le\rho\le1\), \(\operatorname{Stab}_\rho[\mathbf1_A]=\Pr[x\in A,y\in A]\le\alpha^{2/(1+\rho)}\), where \((x,y)\) is \(\rho\)-correlated. Equivalently, for \(\alpha>0\), \(\Pr[y\in A\mid x\in A]\le\alpha^{(1-\rho)/(1+\rho)}\).

<a id="pdf-ffbe9c7b3306-p264-b002"></a>
<!-- pdf-source: page=264; block=2; confidence=0.93 -->
A two-set version is deferred to Chapter 10.1; the text then states an influence consequence.

<a id="pdf-ffbe9c7b3306-p264-b003"></a>
<!-- pdf-source: page=264; block=3; confidence=0.98 -->
**Corollary 9.25.** For Boolean \(f\) and \(0\le\rho\le1\), \(\operatorname{Inf}^{(\rho)}_i[f]\le\operatorname{Inf}_i[f]^{2/(1+\rho)}\).

<a id="pdf-ffbe9c7b3306-p264-b004"></a>
<!-- pdf-source: page=264; block=4; confidence=0.94 -->
Small-set expansion implies that indicators of small sets have limited noise stability and Fourier weight on low levels; the text presents a higher-degree extension of the Level-1 inequality.

<a id="pdf-ffbe9c7b3306-p264-b005"></a>
<!-- pdf-source: page=264; block=5; confidence=0.94 -->
**Level-k Inequalities.** If $ has mean $ and integer $, then $.

<a id="pdf-ffbe9c7b3306-p264-b006"></a>
<!-- pdf-source: page=264; block=6; confidence=0.96 -->
For \(0<\rho\le1\), \(W^{\le k}[f]\le\rho^{-k}\operatorname{Stab}_\rho[f]\le\rho^{-k}\alpha^{2/(1+\rho)}\le\rho^{-k}\alpha^{2(1-\rho)}\). The right-hand side is minimized at \(\rho=k/(2\ln(1/\alpha))\le1\), giving the Level-\(k\) inequality \(W^{\le k}[f]\le(\frac{2e}{k}\ln(1/\alpha))^k\alpha^2\).

<a id="pdf-ffbe9c7b3306-p264-b007"></a>
<!-- pdf-source: page=264; block=7; confidence=0.99 -->
For $, Exercise 9.18 gives the sharper bound $.

<a id="pdf-ffbe9c7b3306-p264-b008"></a>
<!-- pdf-source: page=264; block=8; confidence=1.00 -->
## 9.6. Highlight: The Kahn–Kalai–Linial Theorem

<a id="pdf-ffbe9c7b3306-p264-b009"></a>
<!-- pdf-source: page=264; block=9; confidence=0.95 -->
The section recalls a two-candidate election with $ voters and a monotone rule $ under independent uniform votes; the setup continues beyond the supplied page.

<a id="pdf-ffbe9c7b3306-p265-b001"></a>
<!-- pdf-source: page=265; block=1; confidence=1.00 -->
## 9.6. Highlight: The Kahn–Kalai–Linial Theorem

<a id="pdf-ffbe9c7b3306-p265-b002"></a>
<!-- pdf-source: page=265; block=2; confidence=0.98 -->
For monotone voting rules, fixing voter \(i\)'s vote to candidate \(b\) changes the bias by \(b\,\mathrm{Inf}_i[f]\). The motivating question is to minimize the largest coordinate influence among unbiased Boolean functions.

<a id="pdf-ffbe9c7b3306-p265-b003"></a>
<!-- pdf-source: page=265; block=3; confidence=1.00 -->
**Definition 9.26.** For \(f:\{-1,1\}^n\to\mathbb R\), \(\operatorname{MaxInf}[f]=\max\{\operatorname{Inf}_i[f]:i\in[n]\}\).

<a id="pdf-ffbe9c7b3306-p265-b004"></a>
<!-- pdf-source: page=265; block=4; confidence=0.98 -->
**Theorem (Kahn–Kalai–Linial).** For every \(f:\{-1,1\}^n\to\{-1,1\}\), \[\mathrm{MaxInf}[f]\ge \mathrm{Var}[f]\cdot\Omega\!\left(\frac{\log n}{n}\right).\]

<a id="pdf-ffbe9c7b3306-p265-b005"></a>
<!-- pdf-source: page=265; block=5; confidence=0.97 -->
The variance factor accommodates biased functions; the text notes the bounds \(\mathrm{Var}[f]/n\le \mathrm{MaxInf}[f]\le\mathrm{Var}[f]\), attributed to Poincaré and Exercise 2.8.

<a id="pdf-ffbe9c7b3306-p265-b006"></a>
<!-- pdf-source: page=265; block=6; confidence=0.92 -->
**Proposition 9.27.** If \(f:\{-1,1\}^n\to\{-1,1\}\) is monotone and \(\mathbb E[f]\ge-0.99\), there is \(J\subseteq[n]\), \(|J|=O(n/\log n)\), such that fixing coordinates in \(J\) to \(+1\) gives \(\mathbb E[f^{J\mid(+1,\ldots,+1)}]\ge0.99\) (9.14). Symmetrically, if \(\mathbb E[f]\le0.99\), some \(J\) of that size satisfies \(\mathbb E[f^{J\mid(-1,\ldots,-1)}]\le-0.99\).

<a id="pdf-ffbe9c7b3306-p265-b007"></a>
<!-- pdf-source: page=265; block=7; confidence=0.99 -->
**Proof.** By symmetry, consider bribery for \(+1\). Repeatedly choose a coordinate of maximum influence in the current restricted function: first for \(f_0=f\), then for \(f_1=f^{i_1\mapsto1}\), and continue. The proof continues on page 266.

<a id="pdf-ffbe9c7b3306-p266-b001"></a>
<!-- pdf-source: page=266; block=1; confidence=0.99 -->
For each step, \(\mathbb E[f_{t+1}]\ge\mathbb E[f_t]+\mathrm{MaxInf}[f_t]\). Until the target expectation is reached, \(-0.99\le\mathbb E[f_t]<0.99\), so \(\mathrm{Var}[f_t]=\Omega(1)\); KKL then gives \(\mathrm{MaxInf}[f_t]=\Omega(\log n/n)\). Thus at most \(O(n/\log n)\) bribes suffice to raise the expectation to \(0.99\).

<a id="pdf-ffbe9c7b3306-p266-b002"></a>
<!-- pdf-source: page=266; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p266-b003"></a>
<!-- pdf-source: page=266; block=3; confidence=0.97 -->
The section turns to proving KKL, focusing on unbiased functions with total influence at most \(0.1\log n\). For a balanced set in the cube, small total influence means boundary size is within a constant factor of the minimum; the stated structural aim is to show some coordinate then has large influence.

<a id="pdf-ffbe9c7b3306-p267-b001"></a>
<!-- pdf-source: page=267; block=1; confidence=0.95 -->
**KKL Edge-Isoperimetric Theorem.** If \(f:\{-1,1\}^n\to\{-1,1\}\) is nonconstant and \(\widetilde I[f]=I[f]/\operatorname{Var}[f]\ge1\), then \[\operatorname{MaxInf}[f]\ge\frac{9}{\widetilde I[f]^2}\,9^{-\widetilde I[f]}.\]

<a id="pdf-ffbe9c7b3306-p267-b002"></a>
<!-- pdf-source: page=267; block=2; confidence=0.98 -->
The stated edge-isoperimetric bound is sharp at normalized influence \(1\), and is nontrivial for unbiased functions up to total influence \(\Theta(\log n)\).

<a id="pdf-ffbe9c7b3306-p267-b003"></a>
<!-- pdf-source: page=267; block=3; confidence=0.90 -->
**Proof.** Assume \(f\) is nonconstant. If \(\widehat I[f]\ge0.1\log n\), then \(I[f]\ge0.1\,\mathrm{Var}[f]\log n\), yielding \(\mathrm{MaxInf}[f]\ge0.1\,\mathrm{Var}[f]\log n/n\). Otherwise the edge theorem gives a lower bound of order \((\log n)^{-2}9^{-0.1\log n}=\Omega(n^{-0.317})\), which dominates \(\mathrm{Var}[f]\,\Omega(\log n/n)\).

<a id="pdf-ffbe9c7b3306-p267-b004"></a>
<!-- pdf-source: page=267; block=4; confidence=0.98 -->
The proof proceeds contrapositively: small coordinate influences make derivatives supported on small sets; small-set expansion gives high noise sensitivity, pushing the Fourier weight involving each coordinate to high levels and forcing large total influence.

<a id="pdf-ffbe9c7b3306-p267-b005"></a>
<!-- pdf-source: page=267; block=5; confidence=0.96 -->
**Proof of the KKL Theorem.** For unbiased \(f\), the argument uses \[3\cdot3^{-I[f]}\le3\operatorname{Stab}_{1/3}[f]\le I^{(1/3)}[f]\le\sum_{i=1}^n\operatorname{Inf}_i[f]^{3/2}\le\operatorname{MaxInf}[f]^{1/2}I[f].\]

<a id="pdf-ffbe9c7b3306-p268-b001"></a>
<!-- pdf-source: page=268; block=1; confidence=0.94 -->
For Boolean mean-zero `f`, the Fourier formula gives `I_{1/3}[f] = ∑_{|S|≥1} |S|(1/3)^{|S|-1} f̂(S)^2 ≥ 3 Stab_{1/3}[f]`. If `S` is drawn from the spectral sample, then `3 Stab_{1/3}[f] = 3 E[3^{-|S|}] ≥ 3·3^{-E|S|} = 3·3^{-I[f]}` by convexity of `s ↦ 3^{-s}` (9.15).

<a id="pdf-ffbe9c7b3306-p268-b002"></a>
<!-- pdf-source: page=268; block=2; confidence=0.98 -->
The section derives a stronger KKL consequence and Friedgut’s Junta Theorem by applying an influence bound to coordinates of small influence; stronger junta bounds follow when Fourier weight is concentrated at low degree.

<a id="pdf-ffbe9c7b3306-p268-b003"></a>
<!-- pdf-source: page=268; block=3; confidence=0.93 -->
**Theorem 9.28.** Let \(f:\{-1,1\}^n\to\{-1,1\}\), \(0<\varepsilon\le1\), and \(k\ge0\). Define \(\tau=\frac{\varepsilon^2}{I[f]^2}9^{-k}\) and \(J=\{j\in[n]:\operatorname{Inf}_j[f]\ge\tau\}\). Then \(|J|\le(I[f]^3/\varepsilon^2)9^k\), and the Fourier spectrum is \(\varepsilon\)-concentrated on \(\{S:S\subseteq J\}\cup\{S:|S|>k\}\).

<a id="pdf-ffbe9c7b3306-p268-b004"></a>
<!-- pdf-source: page=268; block=4; confidence=0.86 -->
**Proof.** Summing Corollary 9.12 over `i ∉ J` gives `∑_{i∉J} Inf_i^{(1/3)}[f] ≤ ∑_{i∉J} Inf_i[f]^{3/2} ≤ (max_{i∉J} Inf_i[f]^{1/2}) I[f] ≤ τ^{1/2} I[f] ≤ ε 3^{-k}`.

<a id="pdf-ffbe9c7b3306-p269-b001"></a>
<!-- pdf-source: page=269; block=1; confidence=0.96 -->
\[\sum_{i\notin J}\operatorname{Inf}^{(1/3)}_i[f]=\sum_S|S\cap\bar J|3^{1-|S|}\widehat f(S)^2\ge3^{-k}\sum_{S\notin\mathcal F}\widehat f(S)^2.\] Since \(S\notin\mathcal F\) implies \(|S\cap\bar J|\ge1\) and \(|S|\le k\), combining this with the preceding bound gives \(\sum_{S\notin\mathcal F}\widehat f(S)^2\le\varepsilon\).

<a id="pdf-ffbe9c7b3306-p269-b002"></a>
<!-- pdf-source: page=269; block=2; confidence=0.84 -->
If the spectrum is `2ε`-concentrated on `F′`, Proposition 3.31 gives `2ε`-closeness to the Boolean junta `sgn(f_{⊆J})`; Exercise 3.34 then gives an `ε`-close Boolean junta on `J`.

<a id="pdf-ffbe9c7b3306-p269-b003"></a>
<!-- pdf-source: page=269; block=3; confidence=0.84 -->
**Remark 9.29.** Using Corollary 9.25 instead of Corollary 9.12 improves the junta size in Theorem 9.28 to `(I[f]^{2+η}/ε^{1+η}) C(η)^k` for any `η > 0`, where `C(η) = (2/η + 1)^2`.

<a id="pdf-ffbe9c7b3306-p269-b004"></a>
<!-- pdf-source: page=269; block=4; confidence=0.87 -->
**Theorem (Friedgut’s Junta Theorem).** For Boolean `f` and `0 < ε ≤ 1`, `f` is `ε`-close to an `exp(O(I[f]/ε))`-junta. There is `J ⊆ [n]` with `|J| ≤ exp(O(I[f]/ε))` such that the Fourier spectrum is `2ε`-concentrated on `{S ⊆ J : |S| ≤ I[f]/ε}`. This follows from Theorem 9.28 with `k = I[f]/ε`, using the degree-tail Markov bound.

<a id="pdf-ffbe9c7b3306-p269-b005"></a>
<!-- pdf-source: page=269; block=5; confidence=0.97 -->
A width-`w` DNF has Fourier concentration through degree `O(w log(1/ε))`; LTFs have concentration through degree `O(1/ε²)`, leading to sharper junta bounds.

<a id="pdf-ffbe9c7b3306-p269-b006"></a>
<!-- pdf-source: page=269; block=6; confidence=0.99 -->
**Corollary 9.30.** Every width-`w` DNF is `ε`-close to a `(1/ε)^{O(w)}`-junta.

<a id="pdf-ffbe9c7b3306-p269-b007"></a>
<!-- pdf-source: page=269; block=7; confidence=0.89 -->
**Corollary 9.31.** If `f` is an LTF and `0 < ε, η ≤ 1/2`, then `f` is `ε`-close to a junta on `I[f]^{2+η}(1/η)^{O(1/ε²)}` coordinates. For constant `ε`, choosing `η` on the order of `1/log(I[f])` gives a junta of size `I[f]^2 polylog(I[f])`. The text notes this is essentially optimal by the majority example, and extends the conclusion to constant-degree PTFs using uniform noise stability.

<a id="pdf-ffbe9c7b3306-p270-b001"></a>
<!-- pdf-source: page=270; block=1; confidence=0.98 -->
**Corollary 9.32.** If Boolean `f` satisfies `Var[f] ≥ 1/2`, then some nonempty `S ⊆ [n]` with `|S| ≤ O(I[f])` has `f̂(S)^2 ≥ exp(−O(I[f]^2))`.

<a id="pdf-ffbe9c7b3306-p270-b002"></a>
<!-- pdf-source: page=270; block=2; confidence=0.94 -->
**Proof.** Apply Friedgut’s theorem with `ε = 1/8`: Fourier weight at least `3/4` lies on `F = {S ⊆ J : |S| ≤ 8I[f]}`, where `|J| ≤ exp(O(I[f]))`. Since `f̂(∅)^2 = 1 − Var[f] ≤ 1/2`, nonempty sets in `F` carry weight at least `1/4`. There are at most `|J|^{8I[f]} = exp(O(I[f]^2))` such sets, so one has squared coefficient at least `exp(−O(I[f]^2))` by pigeonhole.

<a id="pdf-ffbe9c7b3306-p270-b003"></a>
<!-- pdf-source: page=270; block=3; confidence=0.96 -->
**Remark 9.33.** If `Var[f] < 1/2`, then the empty coefficient satisfies `f̂(∅)^2 ≥ 1/2`; a refinement of Corollary 9.32 is assigned in Exercise 9.32.

<a id="pdf-ffbe9c7b3306-p270-b004"></a>
<!-- pdf-source: page=270; block=4; confidence=0.95 -->
It is open whether Corollary 9.32 can guarantee a coefficient with `f̂(S)^2 ≥ exp(−O(I[f]))`; Exercise 9.33 gives related context.

<a id="pdf-ffbe9c7b3306-p270-b005"></a>
<!-- pdf-source: page=270; block=5; confidence=0.99 -->
Exercises and notes.

<a id="pdf-ffbe9c7b3306-p270-b006"></a>
<!-- pdf-source: page=270; block=6; confidence=0.99 -->
Show that for each `1 < b < B`, some `b`-reasonable random variable `X` has `1 + X` not `B`-reasonable.

<a id="pdf-ffbe9c7b3306-p270-b007"></a>
<!-- pdf-source: page=270; block=7; confidence=0.96 -->
For degree-at-most-one `f` and independent `3`-reasonable `x_i` satisfying `E[x_i] = E[x_i^3] = 0`, show `f(x)` is `3`-reasonable; the hint suggests direct calculation or refining the Bonami Lemma proof.

<a id="pdf-ffbe9c7b3306-p270-b008"></a>
<!-- pdf-source: page=270; block=8; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p271-b001"></a>
<!-- pdf-source: page=271; block=1; confidence=0.99 -->
## 9.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p271-b002"></a>
<!-- pdf-source: page=271; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p271-b003"></a>
<!-- pdf-source: page=271; block=3; confidence=0.99 -->
Prove Corollary 9.6.

<a id="pdf-ffbe9c7b3306-p271-b004"></a>
<!-- pdf-source: page=271; block=4; confidence=0.95 -->
For $0\leq\delta\leq 1/1600$, real $f,\ell$ satisfying $|\ell^2-1|>39\sqrt{\delta}$ and $|f|=1$ must satisfy $|f-\ell|^2\geq169\delta$.

<a id="pdf-ffbe9c7b3306-p271-b005"></a>
<!-- pdf-source: page=271; block=5; confidence=0.87 -->
Show that the Bonami lemma implies the $(2,4)$ hypercontractivity theorem. (a) For fixed $0<\delta<1$, prove $\|T_{(1-\delta)/\sqrt3}f\|_4\leq\sum_{k\geq0}(1-\delta)^k\|f^{=k}\|_2\leq\delta^{-1}\|f\|_2$. (b) For the product function $g^{\oplus d}(x^{(1)},\ldots,x^{(d)})=\prod_{i=1}^d g(x^{(i)})$, show $\|T_\rho(g^{\oplus d})\|_p=\|T_\rho g\|_p^d$ for positive integer $d$, $p$, and $\rho\in[-1,1]$. (c) Deduce $\|T_{(1-\delta)/\sqrt3}f\|_4\leq\|f\|_2$ by applying (a) to $f^{\oplus d}$ and letting $d$ grow. (d) Let $\delta\to0^+$ to obtain $\|T_{1/\sqrt3}f\|_4\leq\|f\|_2$.

<a id="pdf-ffbe9c7b3306-p271-b006"></a>
<!-- pdf-source: page=271; block=6; confidence=0.99 -->
To prove $\|T_\rho f\|_q\leq\|f\|_p$ for every Boolean-cube function $f$, it suffices to establish it for nonnegative $f$.

<a id="pdf-ffbe9c7b3306-p271-b007"></a>
<!-- pdf-source: page=271; block=7; confidence=0.96 -->
**Exercise 9.8.** For fixed \(k\), show the degree-\(k\) projection is bounded in \(L^q\). For \(q\ge2\), the displayed bound is \(\|f^{\le k}\|_q\le\sqrt{q-1}^{\,k}\|f\|_q\); for \(1<q\le2\), show \(\|f^{\le k}\|_q\le(1/\sqrt{q-1})^k\|f\|_q\).

<a id="pdf-ffbe9c7b3306-p271-b008"></a>
<!-- pdf-source: page=271; block=8; confidence=1.00 -->
If \(X\) is \((p,q,\rho)\)-hypercontractive, show that \(cX\) is \((p,q,\rho)\)-hypercontractive for every \(c\in\mathbb R\).

<a id="pdf-ffbe9c7b3306-p272-b001"></a>
<!-- pdf-source: page=272; block=1; confidence=0.98 -->
If \(X\) is \((p,q,\rho)\)-hypercontractive, show \(\rho\le\|X\|_p/\|X\|_q\).

<a id="pdf-ffbe9c7b3306-p272-b002"></a>
<!-- pdf-source: page=272; block=2; confidence=0.75 -->
Assume $X$ is $(p,q,\rho)$-hypercontractive, with $X$ optionally taken discrete. (a) Prove $\mathbb E[X]=0$. (b) Prove $\rho\leq\sqrt{(p-1)/(q-1)}$; the displayed OCR is imperfect, but the hint invokes a second-order Taylor expansion.

<a id="pdf-ffbe9c7b3306-p272-b003"></a>
<!-- pdf-source: page=272; block=3; confidence=0.97 -->
Assuming $\mathbb E[X]=0$, prove: (a) $X$ is $(q,q,0)$-hypercontractive for every $q\geq1$; (b) it is $(q,q,\rho)$-hypercontractive for $0\leq\rho<1$; (c) if $X$ is $(p,q,\rho)$-hypercontractive, then it is also $(p,q,\rho')$-hypercontractive for $0\leq\rho'<\rho$.

<a id="pdf-ffbe9c7b3306-p272-b004"></a>
<!-- pdf-source: page=272; block=4; confidence=0.86 -->
For a nonconstant $(2,4,\rho)$-hypercontractive random variable $X$, prove that for every real $\theta$ and $0<t<1$, $\Pr[|X-\theta|>t\|X\|_2]\geq(1-t^2)^2\rho^4$. Normalize to $\|X\|_2=1$; for $Y=(X-\theta)^2$, establish $\mathbb E[Y]=1+\theta^2$ and $\mathbb E[Y^2]\leq(\rho^{-2}+\theta^2)^2$. Apply Paley–Zygmund to obtain the intermediate lower bound $\left(\frac{\rho^2(1-t^2)+\rho^2\theta^2}{1+\rho^2\theta^2}\right)^2$, then show it is minimized at $\theta=0$.

<a id="pdf-ffbe9c7b3306-p272-b005"></a>
<!-- pdf-source: page=272; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p272-b006"></a>
<!-- pdf-source: page=272; block=6; confidence=0.83 -->
For degree-at-most-$k$ functions, (a) prove $\|f\|_2\leq(1/(p-1))^{k/2}\|f\|_p$ for $1\leq p\leq2$, using Hölder and hypercontractivity. (b) Verify $\exp(\tfrac12(1/p-1))<1/\sqrt{p-1}$ for $1\leq p<2$, showing the bound of Theorem 9.22 is strictly stronger.

<a id="pdf-ffbe9c7b3306-p273-b001"></a>
<!-- pdf-source: page=273; block=1; confidence=0.99 -->
## 9.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p273-b002"></a>
<!-- pdf-source: page=273; block=2; confidence=0.74 -->
Prove Theorem 9.22 generally. Choose $\theta$ satisfying $1/2=\theta/p+(1-\theta)/(2+\varepsilon)$ and verify $\frac{1-\theta}{2\theta}=\frac1\varepsilon(\frac2p-1)+\frac12(\frac1p-1)$.

<a id="pdf-ffbe9c7b3306-p273-b003"></a>
<!-- pdf-source: page=273; block=3; confidence=0.86 -->
Complete the derivative-induction proof sketch. With $x=(x',x_n)$, $T=T_{1/\sqrt{q-1}}$, $d=D_nf(x')$, and $e=E_nf(x')$, use the one-coordinate $(2,q)$ estimate and Minkowski to derive $\|T_{1/\sqrt{q-1}}f\|_q^2=\|(Te)^2+(Td)^2\|_{q/2}\leq\|Te\|_q^2+\|Td\|_q^2\leq\|e\|_2^2+\|d\|_2^2=\|f\|_2^2$.

<a id="pdf-ffbe9c7b3306-p273-b004"></a>
<!-- pdf-source: page=273; block=4; confidence=0.98 -->
Deduce the $p<2<q$ cases of hypercontractivity from the $(2,q)$ and $(p,2)$ cases using the semigroup property of $T_\rho$.

<a id="pdf-ffbe9c7b3306-p273-b005"></a>
<!-- pdf-source: page=273; block=5; confidence=0.98 -->
For \(f:\{-1,1\}^n\to\{0,1\}\) with \(\mathbb E[f]=\alpha\), show \(W^1[f]\le\frac1\rho(\alpha^{2/(1+\rho)}-\alpha^2)\) for \(0<\rho\le1\). Deduce the sharp Level-1 inequality \(W^1[f]\le2\alpha^2\ln(1/\alpha)\) by taking \(\rho\to0^+\).

<a id="pdf-ffbe9c7b3306-p273-b006"></a>
<!-- pdf-source: page=273; block=6; confidence=0.91 -->
For Boolean $f$ of mean $\alpha$, show $W^{\leq k}[f]=o(\alpha)$ as $\alpha\to0$ provided $k\leq0.373\ln(1/\alpha)$.

<a id="pdf-ffbe9c7b3306-p273-b007"></a>
<!-- pdf-source: page=273; block=7; confidence=0.88 -->
Show KKL fails for bounded real-valued functions even if variance is bounded below by a positive constant; the suggested example is the clipping of $(x_1+\cdots+x_n)/\sqrt n$ to $[-1,1]$.

<a id="pdf-ffbe9c7b3306-p273-b008"></a>
<!-- pdf-source: page=273; block=8; confidence=0.97 -->
**Exercise 9.21.** (a) Show Boolean functions with \(I[f]\le O(\sqrt{\log n})\) are learnable from queries to any constant error in polynomial time. (b) Show monotone Boolean functions with this influence bound are learnable from random examples in polynomial time. (c) Show monotone Boolean functions with decision-tree size at most \(\operatorname{poly}(n)\) are learnable from random examples in polynomial time.

<a id="pdf-ffbe9c7b3306-p273-b009"></a>
<!-- pdf-source: page=273; block=9; confidence=0.83 -->
**Exercise 9.22.** Let \(f:\{-1,1\}^n\to\mathbb R\), \(q\ge2\), and suppose \(0\le\rho\le1\) satisfies \(\rho^2\le1/\sqrt{q-1}\) for some \(0\le\lambda\le1\). Then \(\|T_\rho f\|_q\le\|f\|_2^{1-\lambda}\|f\|_1^\lambda\). The scan’s exponent placement is not entirely clear.

<a id="pdf-ffbe9c7b3306-p273-b010"></a>
<!-- pdf-source: page=273; block=10; confidence=0.85 -->
For $f:\{-1,1\}^n\to[-1,1]$, $0\leq\varepsilon\leq1$, and $q\geq2+2\varepsilon$, prove $\|T_{1-\varepsilon}f\|_q^q\leq\|T_{1/\sqrt{1+2\varepsilon}}f\|_q^q\leq(\|f\|_2^2)^{1+\varepsilon}$.

<a id="pdf-ffbe9c7b3306-p274-b001"></a>
<!-- pdf-source: page=274; block=1; confidence=1.00 -->
## 9. Basics of hypercontractivity

<a id="pdf-ffbe9c7b3306-p274-b002"></a>
<!-- pdf-source: page=274; block=2; confidence=0.99 -->
For fixed $0<\rho<1$, estimate the joint upper-tail probability $\Lambda_\rho(\mu)=\Pr[z_1>t,z_2>t]$, where $(z_1,z_2)$ are standard Gaussians with correlation $\rho$ and $\Phi(t)=\mu$, as $\mu\to0$. The target is $\Lambda_\rho(\mu)=\Theta(\mu^{2/(1+\rho)})$ (9.16), which would show sharpness of the small-set expansion bound via Hamming balls.

<a id="pdf-ffbe9c7b3306-p274-b003"></a>
<!-- pdf-source: page=274; block=3; confidence=0.99 -->
**Proof step.** Use the heuristic $z_1\approx t$ under $z_1>t$, so $z_2\mid z_1=t$ has distribution $\rho t+\sqrt{1-\rho^2}\,y$ for independent standard Gaussian $y$. With $\Phi(u)\sim\phi(u)/u$ as $u\to\infty$, infer $\Pr[z_2>t\mid z_1=t]=\Theta(\mu^{(1-\rho)/(1+\rho)})$, yielding the exponent in (9.16).

<a id="pdf-ffbe9c7b3306-p274-b004"></a>
<!-- pdf-source: page=274; block=4; confidence=0.94 -->
**Proof step.** For joint density $\phi_\rho$, express $\Lambda_\rho(\mu)=\int_t^\infty\int_t^\infty \phi_\rho(z_1,z_2)\,dz_1dz_2$. Derive (9.17):
$$\int_t^\infty\int_t^\infty (z_2-\rho z_1)(z_1-\rho t)\phi_\rho(z_1,z_2)\,dz_1dz_2=\frac{(1-\rho^2)^{3/2}}{2\pi}\exp\!\left(-\frac{2}{1+\rho}\frac{t^2}{2}\right).$$
Show its right-hand side is $\Theta(\mu^{2/(1+\rho)})$.

<a id="pdf-ffbe9c7b3306-p274-b005"></a>
<!-- pdf-source: page=274; block=5; confidence=0.97 -->
**Proof step.** Show $\Pr[z_1>t-1/\rho]=\int_{t-1/\rho}^\infty\phi(z_1)\,dz_1=\Theta(\mu^{1/\rho^2})$, and verify this is asymptotically smaller than $\Theta(\mu^{2/(1+\rho)})$.

<a id="pdf-ffbe9c7b3306-p274-b006"></a>
<!-- pdf-source: page=274; block=6; confidence=0.99 -->
**Proof step.** Deduce (9.16), using the hint to make both factors $z_2-\rho z_1$ and $z_1-\rho t$ in (9.17) at least $1$.

<a id="pdf-ffbe9c7b3306-p274-b007"></a>
<!-- pdf-source: page=274; block=7; confidence=0.98 -->
**Exercise 9.25.** Let \(f:\{-1,1\}^n\to\{-1,1\}\), \(J\subseteq[n]\), and \(\bar J=[n]\setminus J\). Define \(\widetilde{\operatorname{Inf}}_J[f]=\Pr_{z\sim\{-1,1\}^{\bar J}}[f_{J\mid z}\text{ is not constant}]\).

<a id="pdf-ffbe9c7b3306-p275-b001"></a>
<!-- pdf-source: page=275; block=1; confidence=0.99 -->
For \(b\in\{-1,1\}\), define \(\widetilde{\operatorname{Inf}}_J^b[f]=\Pr_{z\sim\{-1,1\}^{\bar J}}[f_{J\mid z}\text{ can be made }b]-\Pr[f=b]=\Pr_z[f_{J\mid z}\not\equiv-b]-\Pr[f=b]\).

<a id="pdf-ffbe9c7b3306-p275-b002"></a>
<!-- pdf-source: page=275; block=2; confidence=0.97 -->
**Exercise 9.25(f).** For \(t=|J|/\sqrt n\), show \(\widetilde{\operatorname{Inf}}_J^{\mathrm{True}}[\mathrm{Maj}_n]=\Phi(t)-\tfrac12+o(1)\) and \(\widetilde{\operatorname{Inf}}_J[\mathrm{Maj}_n]=2\Phi(t)-1+o(1)\). Deduce the stated limits when \(|J|=o(\sqrt n)\) and \(|J|=\omega(\sqrt n)\).

<a id="pdf-ffbe9c7b3306-p275-b003"></a>
<!-- pdf-source: page=275; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p275-b004"></a>
<!-- pdf-source: page=275; block=4; confidence=0.99 -->
Show the exponential dependence on $I[f]$ in Friedgut’s Junta Theorem is necessary; hint: Exercise 4.15.

<a id="pdf-ffbe9c7b3306-p275-b005"></a>
<!-- pdf-source: page=275; block=5; confidence=0.75 -->
**Proof steps.** Let monotone Boolean $f$ satisfy $\operatorname{Var}[f]\ge\delta>0$, and let $0<\epsilon<1/2$. (a) Improve Proposition 9.27: find $J\subseteq[n]$ with $|J|\le O(\log(1/\epsilon)/\delta)\,n$ such that $\mathbb E[f|_{J\gets(1,\ldots,1)}]\ge1-\epsilon$. (b) Find such a $J$ with $\widetilde{\mathrm{Inf}}_J[f]\ge1-\epsilon$, using 9.25(d) and a union of two influential sets. The hint for (a) concerns the number of bribes needed to move the mean outside $[1-2\epsilon,1-\epsilon]$.

<a id="pdf-ffbe9c7b3306-p275-b006"></a>
<!-- pdf-source: page=275; block=6; confidence=0.88 -->
**Proof step.** For $f^*$, the monotonization defined in Exercise 2.52, show $\widetilde{\mathrm{Inf}}_J^b[f^*]\le\widetilde{\mathrm{Inf}}_J^b[f]$ for each $J$ and $b\in\{-1,1\}$, and hence $\widetilde{\mathrm{Inf}}_J[f^*]\le\widetilde{\mathrm{Inf}}_J[f]$.

<a id="pdf-ffbe9c7b3306-p276-b001"></a>
<!-- pdf-source: page=276; block=1; confidence=0.83 -->
**Proof step.** If $\operatorname{Var}[f]\ge\delta>0$ and $0<\epsilon<1/2$, show there is $J\subseteq[n]$ with $|J|\le O(\log(1/\epsilon)/\delta)\,n$ and $\widetilde{\mathrm{Inf}}_J[f]\ge1-\epsilon$, by combining (a) with Exercise 9.27(b).

<a id="pdf-ffbe9c7b3306-p276-b002"></a>
<!-- pdf-source: page=276; block=2; confidence=0.86 -->
**Proof step.** Establish the general-variance KKL edge-isoperimetric theorem. Replace (9.15) with $\sum_{|S|\ge1}(1/3)^{|S|}\widehat f(S)^2\ge3\operatorname{Var}[f]\cdot3^{-I[f]/\operatorname{Var}[f]}$ and apply the same convexity argument to a random nonempty $S$, sampled with probability $\widehat f(S)^2/\operatorname{Var}[f]$.

<a id="pdf-ffbe9c7b3306-p276-b003"></a>
<!-- pdf-source: page=276; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p276-b004"></a>
<!-- pdf-source: page=276; block=4; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p276-b005"></a>
<!-- pdf-source: page=276; block=5; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p276-b006"></a>
<!-- pdf-source: page=276; block=6; confidence=1.00 -->
Establish the claim in Remark 9.29.

<a id="pdf-ffbe9c7b3306-p276-b007"></a>
<!-- pdf-source: page=276; block=7; confidence=0.92 -->
**Proof step.** For nonconstant Boolean $f$, find nonempty $S\subseteq[n]$ with $|S|\le O(I[f]/\operatorname{Var}[f])$ and $\widehat f(S)^2\ge\exp(-O(I[f]^2/\operatorname{Var}[f]^2))$. Mimic Corollary 9.32 to obtain $\Omega(\operatorname{Var}[f])\exp(-O(I[f]^2/\operatorname{Var}[f]^2))$, then use Theorem 2.39 to absorb the variance factor.

<a id="pdf-ffbe9c7b3306-p276-b008"></a>
<!-- pdf-source: page=276; block=8; confidence=0.95 -->
**Proof step.** For nonconstant monotone Boolean $f$, improve Corollary 9.32 by finding nonempty $S$ with $\widehat f(S)^2\ge\exp(-O(I[f]/\operatorname{Var}[f]))$. The hint indicates $|S|\le1$ suffices via the KKL edge-isoperimetric theorem and Proposition 2.21.

<a id="pdf-ffbe9c7b3306-p276-b009"></a>
<!-- pdf-source: page=276; block=9; confidence=0.99 -->
**Exercise 9.34.** For \(f:\{-1,1\}^n\to\mathbb R\), prove \(\|f\|_4\le\operatorname{sparsity}(\widehat f)^{1/4}\|f\|_2\).

<a id="pdf-ffbe9c7b3306-p277-b001"></a>
<!-- pdf-source: page=277; block=1; confidence=1.00 -->
## 9.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p277-b002"></a>
<!-- pdf-source: page=277; block=2; confidence=0.91 -->
**Exercise 9.35.** For positive even integer $q=2r$, set $\rho=1/\sqrt{q-1}$. For functions $f_1,\ldots,f_r:\{-1,1\}^n\to\mathbb R$, prove using Hölder's inequality that $\mathbb E\!\left[\prod_{i=1}^r (T_\rho f_i)^2\right]\leq\prod_{i=1}^r\mathbb E[f_i^2]$.

<a id="pdf-ffbe9c7b3306-p277-b003"></a>
<!-- pdf-source: page=277; block=3; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p277-b004"></a>
<!-- pdf-source: page=277; block=4; confidence=0.83 -->
**Exercise 9.37.** For positive even $q=2r$ and homogeneous degree-$k$ $f:\{-1,1\}^n\to\mathbb R$, improve Theorem 9.21. (a) Show that $\mathbb E[f^q]=\sum_{S_1\triangle\cdots\triangle S_q=\varnothing}\widehat f(S_1)\cdots\widehat f(S_q)\leq\sum_{S_1\triangle\cdots\triangle S_q=\varnothing}|\widehat f(S_1)|\cdots|\widehat f(S_q)|$, equation (9.18), where the sum is over the indicated tuples. (b) Express the right side as equation (9.19), a sum over perfect matchings $M$ of the complete $q$-partite graph with parts $V_1,\ldots,V_q$, each of size $k$, and labelings $\ell:M\to[n]$, with coefficient $1/(k!)^q$ and factors $|\widehat f(T_j(M,\ell))|$, where $T_j$ consists of labels on matching edges incident to $V_j$. (c) Rewrite (9.19) as (9.20), a sum over ordered perfect matchings and indices $i_1,\ldots,i_{rk}\in[n]$, with coefficient $1/((rk)!(k!)^q)$ and factors $|\widehat f(U_j(M,i_1,\ldots,i_{rk}))|$, where $U_j=\{i_t:M(t)\text{ meets }V_j\}$.

<a id="pdf-ffbe9c7b3306-p278-b001"></a>
<!-- pdf-source: page=278; block=1; confidence=0.70 -->
**Exercise 9.37 (continued).** (d) For each ordered perfect matching $M$, prove by applying Cauchy–Schwarz $rk$ times that $\sum_{i_1,\ldots,i_{rk}=1}^n\prod_{j=1}^q|\widehat f(U_j(M,i_1,\ldots,i_{rk}))|\leq\left(\sum_{j_1,\ldots,j_k=1}^n\widehat f(\{j_1,\ldots,j_k\})^2\right)^r$. (e) Deduce the stated bound involving $|M|$, and hence $\|f\|_q\leq (|M|^{1/q}/k!)\|f\|_2$.

<a id="pdf-ffbe9c7b3306-p278-b002"></a>
<!-- pdf-source: page=278; block=2; confidence=0.00 -->


<a id="pdf-ffbe9c7b3306-p278-b003"></a>
<!-- pdf-source: page=278; block=3; confidence=0.88 -->
The notes trace hypercontractivity to Paley's 1932 square-function inequalities and his degree-two homogeneous-function bounds, with other $p$ values obtained by Riesz–Thorin interpolation. They describe Bonami's 1968 homogeneous-function inequality, Kiener's 1969 extension to arbitrary $p$ and degree, and Schreiber's independent 1969 result for multilinear polynomials over centered orthonormal random variables.

<a id="pdf-ffbe9c7b3306-p279-b001"></a>
<!-- pdf-source: page=279; block=1; confidence=0.88 -->
The notes continue that Bonami's 1970 thesis gave the full Hypercontractivity Theorem via a one-bit proof and induction, as well as the sharper combinatorial bounds of Exercises 9.37 and 9.38(c). The stronger estimate in Exercise 9.38(f) is attributed to Janson. Bonami's combinatorial argument also extends to symmetric orthonormal random variables, including Gaussian variables, with bounds depending on their $q$-norms.

<a id="pdf-ffbe9c7b3306-p279-b002"></a>
<!-- pdf-source: page=279; block=2; confidence=0.95 -->
Bonami's work was published in French and was little known among English-language mathematicians for roughly a decade.

<a id="pdf-ffbe9c7b3306-p280-b001"></a>
<!-- pdf-source: page=280; block=1; confidence=1.00 -->
## 9. Basics of hypercontractivity

<a id="pdf-ffbe9c7b3306-p280-b002"></a>
<!-- pdf-source: page=280; block=2; confidence=0.98 -->
The Gaussian Ornstein–Uhlenbeck operator satisfies the hypercontractive bound \(\|U_\rho f\|_q\le\|f\|_p\) at the sharp parameter \(\rho=\sqrt{(p-1)/(q-1)}\), for \(1\le p<q\le\infty\). The notes discuss its history and the relation to the bit-cube theorem.

<a id="pdf-ffbe9c7b3306-p280-b003"></a>
<!-- pdf-source: page=280; block=3; confidence=0.79 -->
The notes attribute sharp complex-parameter variants to Beckner, Weissler, and Epperson; mention an independent Banach-space proof of a $(q,2)$ inequality; and give attributions for the terminology, the Bonami Lemma proof, several chapter theorems, small-set expansion, level-$k$ inequalities, and optimal Khintchine constants.

<a id="pdf-ffbe9c7b3306-p281-b001"></a>
<!-- pdf-source: page=281; block=1; confidence=1.00 -->
## 9.7. Exercises and notes

<a id="pdf-ffbe9c7b3306-p281-b002"></a>
<!-- pdf-source: page=281; block=2; confidence=0.95 -->
The extremizers in Khintchine’s inequality occur either for two equal coefficients \(a_1=a_2=1/\sqrt2\), or in the limiting Gaussian case \(a_i=1/\sqrt n\) as \(n\to\infty\). The notes discuss the history of the KKL theorem and its known proofs and bounds.

<a id="pdf-ffbe9c7b3306-p281-b003"></a>
<!-- pdf-source: page=281; block=3; confidence=0.00 -->
