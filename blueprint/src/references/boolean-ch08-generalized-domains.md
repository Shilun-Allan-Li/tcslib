<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 50833afe740311645b86221ba7175d9c5dcecea394eb400cb4b9ccfcf341ce65 -->

<a id="pdf-50833afe7403-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Chapter 8. Generalized domains

<a id="pdf-50833afe7403-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Analysis of Boolean functions $f:\{0,1\}^n\to\mathbb{R}$ extends to $f:\Omega_1\times\cdots\times\Omega_n\to\mathbb{R}$ under a product distribution $\pi_1\otimes\cdots\otimes\pi_n$, since the theory mainly relies on the domain being a product probability distribution. Two exceptions: the derivative operator $D_i$ does not generalize when $|\Omega_i|>2$ (the Laplacian $L_i$ does), and hypercontractivity (Ch. 9) depends strongly on the $\pi_i$. This chapter takes all $\Omega_i$ equal and all $\pi_i$ equal (notational convenience). Classic cases: $p$-biased hypercube (§8.4), abelian groups (§8.5); generalizing the range, see Exercise 8.33.

<a id="pdf-50833afe7403-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.98 -->
## 8.1. Fourier bases for product spaces

<a id="pdf-50833afe7403-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.96 -->
**Definition 8.1.** Let $(\Omega,\pi)$ be a finite probability space with $|\Omega|\ge 2$ and $\pi$ of full support. For $n\in\mathbb{N}^+$, $L^2(\Omega^n,\pi^{\otimes n})$ denotes the real inner product space of functions $f:\Omega^n\to\mathbb{R}$ with inner product $\langle f,g\rangle=\mathbb{E}_{x\sim\pi^{\otimes n}}[f(x)g(x)]$, where $\pi^{\otimes n}$ is the product distribution on $\Omega^n$.

<a id="pdf-50833afe7403-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
**Example 8.2.** $\Omega=\{a,b,c\}$ with $\pi(a)=\pi(b)=\pi(c)=1/3$ (abstract elements). The definition will later be generalized to nondiscrete probability spaces and complex inner product spaces, but the above definition is kept for now.

<a id="pdf-50833afe7403-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.96 -->
**Notation 8.3.** $\pi_{1/2}$ denotes the uniform distribution on $\{-1,1\}$. Earlier chapters studied functions in $L^2(\{-1,1\}^n,\pi_{1/2}^{\otimes n})$, abbreviated $L^2(\{-1,1\}^n)$.

<a id="pdf-50833afe7403-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.93 -->
**Notation 8.4.** Notation for $L^2(\{-1,1\}^n)$ extends to $L^2(\Omega^n,\pi^{\otimes n})$; e.g. $\|f\|_p=\mathbb{E}_{x\sim\pi^{\otimes n}}[|f(x)|^p]^{1/p}$, and the restriction notation of §3.3.

<a id="pdf-50833afe7403-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.94 -->
Boolean Fourier analysis derives combinatorial properties of $f:\{-1,1\}^n\to\mathbb{R}$ from its coefficients in the parity-function basis of $L^2(\{-1,1\}^n)$; the aim is to do this generally for $L^2(\Omega^n,\pi^{\otimes n})$, starting from vector space bases.

<a id="pdf-50833afe7403-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.96 -->
**Definition 8.5.** For $|\Omega|=m$, the indicator (standard) basis for $L^2(\Omega,\pi)$ is the $m$ indicator functions $(1_x)_{x\in\Omega}$, where $1_x(y)=1$ if $y=x$ and $0$ if $y\neq x$.

<a id="pdf-50833afe7403-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.95 -->
**Fact 8.6.** The functions $(1_x)_{x\in\Omega}$ are nonzero, spanning, and orthogonal, so they form a basis and $\dim(L^2(\Omega,\pi))=m$. For $L^2(\Omega^n,\pi^{\otimes n})$ the indicator basis $(1_x)_{x\in\Omega^n}$ has dimension $m^n$; the expansion $f=\sum_{x\in\Omega^n}f(x)1_x$ has coefficients equal to $f$'s values, giving no new information. A different basis is wanted to yield useful Fourier formulas.

<a id="pdf-50833afe7403-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.95 -->
For $L^2(\{-1,1\}^n)$ the parity functions are $\chi_S(x)=\prod_{i\in S}x_i$. Identifying $S$ with its $0$-$1$ indicator vector, $\chi_S(x)=\prod_{i=1}^n\varphi_{S_i}(x_i)$ where $\varphi_0\equiv 1$ and $\varphi_1=\mathrm{id}$.

<a id="pdf-50833afe7403-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
The parity basis is a **product basis**. For each coordinate $i\in[n]$, $\{1,\mathrm{id}\}$ is a basis of the $2$-dimensional $L^2(\{-1,1\},\pi_{1/2})$; all $n$-fold products give a basis of $L^2(\{-1,1\}^n)$. Generally, given a basis $\varphi_0,\dots,\varphi_{m-1}$ of $L^2(\Omega,\pi)$ (with $|\Omega|=m$), the products $\varphi_{i_1}\varphi_{i_2}\cdots\varphi_{i_n}$ ($0\le i_j<m$) form a basis of $L^2(\Omega^n,\pi^{\otimes n})$.

<a id="pdf-50833afe7403-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.94 -->
The parity basis is **orthonormal**. If $\varphi_0,\dots,\varphi_{m-1}$ is orthonormal for $L^2(\Omega,\pi)$, the product basis is orthonormal for $L^2(\Omega^n,\pi^{\otimes n})$ (using that $\pi^{\otimes n}$ is a product distribution). E.g. $\{1,\mathrm{id}\}$ is orthonormal since $\mathbb{E}[1^2]=1$, $\mathbb{E}[1\cdot x_i]=0$, $\mathbb{E}[x_i^2]=1$. Orthonormality yields Parseval: if $f=\sum_{i=0}^{m-1}c_i\varphi_i$ then $\mathbb{E}[f^2]=\sum_{i=0}^{m-1}c_i^2$.

<a id="pdf-50833afe7403-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.94 -->
The parity basis contains the constant function $1$. For an orthonormal basis $\varphi_0,\dots,\varphi_{m-1}$ with $\varphi_0\equiv 1$, $\langle\varphi_0,\varphi_i\rangle=\mathbb{E}_{x\sim\pi}[\varphi_i(x)]=0$ for $i>0$. Hence if $f=\sum_{i=0}^{m-1}c_i\varphi_i$ then $\mathbb{E}[f]=c_0$ and $\mathrm{Var}[f]=\sum_{i>0}c_i^2$.

<a id="pdf-50833afe7403-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.97 -->
**Definition 8.7.** A Fourier basis for $L^2(\Omega,\pi)$ is an orthonormal basis $\varphi_0,\dots,\varphi_{m-1}$ with $\varphi_0\equiv 1$.

<a id="pdf-50833afe7403-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.96 -->
**Example 8.8.** For each $n\in\mathbb{N}^+$, the $2^n$ parity functions $(\chi_S)_{S\subseteq[n]}$ form a Fourier basis for $L^2(\{-1,1\}^n,\pi_{1/2}^{\otimes n})$.

<a id="pdf-50833afe7403-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.96 -->
**Remark 8.9.** A Fourier basis always exists: extend $\{1\}$ to a basis and apply Gram–Schmidt. It is not unique; even for $L^2(\{-1,1\},\pi_{1/2})$ both $\{1,\mathrm{id}\}$ and $\{1,-\mathrm{id}\}$ work.

<a id="pdf-50833afe7403-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.94 -->
**Example 8.10.** For $\Omega=\{a,b,c\}$ with $\pi(a)=\pi(b)=\pi(c)=1/3$, one Fourier basis (Exercise 8.4) is: $\varphi_0\equiv 1$; $\varphi_1(a)=+\sqrt2,\ \varphi_1(b)=-\sqrt2/2,\ \varphi_1(c)=-\sqrt2/2$; $\varphi_2(a)=0,\ \varphi_2(b)=+\sqrt6/2,\ \varphi_2(c)=-\sqrt6/2$.

<a id="pdf-50833afe7403-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
# 8. Generalized domains

<a id="pdf-50833afe7403-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
A Fourier basis for $L^2(\Omega^n, \pi^{\otimes n})$ can be built from a Fourier basis for $L^2(\Omega,\pi)$ by taking all $n$-fold products; the following notation makes this precise.

<a id="pdf-50833afe7403-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.93 -->
**Definition 8.11.** An $n$-dimensional multi-index is a tuple $\alpha \in \mathbb{N}^n$. Define $\operatorname{supp}(\alpha) = \{i : \alpha_i \neq 0\}$, $\#\alpha = |\operatorname{supp}(\alpha)|$, and $|\alpha| = \sum_{i=1}^n \alpha_i$. Write $\alpha \in \mathbb{N}^n_{<m}$ to emphasize that each $\alpha_i \in \{0,1,\dots,m-1\}$.

<a id="pdf-50833afe7403-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.93 -->
**Definition 8.12.** Given $\varphi_0,\dots,\varphi_{m-1} \in L^2(\Omega,\pi)$ and a multi-index $\alpha \in \mathbb{N}^n_{<m}$, define $\varphi_\alpha \in L^2(\Omega^n,\pi^{\otimes n})$ by $\varphi_\alpha(x) = \prod_{i=1}^n \varphi_{\alpha_i}(x_i)$.

<a id="pdf-50833afe7403-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.92 -->
**Proposition 8.13.** If $\varphi_0,\dots,\varphi_{m-1}$ is a Fourier basis for $L^2(\Omega,\pi)$, then $(\varphi_\alpha)_{\alpha \in \mathbb{N}^n_{<m}}$ is a Fourier basis for $L^2(\Omega^n,\pi^{\otimes n})$, with $\alpha=(0,\dots,0)$ indexing the constant function $1$.

<a id="pdf-50833afe7403-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.90 -->
**Proof.** For $\alpha,\beta \in \mathbb{N}^n_{<m}$, $\langle \varphi_\alpha,\varphi_\beta\rangle = \mathbb{E}_{x\sim\pi^{\otimes n}}[\varphi_\alpha(x)\varphi_\beta(x)] = \mathbb{E}_{x\sim\pi^{\otimes n}}\big[\prod_{i=1}^n \varphi_{\alpha_i}(x_i)\varphi_{\beta_i}(x_i)\big] = \prod_{i=1}^n \mathbb{E}_{x_i\sim\pi}[\varphi_{\alpha_i}(x_i)\varphi_{\beta_i}(x_i)]$ (product distribution) $= \prod_{i=1}^n \mathbf{1}\{\alpha_i=\beta_i\} = \mathbf{1}\{\alpha=\beta\}$ (orthonormality of $\{\varphi_0,\dots,\varphi_{m-1}\}$). So the collection is orthonormal, hence linearly independent, and is a basis because it has cardinality $m^n = \dim L^2(\Omega^n,\pi^{\otimes n})$ (Fact 8.6). $\square$

<a id="pdf-50833afe7403-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.88 -->
Any $f \in L^2(\Omega^n,\pi^{\otimes n})$ is written as a linear combination of the basis functions; $\widehat{f}(\alpha)$ denotes the Fourier coefficient on $\varphi_\alpha$.

<a id="pdf-50833afe7403-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.92 -->
**Definition 8.14.** Having fixed a Fourier basis $\varphi_0,\dots,\varphi_{m-1}$ for $L^2(\Omega,\pi)$, every $f \in L^2(\Omega^n,\pi^{\otimes n})$ is uniquely expressible as $f = \sum_{\alpha\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)\varphi_\alpha$, the Fourier expansion of $f$. The Fourier coefficient $\widehat{f}(\alpha)$ satisfies $\widehat{f}(\alpha) = \langle f, \varphi_\alpha\rangle$.

<a id="pdf-50833afe7403-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.82 -->
**Example 8.15.** With the basis of Example 8.10, let $f:\{a,b,c\}^2\to\{0,1\}$ equal $1$ iff both inputs are $c$. Then (Exercise 8.5) $f = \tfrac{1}{9} - \tfrac{\sqrt{2}}{18}\varphi_{(1,0)} - \tfrac{\sqrt{6}}{18}\varphi_{(2,0)} - \tfrac{\sqrt{2}}{18}\varphi_{(0,1)} - \tfrac{\sqrt{6}}{18}\varphi_{(0,2)} + \tfrac{1}{18}\varphi_{(1,1)} + \tfrac{\sqrt{12}}{36}\varphi_{(2,1)} + \tfrac{\sqrt{12}}{36}\varphi_{(1,2)} + \tfrac{1}{6}\varphi_{(2,2)}$.

<a id="pdf-50833afe7403-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.87 -->
Although the notation $\widehat{f}(\alpha)$ hides the basis dependence, the Fourier formulas developed next are the same for every product Fourier basis; a basis-independent development is given in Section 8.3.

<a id="pdf-50833afe7403-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
## 8.2. Generalized Fourier formulas

<a id="pdf-50833afe7403-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.87 -->
Several combinatorial/probabilistic notions have Fourier formulas, independent of the chosen basis, for functions $f \in L^2(\Omega^n,\pi^{\otimes n})$.

<a id="pdf-50833afe7403-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.83 -->
**Proposition 8.16.** For $f,g \in L^2(\Omega^n,\pi^{\otimes n})$ and any fixed product Fourier basis:
- $\mathbb{E}[f] = \widehat{f}(0)$;
- $\mathbb{E}[f^2] = \sum_{\alpha\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)^2$ (Parseval);
- $\operatorname{Var}[f] = \sum_{\alpha\neq 0} \widehat{f}(\alpha)^2$;
- $\langle f,g\rangle = \sum_{\alpha\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)\,\widehat{g}(\alpha)$ (Plancherel);
- $\operatorname{Cov}[f,g] = \sum_{\alpha\neq 0} \widehat{f}(\alpha)\,\widehat{g}(\alpha)$.

<a id="pdf-50833afe7403-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.90 -->
**Proof.** It suffices to verify Plancherel (the others follow, Exercise 8.6): $\langle f,g\rangle = \big\langle \sum_{\alpha\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)\varphi_\alpha, \sum_{\beta\in\mathbb{N}^n_{<m}} \widehat{g}(\beta)\varphi_\beta\big\rangle = \sum_{\alpha,\beta\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)\widehat{g}(\beta)\langle\varphi_\alpha,\varphi_\beta\rangle = \sum_{\alpha\in\mathbb{N}^n_{<m}} \widehat{f}(\alpha)\widehat{g}(\alpha)$ by orthonormality of $(\varphi_\alpha)$. $\square$

<a id="pdf-50833afe7403-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.87 -->
The key definition for basis-independent Fourier expansions follows; for $L^2(\{-1,1\})$ it appeared in Exercise 3.28.

<a id="pdf-50833afe7403-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Definition 8.17.** Let $J \subseteq [n]$ and $\bar{J} = [n]\setminus J$. For $f \in L^2(\Omega^n,\pi^{\otimes n})$, the projection of $f$ on coordinates $J$ is $f^{\subseteq J} \in L^2(\Omega^n,\pi^{\otimes n})$ defined by $f^{\subseteq J}(x) = \mathbb{E}_{x'\sim\pi^{\otimes \bar{J}}}[f(x_J, x')]$, where $x_J \in \Omega^J$ are the $J$-coordinates of $x$; i.e. the expectation of $f$ when the $\bar{J}$-coordinates are rerandomized. $f^{\subseteq J}$ has domain $\Omega^n$ though it depends only on the coordinates in $J$. Forming $f^{\subseteq J}$ is the application of a projection linear operator to $f$, the expectation over $\bar{J}$ operator $\mathrm{E}_{\bar{J}}$, taken as its definition $\mathrm{E}_{\bar{J}} f = f^{\subseteq J}$; when $\bar{J}=\{i\}$ is a singleton write simply $\mathrm{E}_i$.

<a id="pdf-50833afe7403-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.83 -->
**Remark 8.18.** This definition of $\mathrm{E}_i$ is consistent with Definition 2.23; Exercise 8.7 asks to verify that $\mathrm{E}_{\bar{J}}$ is a self-adjoint projection linear operator.

<a id="pdf-50833afe7403-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.88 -->
**Proposition 8.19.** For $J \subseteq [n]$, $f \in L^2(\Omega^n,\pi^{\otimes n})$, and any fixed product Fourier basis: $f^{\subseteq J} = \sum_{\substack{\alpha\in\mathbb{N}^n_{<m}\\ \operatorname{supp}(\alpha)\subseteq J}} \widehat{f}(\alpha)\,\varphi_\alpha$.

<a id="pdf-50833afe7403-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.93 -->
**Proof.** Since $\mathrm{E}_{\bar{J}}$ is a linear operator, it suffices to verify for each $\alpha$ that $\phi_\alpha^{\subseteq J} = \phi_\alpha$ if $\operatorname{supp}(\alpha)\subseteq J$, and $=0$ otherwise. If $\operatorname{supp}(\alpha)\subseteq J$, then $\phi_\alpha$ does not depend on the $\bar{J}$-coordinates, so $\phi_\alpha^{\subseteq J} = \phi_\alpha$. So suppose $\operatorname{supp}(\alpha)\not\subseteq J$. Since $\phi_\alpha(x)=\big(\prod_{i\in J}\phi_{\alpha_i}(x_i)\big)\big(\prod_{i\in\bar{J}}\phi_{\alpha_i}(x_i)\big)$, we can write $\phi_\alpha = \phi_{\alpha_J}\cdot\phi_{\alpha_{\bar{J}}}$, where $\phi_{\alpha_J}$ depends only on the coordinates in $J$, [text continues on the next page].

<a id="pdf-50833afe7403-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
**Proof (continued).** Here $\phi_{\alpha_{\bar{J}}}$ depends only on the coordinates in $\bar{J}$, and $\mathbb{E}[\phi_{\alpha_{\bar{J}}}]=0$ precisely because $\operatorname{supp}(\alpha)\not\subseteq J$. Thus for every $x\in\Omega^n$,
$$\phi^{\subseteq J}_\alpha(x)=\mathbb{E}_{x'\sim\pi^{\otimes\bar{J}}}[\phi_{\alpha_J}(x_J)\,\phi_{\alpha_{\bar{J}}}(x')]=\phi_{\alpha_J}(x_J)\cdot\mathbb{E}_{x'\sim\pi^{\otimes\bar{J}}}[\phi_{\alpha_{\bar{J}}}(x')]=0,$$
as needed. $\square$

<a id="pdf-50833afe7403-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Corollary 8.20.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ and fix a product Fourier basis. If $f$ depends only on the coordinates in $J\subseteq[n]$, then $\widehat{f}(\alpha)=0$ whenever $\mathrm{supp}(\alpha)\not\subseteq J$.

<a id="pdf-50833afe7403-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->
**Proof.** Immediate from Proposition 8.19, since $f=f^{\subseteq J}$. $\square$

<a id="pdf-50833afe7403-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.93 -->
**Corollary 8.21.** Let $i\in[n]$ and $f\in L^2(\Omega^n,\pi^{\otimes n})$. For any fixed product Fourier basis,
$$\mathrm{E}_i f=\sum_{\alpha:\,\alpha_i=0}\widehat{f}(\alpha)\,\varphi_\alpha.$$

<a id="pdf-50833afe7403-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.85 -->
For $\Omega=\{-1,1\}$ influence was $\mathrm{Inf}_i[f]=\mathbb{E}[(\mathrm{D}_i f)^2]$, but the derivative operator is not basis-invariant and does not generalize to arbitrary $\Omega$. Instead one takes the identity $\mathrm{Inf}_i[f]=\langle f,\mathrm{L}_i f\rangle$ from Proposition 2.26 as the definition.

<a id="pdf-50833afe7403-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.92 -->
**Definition 8.22.** For $i\in[n]$ and $f\in L^2(\Omega^n,\pi^{\otimes n})$, the $i$th coordinate Laplacian operator $\mathrm{L}_i$ is the self-adjoint projection linear operator $\mathrm{L}_i f=f-\mathrm{E}_i f$. The influence of coordinate $i$ is $\mathrm{Inf}_i[f]=\langle f,\mathrm{L}_i f\rangle=\langle \mathrm{L}_i f,\mathrm{L}_i f\rangle$. The total influence is $\mathrm{I}[f]=\sum_{i=1}^n \mathrm{Inf}_i[f]$. (Intuitively $\mathrm{L}_i f$ is the part of $f$ depending on coordinate $i$.)

<a id="pdf-50833afe7403-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.93 -->
**Proposition 8.23.** Let $i\in[n]$, $f\in L^2(\Omega^n,\pi^{\otimes n})$. For any fixed product Fourier basis,
$$\mathrm{L}_i f=\sum_{\alpha:\,\alpha_i\neq0}\widehat{f}(\alpha)\,\varphi_\alpha,\quad \mathrm{Inf}_i[f]=\sum_{\alpha:\,\alpha_i\neq0}\widehat{f}(\alpha)^2,\quad \mathrm{I}[f]=\sum_{\alpha}\#\alpha\cdot\widehat{f}(\alpha)^2.$$

<a id="pdf-50833afe7403-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.93 -->
**Proof.** First formula from Corollary 8.21; second from Plancherel; third by summing the second over $i$. $\square$

<a id="pdf-50833afe7403-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.85 -->
Exercise 8.9 (cf. Exercise 2.21) asks the reader to verify the following computationally useful formulas.

<a id="pdf-50833afe7403-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
**Proposition 8.24.** For $i\in[n]$, $f\in L^2(\Omega^n,\pi^{\otimes n})$,
$$\mathrm{Inf}_i[f]=\mathbb{E}_{x\sim\pi^{\otimes n}}\big[\mathrm{Var}_{x_i'\sim\pi}[f(x_1,\dots,x_{i-1},x_i',x_{i+1},\dots,x_n)]\big].$$
If furthermore $f$ has range $\{-1,1\}$, then
$$\mathrm{Inf}_i[f]=\mathbb{E}[\,|\mathrm{L}_i f|\,]=2\Pr_{x\sim\pi^{\otimes n},\,x_i'\sim\pi}[f(x)\neq f(x_1,\dots,x_{i-1},x_i',x_{i+1},\dots,x_n)].$$

<a id="pdf-50833afe7403-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->
**Example 8.25.** Continuing Example 8.15: $\{a,b,c\}$ uniform and $f:\{a,b,c\}^2\to\{0,1\}$ equal to $1$ iff both inputs are $c$. Via Proposition 8.24: $\mathrm{Var}[f(x_1,a)]=\mathrm{Var}[f(x_1,b)]=0$ and $\mathrm{Var}[f(x_1,c)]=\tfrac13\cdot\tfrac23=\tfrac29$ (Bernoulli with parameter $\tfrac13$), so $\mathrm{Inf}_1[f]=\tfrac13\cdot\tfrac29=\tfrac2{27}$. Alternatively, using Proposition 8.23 and the Fourier expansion from Example 8.15, $\mathrm{Inf}_1[f]=(-\tfrac{\sqrt2}{18})^2+(-\tfrac{\sqrt6}{18})^2+(\tfrac{1}{18})^2+(\tfrac{\sqrt{12}}{36})^2+(\tfrac{\sqrt{12}}{36})^2+(\tfrac16)^2=\tfrac2{27}$.

<a id="pdf-50833afe7403-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.92 -->
**Definition 8.26.** Fix $(\Omega^n,\pi^{\otimes n})$, $\rho\in[0,1]$, $x\in\Omega^n$. Write $y\sim N_\rho(x)$ when, independently for each $i\in[n]$, $y_i=x_i$ with probability $\rho$ and $y_i$ is drawn from $\pi$ with probability $1-\rho$. If $x\sim\pi^{\otimes n}$ and $y\sim N_\rho(x)$, then $(x,y)$ is a $\rho$-correlated pair under $\pi^{\otimes n}$ (symmetric in $x,y$).

<a id="pdf-50833afe7403-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Definition 8.27.** For $L^2(\Omega^n,\pi^{\otimes n})$ and $\rho\in[0,1]$, the noise operator $T_\rho$ acts by $T_\rho f(x)=\mathbb{E}_{y\sim N_\rho(x)}[f(y)]$. The noise stability of $f$ at $\rho$ is $\mathrm{Stab}_\rho[f]=\langle f,T_\rho f\rangle=\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[f(x)f(y)]$.

<a id="pdf-50833afe7403-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.90 -->
**Proposition 8.28.** For $\rho\in[0,1]$ and $f\in L^2(\Omega^n,\pi^{\otimes n})$, in any fixed product Fourier basis,
$$T_\rho f=\sum_{\alpha\in\mathbb{N}^n_{<m}}\rho^{\#\alpha}\,\widehat{f}(\alpha)\,\varphi_\alpha,\qquad \mathrm{Stab}_\rho[f]=\sum_{\alpha\in\mathbb{N}^n_{<m}}\rho^{\#\alpha}\,\widehat{f}(\alpha)^2.$$

<a id="pdf-50833afe7403-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**Proof.** Let $J$ be a $\rho$-random subset of $[n]$ (each $i$ included independently with probability $\rho$). By definition $T_\rho f(x)=\mathbb{E}_J[f^{\subseteq J}(x)]$, so by Proposition 8.19,
$$T_\rho f(x)=\mathbb{E}_J\Big[\sum_{\mathrm{supp}(\alpha)\subseteq J}\widehat{f}(\alpha)\varphi_\alpha(x)\Big]=\sum_{\alpha\in\mathbb{N}^n_{<m}}\rho^{\#\alpha}\widehat{f}(\alpha)\varphi_\alpha(x),$$
since $\Pr[\mathrm{supp}(\alpha)\subseteq J]=\rho^{\#\alpha}$. The $\mathrm{Stab}_\rho[f]$ formula follows from Plancherel. $\square$

<a id="pdf-50833afe7403-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.90 -->
**Remark 8.29.** The first formula lets one extend the definition of $T_\rho f$ to values of $\rho$ outside $[0,1]$.

<a id="pdf-50833afe7403-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
**Definition 8.30.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, $\rho\in(0,1]$, $i\in[n]$, the $\rho$-stable influence of $i$ on $f$ is
$$\mathrm{Inf}^{(\rho)}_i[f]=\rho^{-1}\mathrm{Stab}_\rho[\mathrm{L}_i f]=\sum_{\alpha:\,\alpha_i\neq0}\rho^{\#\alpha-1}\widehat{f}(\alpha)^2,$$
and $\mathrm{I}^{(\rho)}[f]=\sum_{i=1}^n \mathrm{Inf}^{(\rho)}_i[f]$. The $\rho^{-1}$ factor is for consistency with the $L^2(\{-1,1\}^n)$ case.

<a id="pdf-50833afe7403-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.90 -->
**Proposition 8.31.** Suppose $f\in L^2(\Omega^n,\pi^{\otimes n})$ has $\mathrm{Var}[f]\le1$. Given $0<\delta<1$, $0<\varepsilon\le1$, let $J=\{i\in[n]:\mathrm{Inf}^{(1-\delta)}_i[f]\ge\varepsilon\}$. Then $|J|\le \dfrac{1}{\delta\varepsilon}$.

<a id="pdf-50833afe7403-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.92 -->
**Definition 8.32.** For nonzero $f\in L^2(\Omega^n,\pi^{\otimes n})$, the degree $\deg(f)$ is the least $k\in\mathbb{N}$ such that $f$ is a sum of $k$-juntas (functions depending on at most $k$ coordinates).

<a id="pdf-50833afe7403-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.90 -->
**Proposition 8.33.** For nonzero $f\in L^2(\Omega^n,\pi^{\otimes n})$ and any fixed product Fourier basis, $\deg(f)=\max\{\#\alpha:\widehat{f}(\alpha)\neq0\}$.

<a id="pdf-50833afe7403-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.92 -->
**Proof.** The inequality $\deg(f)\le\max\{\#\alpha:\widehat{f}(\alpha)\neq0\}$ is immediate from the Fourier expansion $f=\sum_{\alpha:\widehat{f}(\alpha)\neq0}\widehat{f}(\alpha)\phi_\alpha$. [Proof continues on the next page.]

<a id="pdf-50833afe7403-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.93 -->
**Proof (conclusion).** Each function $\widehat{f}(\alpha)\phi_\alpha$ depends on at most $\#\alpha$ coordinates. For the reverse inequality, suppose $f = g_1 + \cdots + g_m$ where each $g_i$ depends on at most $k$ coordinates. By Corollary 8.20 each $g_i$ has its Fourier support on functions $\phi_\alpha$ with $\#\alpha \le k$. But $\widehat{f}(\alpha) = \widehat{g_1}(\alpha) + \cdots + \widehat{g_m}(\alpha)$, so the same is true of $f$. $\square$

<a id="pdf-50833afe7403-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.99 -->
## 8.3. Orthogonal decomposition

<a id="pdf-50833afe7403-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
Basis-free "Fourier expansion" for $f \in L^2(\Omega^n, \pi^{\otimes n})$, also known as the Hoeffding, Efron–Stein, or ANOVA decomposition. Goal: express
$$f = \sum_{S \subseteq [n]} f^{=S} \tag{8.1}$$
where each $f^{=S} \in L^2(\Omega^n, \pi^{\otimes n})$ is the "contribution to $f$ coming from coordinates $S$ (but not from any subset of $S$)."

<a id="pdf-50833afe7403-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.88 -->
**Definition (Boolean case).** For $f\colon \{-1,1\}^n \to \mathbb{R}$, define $f^{=S} = \hat f(S)\,\chi_S$. This satisfies (8.1) and:

1. $f^{=S}$ depends only on the coordinates in $S$.
2. If $T \subsetneq S$ and $g$ depends only on the coordinates in $T$, then $\langle f^{=S}, g\rangle = 0$.

The decomposition is orthogonal: $\langle f^{=S}, f^{=T}\rangle = 0$ whenever $S \neq T$.

<a id="pdf-50833afe7403-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.85 -->
**Definition (basis-free direction).** Using the projection of $f$ onto coordinates $J$, $f^{\subseteq J}$ (Exercise 3.28, Definition 8.17) — the contribution from coordinates $J$ collectively, with a probabilistic (basis-free) definition — one has
$$f^{\subseteq J} = \sum_{S \subseteq J} f^{=S}. \tag{8.2}$$
Inverting (8.2) yields a basis-free definition of the $f^{=S}$. For general $f \in L^2(\Omega^n,\pi^{\otimes n})$, the projections $f^{\subseteq J}$ are defined as in Definition 8.17 and one requires (8.2) to hold.

<a id="pdf-50833afe7403-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.85 -->
**Definition (inverting (8.2)).** For $J = \varnothing$: $f^{=\varnothing} = f^{\subseteq\varnothing}$, the constant function equal to $\mathbb{E}[f]$. For singletons $J=\{j\}$: from $f^{\subseteq\{j\}} = f^{=\varnothing} + f^{=\{j\}}$,
$$f^{=\{j\}} = f^{\subseteq\{j\}} - f^{\subseteq\varnothing}, \qquad f^{=\{j\}}(x) = \mathbb{E}_{x\sim\pi^{\otimes n}}[\,f \mid x_j\,] - \mathbb{E}_{x\sim\pi^{\otimes n}}[f(x)],$$
which depends only on $x_j$ and measures the change in expectation given $x_j$. For $J=\{i,j\}$: from $f^{\subseteq\{i,j\}} = f^{=\varnothing} + f^{=\{i\}} + f^{=\{j\}} + f^{=\{i,j\}}$,
$$f^{=\{i,j\}} = f^{\subseteq\{i,j\}} - f^{\subseteq\{i\}} - f^{\subseteq\{j\}} + f^{\subseteq\varnothing}.$$
Continuing by inclusion–exclusion defines all $f^{=S}$.

<a id="pdf-50833afe7403-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
**Lemma 8.34.** Let $f, g \in L^2(\Omega^n, \pi^{\otimes n})$. Assume $f$ does not depend on any coordinate outside $I \subseteq [n]$, and $g$ does not depend on any coordinate outside $J \subseteq [n]$. Then
$$\langle f, g\rangle = \langle f^{\subseteq I\cap J},\, g^{\subseteq I\cap J}\rangle.$$

<a id="pdf-50833afe7403-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.87 -->
**Proof.** WLOG $I \cup J = [n]$. Split $x \in \Omega^n$ as $(x_{I\cap J}, x_{I\setminus J}, x_{J\setminus I})$. Then
$$\langle f, g\rangle = \mathbb{E}_{x_{I\cap J},\,x_{I\setminus J},\,x_{J\setminus I}}\!\big[\,f(x_{I\cap J}, x_{I\setminus J})\cdot g(x_{I\cap J}, x_{J\setminus I})\big].$$
Since $x_{I\setminus J}$ and $x_{J\setminus I}$ are independent, this equals
$$\mathbb{E}_{x_{I\cap J}}\!\Big[\,\mathbb{E}_{x_{I\setminus J}}[f(x_{I\cap J}, x_{I\setminus J})]\cdot \mathbb{E}_{x_{J\setminus I}}[g(x_{I\cap J}, x_{J\setminus I})]\Big].$$
But $\mathbb{E}_{x_{I\setminus J}}[f(x_{I\cap J}, x_{I\setminus J})] = f^{\subseteq I\cap J}(x_{I\cap J})$ and similarly for $g$, so the expression equals $\langle f^{\subseteq I\cap J}, g^{\subseteq I\cap J}\rangle$. $\square$

<a id="pdf-50833afe7403-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
**Theorem 8.35.** Let $f \in L^2(\Omega^n, \pi^{\otimes n})$. Then $f$ has a unique decomposition $f = \sum_{S \subseteq [n]} f^{=S}$ with $f^{=S} \in L^2(\Omega^n, \pi^{\otimes n})$ satisfying:

1. $f^{=S}$ depends only on the coordinates in $S$.
2. If $T \subsetneq S$ and $g \in L^2(\Omega^n,\pi^{\otimes n})$ depends only on the coordinates in $T$, then $\langle f^{=S}, g\rangle = 0$.

Additional properties:

3. Condition (2) also holds whenever $S \not\subseteq T$.
4. The decomposition is orthogonal: $\langle f^{=S}, f^{=T}\rangle = 0$ for $S \neq T$.
5. $f^{\subseteq T} = \sum_{S \subseteq T} f^{=S}$.
6. For each $S \subseteq [n]$, the mapping $f \mapsto f^{=S}$ is a linear operator.

<a id="pdf-50833afe7403-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.92 -->
**Proof.** We first show the existence of a decomposition satisfying (1)–(6); uniqueness (for (1) and (2)) is shown afterward. For each $S \subseteq [n]$ define
$$f^{=S} = \sum_{J \subseteq S} (-1)^{|S| - |J|}\, f^{\subseteq J},$$
with $f^{\subseteq J}$ as in Definition 8.17. Condition (1) holds since each $f^{\subseteq J}$ depends only on the coordinates in $J$; (5) holds by inclusion–exclusion (Exercise 8.14); (6) holds since each $f \mapsto f^{\subseteq J}$ is linear.

_Verify (2):_ Assume $T \subsetneq S$ and $g$ depends only on the coordinates in $T$. Then
$$\langle f^{=S}, g\rangle = \sum_{J \subseteq S} (-1)^{|S|-|J|}\,\langle f^{\subseteq J}, g\rangle. \tag{8.3}$$
Take any $i \in S \setminus T$ and pair the summands as $J', J'' = J' \cup \{i\}$ (with $i \notin J'$). By Lemma 8.34,
$$\langle f^{\subseteq J''}, g\rangle = \langle f^{\subseteq J''\cap T}, g^{\subseteq T}\rangle = \langle f^{\subseteq J'\cap T}, g^{\subseteq T}\rangle,$$
the latter equality using $i \notin T$. Since the signs $(-1)^{|S|-|J'|}$ and $(-1)^{|S|-|J''|}$ are opposite, the summands cancel in pairs, so the sum is $0$, confirming (2).

Existence is completed by $(2) \Rightarrow (3) \Rightarrow (4)$ (assuming (1)): the first because $\langle f^{=S}, g\rangle = \langle f^{=S}, g^{\subseteq S\cap T}\rangle$ when $g$ depends only on the coordinates in $T$ (Lemma 8.34), and $S \cap T \subsetneq S$ when $S \not\subseteq T$; the second because $S \neq T$ implies either $S \not\subseteq T$ or $T \not\subseteq S$.

<a id="pdf-50833afe7403-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.86 -->
**Proof (uniqueness, cont.).** To finish uniqueness in Theorem 8.35: if $f$ has two representations satisfying (1) and (2), subtract them to get a decomposition of the $0$ function satisfying (1),(2); the goal is that each piece is $0$. Any decomposition satisfying (1),(2) also satisfies Parseval's theorem $\langle f,f\rangle=\sum_{S\subseteq[n]}\|f_{=S}\|_2^2$, an easy consequence of (4), itself a consequence of (1),(2).

<a id="pdf-50833afe7403-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.93 -->
**Proposition 8.36.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ have orthogonal decomposition $f=\sum_{S\subseteq[n]}f^{=S}$. Fix any Fourier basis $\phi_0,\dots,\phi_{m-1}$ for $L^2(\Omega,\pi)$. Then
$$f^{=S}=\sum_{\substack{\alpha\in\mathbb{N}^n_{<m}\\ \mathrm{supp}(\alpha)=S}}\widehat f(\alpha)\,\phi_\alpha.\tag{8.4}$$

<a id="pdf-50833afe7403-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
**Proof.** Follows from the uniqueness part of Theorem 8.35. Taking (8.4) as the definition of $f_{=S}$, it is immediate that $f=\sum_S f_{=S}$ and that $f_{=S}$ depends only on the coordinates in $S$. If $g$ depends only on coordinates $T\subsetneq S$, then $f_{=S}$ and $g$ have disjoint Fourier support (Corollary 8.20), hence $\langle f_{=S},g\rangle=0$ by Plancherel (Proposition 8.16). $\square$

<a id="pdf-50833afe7403-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->
**Example 8.37.** Orthogonal decomposition of $f:\{a,b,c\}^2\to\{0,1\}$ from Example 8.15 (uniform $\{a,b,c\}$, $f(x_1,x_2)=1$ iff $x_1=x_2=c$). First, $f^{=\emptyset}=\mathbb{E}[f]=\tfrac19$. Next, for $i=1,2$, $f^{\subseteq\{i\}}(x)=\tfrac13$ if $x_i=c$ and $0$ otherwise, so $f^{=\{i\}}(x_1,x_2)=+\tfrac29$ if $x_i=c$ and $-\tfrac19$ else. Finally, computing $f^{=\{1,2\}}$ as $f-f^{=\emptyset}-f^{=\{1\}}-f^{=\{2\}}$: $f^{=\{1,2\}}(x_1,x_2)=+\tfrac49$ if $x_1=x_2=c$, $-\tfrac29$ if exactly one of $x_1,x_2$ is $c$, and $+\tfrac19$ if $x_1,x_2\neq c$. Consistent with Proposition 8.36 and the Fourier expansion from Example 8.15 (Exercise 8.20).

<a id="pdf-50833afe7403-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.82 -->
The Section 8.2 Fourier formulas restated via the orthogonal decomposition, e.g. $\langle f,g\rangle=\sum_{S\subseteq[n]}\langle f_{=S},g_{=S}\rangle$, $\mathrm{Inf}_i[f]=\sum_{S\ni i}\|f_{=S}\|_2^2$, and $T_\rho f=\sum_{S}\rho^{|S|}f_{=S}$.

<a id="pdf-50833afe7403-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.88 -->
These formulas follow via Proposition 8.36 or directly from Theorem 8.35 (Exercise 8.18); the decomposition stratifies $f$ by degree.

**Definition 8.38.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$ and $k\in\mathbb{N}$: degree-$k$ part $f^{=k}=\sum_{|S|=k}f_{=S}$; weight at degree $k$ $W_k[f]=\sum_{|S|=k}\|f_{=S}\|_2^2=\|f^{=k}\|_2^2$. Also $f^{\le k}=\sum_{|S|\le k}f_{=S}$ and $W_{>k}[f]=\sum_{|S|>k}\|f_{=S}\|_2^2$.

<a id="pdf-50833afe7403-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->
**8.4. $p$-biased analysis**

<a id="pdf-50833afe7403-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
The $p$-biased hypercube: a random input in $\{-1,1\}^n$ has each bit independently equal to $-1$ (True) with probability $p\in(0,1)$ and $+1$ (False) with probability $q=1-p$; i.e. $L^2(\Omega^n,\pi_p^{\otimes n})$ with $\Omega=\{-1,1\}$ and $\pi_p(-1)=p$, $\pi_p(1)=q$, and $\mu=\mathbb{E}_{x_i\sim\pi_p}[x_i]=q-p=1-2p$. (Coordinate-dependent $p_i$: Exercise 8.24.) A fixed combinatorial $f:\{-1,1\}^n\to\{-1,1\}$ is studied as $p$ varies; abbreviations $\Pr_{\pi_p}[\cdot]$ and $\mathbb{E}_{\pi_p}[\cdot]$ are used.

<a id="pdf-50833afe7403-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.95 -->
**Definition 8.39.** Since $|\Omega|=2$ there is a unique Fourier basis $\{\phi_0,\phi_1\}$ up to negating $\phi_1$; write $\phi=\phi_1$. Define $\phi:\{-1,1\}\to\mathbb{R}$ by $\phi(x_i)=\dfrac{x_i-\mu}{\sigma}$, where $\mu=\mathbb{E}_{x_i\sim\pi_p}[x_i]=q-p=1-2p$ and $\sigma=\mathrm{stddev}_{x_i\sim\pi_p}[x_i]=\sqrt{4pq}=2\sqrt{p}\sqrt{1-p}$. Note $\sigma^2=1-\mu^2$; also $\phi(1)=\sqrt{p/q}$, $\phi(-1)=-\sqrt{q/p}$.

<a id="pdf-50833afe7403-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.90 -->
The notation $\mu,\sigma$ is used throughout the section. $\{1,\phi\}$ is a Fourier basis for $L^2(\{-1,1\},\pi_p)$ because $\mathbb{E}[\phi(x_i)]=0$ and $\mathbb{E}[\phi(x_i)^2]=1$ by design.

<a id="pdf-50833afe7403-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.85 -->
**Definition 8.40.** In $L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ define the product Fourier basis $\phi_S(x)=\prod_{i\in S}\phi(x_i)$ for $S\subseteq[n]$, with coefficient $\hat f(S)=\mathbb{E}_{x\sim\pi_p^{\otimes n}}[f(x)\phi_S(x)]$ and biased Fourier expansion $f(x)=\sum_{S\subseteq[n]}\hat f(S)\phi_S(x)$. Caution: in general $\phi_S\phi_T\neq\phi_{S\triangle T}$.

<a id="pdf-50833afe7403-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.90 -->
**Example 8.41.** For the $i$th dictator $\chi_i(x)=x_i$ under $\pi_p$: from $\phi(x_i)=(x_i-\mu)/\sigma$ we get $x_i=\mu+\sigma\phi(x_i)$, which is its biased Fourier expansion. Hence $\hat{\chi_i}(\emptyset)=\mu$, $\hat{\chi_i}(\{i\})=\sigma$, and $\hat{\chi_i}(S)=0$ otherwise.

<a id="pdf-50833afe7403-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.90 -->
Link between the usual and biased Fourier expansions (Exercise 8.25); writing $\phi_i=\phi(x_i)$:
$$x_i=\mu+\sigma\phi_i\iff\phi_i=\frac{x_i-\mu}{\sigma}.\tag{8.5}$$
One converts a usual expansion to the biased one by substituting the latter.

<a id="pdf-50833afe7403-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.88 -->
**Example 8.42.** The selection function $\mathrm{Sel}:\{-1,1\}^3\to\{-1,1\}$ (Exercise 1.1(j)) outputs $x_2$ if $x_1=-1$ and $x_3$ if $x_1=1$; its usual Fourier expansion is $\mathrm{Sel}=\tfrac12 x_2+\tfrac12 x_3-\tfrac12 x_1x_2+\tfrac12 x_1x_3$. Substituting (8.5):
$$\mathrm{Sel}=\mu+(\tfrac12-\tfrac12\mu)\sigma\phi_2+(\tfrac12+\tfrac12\mu)\sigma\phi_3-\tfrac12\sigma^2\phi_1\phi_2+\tfrac12\sigma^2\phi_1\phi_3.\tag{8.6}$$

<a id="pdf-50833afe7403-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->
**Example (biased selection function).** For $\mathrm{Sel}^{(p)}\in L^2(\{-1,1\}^3,\pi_p^{\otimes 3})$, the nonzero $p$-biased Fourier coefficients are: $\widehat{\mathrm{Sel}^{(p)}}(\emptyset)=\mu$, $\widehat{\mathrm{Sel}^{(p)}}(2)=(\tfrac12-\tfrac12\mu)\sigma$, $\widehat{\mathrm{Sel}^{(p)}}(3)=(\tfrac12+\tfrac12\mu)\sigma$, $\widehat{\mathrm{Sel}^{(p)}}(\{1,2\})=-\tfrac12\sigma^2$, $\widehat{\mathrm{Sel}^{(p)}}(\{1,3\})=\tfrac12\sigma^2$, and $\widehat{\mathrm{Sel}^{(p)}}(S)=0$ for all other $S$. By the Fourier formulas of Section 8.2 one deduces e.g. $\mathbb{E}[\mathrm{Sel}^{(p)}]=\mu$ and $\mathrm{Inf}_1[\mathrm{Sel}^{(p)}]=(-\tfrac12\sigma^2)^2+(\tfrac12\sigma^2)^2=\tfrac12\sigma^4$.

<a id="pdf-50833afe7403-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.95 -->
**Notation 8.43.** For f : {−1,1}ⁿ → ℝ and p ∈ (0,1), write f^(p) for f viewed as an element of L²({−1,1}ⁿ, π_p^⊗n).

<a id="pdf-50833afe7403-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.85 -->
**Derivative operators (motivation).** Seeking an operator D_i on L²({−1,1}ⁿ, π_p^⊗n) acting like differentiation on the biased Fourier expansion; e.g. from (8.6), D₃Sel(p) = (½ + ½µ)σ + ½σ²φ₁. Using the relation (8.5) xᵢ = µ + σφᵢ and basic calculus, ∂/∂φᵢ = (∂xᵢ/∂φᵢ)·(∂/∂xᵢ) = σ · ∂/∂xᵢ, where ∂/∂xᵢ is the usual ith derivative operator.

<a id="pdf-50833afe7403-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.90 -->
**Definition 8.44.** For i ∈ [n], the ith (discrete) derivative operator D_i on L²({−1,1}ⁿ, π_p^⊗n) is defined by D_i f(x) = σ · [ f(x^{(i↦1)}) − f(x^{(i↦−1)}) ] / 2. This defines a different operator for each value of p, and is also written Dφᵢ = σ · Dxᵢ.

<a id="pdf-50833afe7403-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.90 -->
**Formula (8.7).** With respect to the biased Fourier expansion of f ∈ L²({−1,1}ⁿ, π_p^⊗n), the operator D_i satisfies D_i f = Σ_{S ∋ i} \hat f(S) φ_{S∖{i}}. This enables further influence formulas, generalizing Proposition 2.21.

<a id="pdf-50833afe7403-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.92 -->
**Proposition 8.45.** Suppose f ∈ L²({−1,1}ⁿ, π_p^⊗n) is Boolean-valued (range {−1,1}). Then for each i ∈ [n], Infᵢ[f] = σ² · Pr_{x∼π_p^n}[ f(x) ≠ f(x^{⊕i}) ], and I[f] = σ² · E_{x∼π_p^n}[ sens_f(x) ]. If furthermore f is monotone, then Infᵢ[f] = σ · \hat f(i).

<a id="pdf-50833afe7403-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.90 -->
**Proof.** Infᵢ[f] = E_{πp}[(Dφᵢ f)²] = σ² E_{πp}[(Dxᵢ f)²]. Since (Dxᵢ f)² is the 0–1 indicator that i is pivotal for f, the first formula follows; summing over i gives the second. When f is monotone, (Dxᵢ f)² = Dxᵢ f, hence Infᵢ[f] = σ² E_{πp}[Dxᵢ f] = σ E_{πp}[Dφᵢ f] = σ \hat f(i). ∎

<a id="pdf-50833afe7403-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.90 -->
**Definition 8.46.** A graph G on v ≥ 2 vertices is identified with the string in {True,False}^{(v choose 2)} indicating which edges are present (True) or absent (False). G(v,p) denotes the distribution {True,False}^{(v choose 2)} under π_p^⊗(v choose 2) — the Erdős–Rényi random graph model. Permuting the v vertices induces a permutation on the (v choose 2) edges. A (v-vertex) graph property is a Boolean function f : {True,False}^{(v choose 2)} → {True,False} invariant under all v! such vertex permutations ("does not depend on the names of the vertices").

<a id="pdf-50833afe7403-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.95 -->
Graph properties are always transitive-symmetric functions in the sense of Definition 2.10.

<a id="pdf-50833afe7403-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.88 -->
**Example 8.47.** v-vertex graph properties: Conn(G) = True iff G is connected; 3Col(G) = True iff G is 3-colorable; Clique_k(G) = True iff G contains a clique on at least k vertices; Maj_n(G) = True (assuming n = (v choose 2) is odd) iff G has at least (v choose 2)/2 edges; χ_[n](G) = True iff G has an odd number of edges. Each defines a family of Boolean functions, one per v.

<a id="pdf-50833afe7403-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.85 -->
A non-example graph property: f(G) = True iff vertex #1 has at least one neighbor (not permutation-invariant). Monotone graph properties are those for which adding edges never turns True into False; Conn, Clique_k, Maj_n, and 3Col are monotone. Typical question: how does Pr_{G∼G(v,p)}[Conn(G) = True] vary as p increases from 0 to 1? More generally, for any non-constant monotone f : {True,False}ⁿ → {True,False}, Pr_{πp}[f(x) = True] increases from 0 to 1 as p increases from 0 to 1.

<a id="pdf-50833afe7403-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.90 -->
**Figure 8.1.** Plot of Pr_{πp}[f(x) = True] versus p for f a dictator (dotted), AND₂ (dashed), and Maj₁₀₁ (solid).

<a id="pdf-50833afe7403-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.90 -->
**Margulis–Russo Formula.** Let f : {−1,1}ⁿ → ℝ. Using Notation 8.43 and the relation µ = 1 − 2p, d/dµ E[f^(p)] = (1/σ) · Σ_{i=1}^{n} \hat{f^(p)}(i).  (8.8)

<a id="pdf-50833afe7403-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.83 -->
**Margulis–Russo Formula (monotone case), eq. (8.9).** If $f:\{-1,1\}^n\to\{-1,1\}$ is monotone, then
$$\frac{d}{dp}\,\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=-1]=\frac{d}{d\mu}\,\mathbf{E}[f^{(p)}]=\frac{1}{\sigma^2}\,\mathbf{I}[f^{(p)}].$$

<a id="pdf-50833afe7403-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.93 -->
**Proof.** Treating $f$ as a multilinear polynomial in $x_1,\dots,x_n$, $\mathbb{E}[f^{(p)}]=\mathrm{T}_\mu f(1,\dots,1)=f(\mu,\dots,\mu)$ (also from Exercise 1.4). By calculus, $\frac{d}{d\mu}f(\mu,\dots,\mu)=\sum_{i=1}^n \mathrm{D}_{x_i}f(\mu,\dots,\mu)$, and
$$\mathrm{D}_{x_i}f(\mu,\dots,\mu)=\mathbb{E}[\mathrm{D}_{x_i}f^{(p)}]=\tfrac{1}{\sigma}\mathbb{E}[\mathrm{D}_{\phi_i}f^{(p)}]=\tfrac{1}{\sigma}\widehat{f^{(p)}}(i),$$
giving (8.8). For (8.9): the second equality follows from Proposition 8.45; the first holds because $\mu=1-2p$ and $\mathbb{E}[f]=1-2\Pr[f=-1]$, so the two factors of $-2$ cancel. $\square$

<a id="pdf-50833afe7403-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.92 -->
**Remark 8.48.** For nonconstant monotone $f:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$, the Margulis–Russo Formula implies $\Pr_{\pi_p}[f(x)=\text{True}]$ is a strictly increasing function of $p$, since $\mathbf{I}[f^{(p)}]>0$ always.

<a id="pdf-50833afe7403-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.85 -->
The plot for $\mathrm{Maj}_{101}$ resembles a step function jumping from $\approx0$ to $\approx1$ near the critical value $p=1/2$; this sharp threshold sharpens as $n$ grows. Margulis–Russo explains it: the derivative at $p=1/2$ equals the uniform total influence $\mathbf{I}[\mathrm{Maj}_n]=\Theta(\sqrt{n})$ (Theorem 2.33).

<a id="pdf-50833afe7403-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.80 -->
**Example 8.49.** (Exercise 8.23) For every $\varepsilon>0$ there is $C$ with $\Pr_{\pi_{1/2-C/\sqrt n}}[\mathrm{Maj}_n=\text{True}]\le\varepsilon$ and $\Pr_{\pi_{1/2+C/\sqrt n}}[\mathrm{Maj}_n=\text{True}]\ge 1-\varepsilon$. For the Erdős–Rényi model $G\sim\mathcal{G}(v,p)$:
$$\Pr[\mathrm{Clique}_{\log v}(G)=\text{True}]\to \begin{cases}0 & p<1/4\\ 1 & p>1/4,\end{cases}$$
$$\Pr[\mathrm{Conn}(G)=\text{True}]\to \begin{cases}0 & p<\tfrac{\ln v}{v}\left(1-\tfrac{\log\log v}{\log v}\right)\\ 1 & p>\tfrac{\ln v}{v}\left(1+\tfrac{\log\log v}{\log v}\right).\end{cases}$$

<a id="pdf-50833afe7403-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.88 -->
**Definition 8.50.** For monotone nonconstant $f:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$, the *critical probability* $p_c$ is the unique $p\in(0,1)$ with $\Pr_{x\sim\pi_p^{\otimes n}}[f(x)=\text{True}]=1/2$. Write $q_c=1-p_c$, $\mu_c=1-2p_c$, and $\sigma_c^2=4p_cq_c$. (Exercise 8.27: $p_c$ is well defined.)

<a id="pdf-50833afe7403-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.93 -->
For monotone nonconstant $f$, let $\Delta$ be the derivative of $\Pr_{\pi_p}[f(x)=\text{True}]$ at $p=p_c$; the jump from near $0$ to near $1$ occurs over an interval around $p_c$ of width $\approx 1/\Delta$. A sharp threshold means $1/\Delta$ is small even relative to $\min(p_c,q_c)$. Since Margulis–Russo gives $\Delta=\tfrac{1}{\sigma_c^2}\mathbf{I}[f^{(p_c)}]$ and $\min(p_c,q_c)$ is proportional to $4p_cq_c=\sigma_c^2$, $1/\Delta$ is small compared to $\min(p_c,q_c)$ iff $\mathbf{I}[f^{(p_c)}]$ is large.

<a id="pdf-50833afe7403-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.93 -->
**Sharp threshold principle.** Let $f:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$ be monotone. Then, roughly, $\Pr_{\pi_p}[f(x)=\text{True}]$ has a sharp threshold iff $f$ has large (superconstant) total influence under its critical probability distribution.

<a id="pdf-50833afe7403-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.78 -->
One may prove a sharp threshold by showing $\mathbf{I}[f^{(p_c)}]$ is not small, motivating the problem of characterizing $f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ with small $\mathbf{I}[f]$. Friedgut's Junta Theorem (Ch. 3.1, proved Ch. 9.6): in the uniform case $p=1/2$, small $\mathbf{I}[f]$ forces $f$ close to a junta. Hence any monotone graph property with $p_c=1/2$ has large derivative at $p_c$ (transitive-symmetric $\Rightarrow$ all coordinates equally influential, so not junta-like); this extends to $p$ bounded away from $0,1$ (Ch. 10.3). Many properties (e.g. connectivity) have $p_c$ near $0$, where characterizing small-$\mathbf{I}[f]$ functions is harder (Friedgut, Bourgain, Hatami; Ch. 10.5).

<a id="pdf-50833afe7403-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.82 -->
**§8.5. Abelian groups.** Beyond $|\Omega|=2$, explicit Fourier bases are often unhelpful when the only operation is equality (e.g. $f:\{\text{Red},\text{Green},\text{Blue}\}^n\to\mathbb{R}$ — work abstractly with the orthogonal decomposition). But if $\Omega$ is a finite abelian group $G$ (operation $+$, identity $0$) under the uniform distribution $\pi$, then $\pi$ is translation-invariant ($\pi(X)=\pi(t+X)$) and there is a natural canonical Fourier basis for $L^2(\Omega,\pi)$; complex-valued functions are allowed.

<a id="pdf-50833afe7403-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.90 -->
**Definition 8.51.** For a finite abelian group $G$ (operation $+$, identity $0$) and $n\in\mathbb{N}^+$, $L^2(G^n)$ is the complex inner product space of functions $f:G^n\to\mathbb{C}$ with $\langle f,g\rangle=\mathbf{E}_{x\sim G^n}[f(x)\overline{g(x)}]$, where $x\sim G^n$ means $x$ is uniform on $G^n$.

<a id="pdf-50833afe7403-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.92 -->
The real theory generalizes to the complex inner product; the main change is Plancherel's Theorem:
$$\langle f,g\rangle=\sum_{\alpha\in\mathbb{N}^n_{<m}}\widehat{f}(\alpha)\,\overline{\widehat{g}(\alpha)}=\sum_{S\subseteq[n]}\langle f^{=S},g^{=S}\rangle.$$
(Exercise 8.32.)

<a id="pdf-50833afe7403-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.85 -->
**Definition 8.52.** A *character* of a finite group $G$ is a homomorphism $\chi:G\to\mathbb{C}^\times$ (the nonzero complex numbers under multiplication), i.e. $\chi(x+y)=\chi(x)\chi(y)$. Since $G$ is finite there is $m\in\mathbb{N}^+$ with $0=x+\cdots+x$ ($m$ times) for each $x\in G$; then $\chi(0)=1$ and $\chi(x)^m=1$, so $|\chi(x)|=1$ and the range of $\chi$ lies in the $m$th roots of unity. Characters furnish a natural Fourier basis for $L^2(G)$.

<a id="pdf-50833afe7403-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.95 -->
**Fact 8.53.** If $\chi$ and $\phi$ are characters of $G$, then so are $\overline{\chi}$ and $\phi\cdot\chi$.

<a id="pdf-50833afe7403-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.97 -->
**Proposition 8.54.** Let $\chi$ be a character of $G$. Then either $\chi\equiv 1$ or $\mathbf{E}[\chi]=0$.

<a id="pdf-50833afe7403-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.96 -->
**Proof.** If $\chi\not\equiv 1$, pick $y\in G$ with $\chi(y)\neq 1$. Since $x+y$ is uniform on $G$ when $x\sim G$, $\mathbf{E}_{x\sim G}[\chi(x)]=\mathbf{E}_{x\sim G}[\chi(x+y)]=\mathbf{E}_{x\sim G}[\chi(x)\chi(y)]=\chi(y)\,\mathbf{E}_{x\sim G}[\chi(x)]$. As $\chi(y)\neq 1$, $\mathbf{E}[\chi(x)]=0$. $\square$

<a id="pdf-50833afe7403-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.95 -->
**Proposition 8.55.** The set of all characters of $G$ is orthonormal; consequently $G$ has at most $\dim(L^2(G))=|G|$ characters.

<a id="pdf-50833afe7403-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.93 -->
**Proof.** For a character $\chi$, $\mathbf{E}[|\chi|^2]=1$ since $|\chi|\equiv 1$, so $\langle\chi,\chi\rangle=1$. For a distinct character $\varphi$, $\langle\varphi,\chi\rangle=\mathbf{E}[\varphi\overline{\chi}]$; here $\varphi\overline{\chi}=\varphi/\chi$ is a character (Fact 8.53) using $\overline{\chi}=1/\chi$, and $\varphi/\chi\not\equiv 1$ since $\varphi\neq\chi$. Hence $\langle\varphi,\chi\rangle=\mathbf{E}[\varphi/\chi]=0$ by Proposition 8.54. $\square$

<a id="pdf-50833afe7403-p022-b006"></a>
<!-- pdf-source: page=22; block=6; confidence=0.90 -->
$G$ has exactly $|G|$ characters, so by Proposition 8.55 all characters (including the constant $1$) form a Fourier basis for $L^2(G)$. To verify $|G|$ distinct characters exist, start with the cyclic group $\mathbb{Z}_m$, where every character's range lies in the $m$th roots of unity.

<a id="pdf-50833afe7403-p022-b007"></a>
<!-- pdf-source: page=22; block=7; confidence=0.96 -->
**Definition 8.56.** Fix $m\geq 2$ and let $\omega=\exp(2\pi i/m)$. For $0\leq j<m$, define $\chi_j:\mathbb{Z}_m\to\mathbb{C}$ by $\chi_j(x)=\omega^{jx}$. These are distinct characters of $\mathbb{Z}_m$.

<a id="pdf-50833afe7403-p022-b008"></a>
<!-- pdf-source: page=22; block=8; confidence=0.92 -->
Thus $\chi_0\equiv 1,\chi_1,\dots,\chi_{m-1}$ form a Fourier basis for $L^2(\mathbb{Z}_m)$. By Proposition 8.13, a Fourier basis for $L^2(\mathbb{Z}_m^n)$ is obtained by taking all products of these functions.

<a id="pdf-50833afe7403-p022-b009"></a>
<!-- pdf-source: page=22; block=9; confidence=0.95 -->
**Definition 8.57.** For $n\in\mathbb{N}^+$ and $\alpha\in\mathbb{Z}_m^n$, define $\chi_\alpha:\mathbb{Z}_m^n\to\mathbb{C}$ by $\chi_\alpha(x)=\prod_{j=1}^{n}\chi_{\alpha_j}(x_j)$. These are all the characters of $\mathbb{Z}_m^n$ and form a Fourier basis of $L^2(\mathbb{Z}_m^n)$.

<a id="pdf-50833afe7403-p022-b010"></a>
<!-- pdf-source: page=22; block=10; confidence=0.90 -->
By the Fundamental Theorem of Finitely Generated Abelian Groups, any finite abelian $G$ is a direct product of cyclic groups of prime-power order; Exercise 8.35 asks to check that all characters of $G$ (hence a Fourier basis for $L^2(G)$) arise as products of the associated cyclic groups' characters.

<a id="pdf-50833afe7403-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.88 -->
Restricting attention mostly to groups $\mathbb{Z}_m^n$: the characters of Definition 8.56 satisfy (using $\omega^m=1$) $\chi_j\chi_{j'}=\chi_{j+j'\ (\mathrm{mod}\ m)}$ and $1/\chi_j=\chi_{-j\ (\mathrm{mod}\ m)}$, so they form a group under multiplication isomorphic to $\mathbb{Z}_m$, indexed by $\widehat{\mathbb{Z}}_m\cong\mathbb{Z}_m$. Generally the Fourier basis/characters of $L^2(\mathbb{Z}_m^n)$ are indexed by $\mathbb{Z}_m^n$ instead of multi-indices.

<a id="pdf-50833afe7403-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.95 -->
**Fact 8.58.** The characters $(\chi_\alpha)_{\alpha\in\mathbb{Z}_m^n}$ of $\mathbb{Z}_m^n$ form a group under multiplication: $\chi_\alpha\cdot\chi_\beta=\chi_{\alpha+\beta}$ and $1/\chi_\alpha=\chi_{-\alpha}$.

<a id="pdf-50833afe7403-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.85 -->
The distinguishing feature of $L^2(G)$ versus general $L^2(\Omega,\pi)$ is addition on the domain, making convolution central; the definition from $\mathbb{F}_2^n$ generalizes.

<a id="pdf-50833afe7403-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.96 -->
**Definition 8.59.** For $f,g\in L^2(G)$, their convolution $f*g\in L^2(G)$ is $(f*g)(x)=\mathbf{E}_{y\sim G}[f(y)g(x-y)]=\mathbf{E}_{y\sim G}[f(x-y)g(y)]$.

<a id="pdf-50833afe7403-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.88 -->
Exercise 8.36: convolution is associative and commutative, and the generalization of Theorem 1.27 holds:

<a id="pdf-50833afe7403-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.96 -->
**Theorem 8.60.** For $f,g\in L^2(G)$, $\widehat{f*g}(\alpha)=\hat{f}(\alpha)\,\hat{g}(\alpha)$.

<a id="pdf-50833afe7403-p023-b007"></a>
<!-- pdf-source: page=23; block=7; confidence=0.87 -->
On vector space domains: subgroups of $\mathbb{Z}_m^n$ arise naturally. When $\mathbb{Z}_m$ has only trivial subgroups $\{0\},\mathbb{Z}_m$ — equivalently $m=p$ is prime — every subgroup of $\mathbb{Z}_m^n$ is isomorphic to $\mathbb{Z}_m^{n_0}$, $n_0\leq n$. Then $\mathbb{Z}_p$ is a field, $\mathbb{Z}_p^n=\mathbb{F}_p^n$ an $n$-dimensional vector space with subgroups as subspaces; characters are indexed by $\widehat{\mathbb{F}_p^n}$, generalizing $p=2$. Notions of affine subspaces and restrictions from Chapters 3.2–3.3 generalize to $L^2(\mathbb{F}_p^n)$.

<a id="pdf-50833afe7403-p023-b008"></a>
<!-- pdf-source: page=23; block=8; confidence=0.99 -->
**8.6. Highlight: Randomized decision tree complexity**

<a id="pdf-50833afe7403-p023-b009"></a>
<!-- pdf-source: page=23; block=9; confidence=0.90 -->
A decision tree $T$ for $f:\{-1,1\}^n\to\{-1,1\}$ is a deterministic algorithm with adaptive query access to the bits of an unknown input string.

<a id="pdf-50833afe7403-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.92 -->
Given $x\in\{-1,1\}^n$, the tree outputs $f(x)$. Example for $f=\mathrm{Maj}_3$: query $x_1$, then $x_2$; if equal output that value, else query and output $x_3$. Worst-case input ($x_1\neq x_2$) costs $3$ queries. The cost of the worst-case input is the tree's depth.

<a id="pdf-50833afe7403-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.93 -->
Randomization helps: for $\mathrm{Maj}_3$, query two random distinct coordinates; if equal output that value, else query and output the third. Every input finishes in $2$ queries with probability $\geq 1/3$. Defining input cost as expected queries, worst-case cost is $(1/3)\cdot 2+(2/3)\cdot 3=8/3<3$.

<a id="pdf-50833afe7403-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.95 -->
**Definition 8.61.** For $f:\{-1,1\}^n\to\mathbb{R}$, a (zero-error) randomized decision tree $\mathbf{T}$ computing $f$ is a probability distribution over deterministic decision trees that compute $f$. Its cost on $x\in\{-1,1\}^n$ is the expected number of queries $T$ makes on $x$ when $T\sim\mathbf{T}$; the cost of $\mathbf{T}$ is the maximum cost over inputs. The (zero-error) randomized decision tree complexity $\mathrm{RDT}(f)$ is the minimum cost over randomized decision trees computing $f$.

<a id="pdf-50833afe7403-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.92 -->
Assuming random input gives further savings: for uniform $x\sim\{-1,1\}^3$, any deterministic decision tree for $\mathrm{Maj}_3$ makes $2$ queries with probability $1/2$ and $3$ with probability $1/2$, expected $5/2<8/3<3$.

<a id="pdf-50833afe7403-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.95 -->
**Definition 8.62.** For a randomized decision tree $\mathbf{T}$, define $\delta_i(\mathbf{T})=\Pr_{x\sim\{-1,1\}^n,\ T\sim\mathbf{T}}[T\text{ queries }x_i]$ and $\Delta(\mathbf{T})=\sum_{i=1}^n\delta_i(\mathbf{T})=\mathbf{E}_{x\sim\{-1,1\}^n,\ T\sim\mathbf{T}}[\#\text{ coordinates queried by }T\text{ on }x]$ (8.10). For $f:\{-1,1\}^n\to\mathbb{R}$, $\Delta(f)$ is the minimum of $\Delta(\mathbf{T})$ over randomized decision trees computing $f$.

<a id="pdf-50833afe7403-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.88 -->
These definitions generalize to $f\in L^2(\Omega,\pi^{\otimes n})$: a deterministic decision tree over domain $\Omega$ has each internal query node with $|\Omega|$ outgoing edges labeled by elements of $\Omega$; the generalizations are written $\delta_i^{(\pi)}(\mathbf{T})$, $\Delta^{(\pi)}(\mathbf{T})$, $\Delta^{(\pi)}(f)$.

<a id="pdf-50833afe7403-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.97 -->
**Section 8.6. Highlight: Randomized decision tree complexity.**

<a id="pdf-50833afe7403-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.92 -->
Notation: for the space $L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ the superscript $(p)$ is used in place of $(\pi_p)$. Directly from the definitions, for any $f\in L^2(\Omega^n,\pi^{\otimes n})$: $\Delta^{(\pi)}(f)\le \mathrm{RDT}(f)\le \mathrm{DT}(f)$.

<a id="pdf-50833afe7403-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.90 -->
**Remark 8.63.** In the definition of $\Delta^{(\pi)}(f)$ it suffices to allow only deterministic decision trees, since in the defining expression (8.10) one can always pick the best deterministic tree $T$ in the support of the random tree $\mathcal{T}$.

<a id="pdf-50833afe7403-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.90 -->
**Example 8.64.** $\mathrm{RDT}(\mathrm{Maj}_3)\le 8/3$ and $\Delta(\mathrm{Maj}_3)\le 5/2$, with both bounds actually equalities. For the recursive majority $\mathrm{Maj}_3^{\otimes d}$ on $n=3^d$ inputs (Exercise 8.38): $\mathrm{DT}(\mathrm{Maj}_3^{\otimes d})=3^d=n$; $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d})\le (8/3)^d=n^{\log_3(8/3)}\approx n^{0.89}$; $\Delta(\mathrm{Maj}_3^{\otimes d})\le (5/2)^d=n^{\log_3(5/2)}\approx n^{0.83}$. These bounds are not asymptotically sharp; estimating $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d})$ is a well-studied open problem.

<a id="pdf-50833afe7403-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.95 -->
**Example 8.65.** (Exercise 8.39) For the logical $\mathrm{OR}_n$ function, $\Delta^{(p)}(\mathrm{OR}_n)=\dfrac{1-(1-p)^n}{p}$, which is roughly $2$ for $p=1/2$ but is asymptotic to $n/(2\ln 2)$ at the critical probability $p_c$.

<a id="pdf-50833afe7403-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.85 -->
Example 8.64 shows that randomness allows evaluating certain unbiased $n$-bit functions while reading only a $1/n^{\Theta(1)}$ fraction of input bits, notably for transitive-symmetric $f$ like $\mathrm{Maj}_3^{\otimes d}$. Exercise 8.37: any randomized tree $T$ computing a transitive-symmetric $f$ can be converted to one with the same $\Delta(T)$ but all $\delta_i(T)=\Delta(f)/n$ equal, so each bit is queried with probability $1/n^{\Theta(1)}$.

<a id="pdf-50833afe7403-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=0.92 -->
**Yao's Conjecture [Yao77].** Let $f:\{-1,1\}^n\to\{-1,1\}$ be a nonconstant monotone $v$-vertex graph property, where $n=\binom{v}{2}$. Then $\mathrm{RDT}(f)\ge\Omega(n)$.

<a id="pdf-50833afe7403-p025-b008"></a>
<!-- pdf-source: page=25; block=8; confidence=0.90 -->
Toward Yao's conjecture the text presents a lower bound of O'Donnell, Saks, Schramm, Servedio [OSSS05] that applies to the broader class of transitive-symmetric functions and even lower-bounds $\Delta^{(p_c)}(f)$.

<a id="pdf-50833afe7403-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.93 -->
**Theorem 8.66.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be a nonconstant monotone transitive-symmetric function with critical probability $p_c$. Then $\Delta^{(p_c)}(f)\ge (n/\sigma_c)^{2/3}$.

<a id="pdf-50833afe7403-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.85 -->
Theorem 8.66 is essentially sharp in several cases. When $p_c=\Theta(1/n)$ or $1-\Theta(1/n)$, then $\sigma_c=\Theta(1/\sqrt{n})$ and the theorem gives the strongest possible bound $\Delta^{(p_c)}(f)\ge\Omega(n)$ (e.g. $\mathrm{OR}_n$, Example 8.65). It can be tight up to a logarithmic factor when $p_c=1/2$, per Theorem 8.67.

<a id="pdf-50833afe7403-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.90 -->
**Theorem 8.67 [BSW05].** There is an infinite family of monotone transitive-symmetric functions $f_n:\{-1,1\}^n\to\{-1,1\}$ with critical probability $p_c=1/2$ and $\Delta(f)\le O(n^{2/3}\log n)$.

<a id="pdf-50833afe7403-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.90 -->
Theorem 8.66 follows easily from two inequalities [OS06, OS07, OSSS05], presented next.

<a id="pdf-50833afe7403-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=0.95 -->
**OS Inequality.** Let $f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})$. Then $\sum_{i=1}^n\widehat{f}(i)\le\|f\|_2\cdot\sqrt{\Delta^{(p)}(f)}$. In particular, if $f$ has range $\{-1,1\}$ and is monotone, then $\mathrm{I}[f]\le\sigma\sqrt{\Delta^{(p)}(f)}$.

<a id="pdf-50833afe7403-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=0.92 -->
**OSSS Inequality.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ have range $\{-1,1\}$ and let $T$ be any randomized decision tree computing $f$. Then $\mathrm{Var}[f]\le\sum_{i=1}^n \delta_i^{(\pi)}(T)\cdot\mathrm{Inf}_i[f]$.

<a id="pdf-50833afe7403-p026-b007"></a>
<!-- pdf-source: page=26; block=7; confidence=0.90 -->
**Remark 8.68.** Corollary of OSSS: $\mathrm{MaxInf}[f]\ge \mathrm{Var}[f]/\Delta^{(\pi)}(f)\ge \mathrm{Var}[f]/\mathrm{DT}(f)\ge \mathrm{Var}[f]/\deg(f)^3$, the last inequality assuming $\Omega=\{-1,1\}$. See Exercise 8.44.

<a id="pdf-50833afe7403-p026-b008"></a>
<!-- pdf-source: page=26; block=8; confidence=0.88 -->
Both inequalities strengthen basic Fourier inequalities by accounting for decision-tree complexity: the OS Inequality generalizes the fact that majority maximizes $\sum_{i=1}^n|\hat f(i)|$ (Theorem 2.33); the OSSS Inequality generalizes the Poincaré Inequality, discounting influences of rarely-read coordinates.

<a id="pdf-50833afe7403-p026-b009"></a>
<!-- pdf-source: page=26; block=9; confidence=0.87 -->
**Proof of Theorem 8.66.** Regard $f\in L^2(\{-1,1\}^n,\pi_{p_c}^{\otimes n})$ and let $T$ achieve $\Delta^{(p_c)}(f)$. In the OSSS Inequality, $\mathrm{Var}[f]=1$ (since $p_c$ is critical) and $\mathrm{Inf}_i[f]=I[f]/n$ for each $i\in[n]$ (transitive-symmetric). [continues p.27]

<a id="pdf-50833afe7403-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.82 -->
**Proof (cont.).** Thus $\sum_{i=1}^n\delta_i^{(p_c)}(T)\cdot\frac{I[f]}{n}\le 1$, i.e. $n\le I[f]\cdot\Delta^{(p_c)}(f)$. Applying the OS Inequality gives $n\le \sigma\,\Delta^{(p_c)}(f)^{3/2}$; rearranging yields $\Delta^{(p_c)}(f)\ge(n/\sigma)^{2/3}$. $\square$

<a id="pdf-50833afe7403-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.90 -->
**Lemma 8.69.** Let $f,g\in L^2(\Omega^n,\pi^{\otimes n})$ and $j\in[n]$. For $\omega\in\Omega$ write $f_{|\omega}$ for the restriction fixing coordinate $j$ to $\omega$ (similarly $g_{|\omega}$). Then $\mathrm{Cov}[f,g]=\mathbb{E}_{\omega,\omega'\sim\pi\ \text{indep}}\big[\mathrm{Cov}[f_{|\omega},g_{|\omega'}]\big]+\langle L_j f, L_j g\rangle$.

<a id="pdf-50833afe7403-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.88 -->
**Proof.** Covariances and Laplacians are unchanged by adding constants, so assume $\mathbb{E}[f]=\mathbb{E}[g]=0$; then $\mathrm{Cov}[f,g]=\langle f,g\rangle$. Compute $\mathbb{E}_{\omega,\omega'}[\mathrm{Cov}[f_{|\omega},g_{|\omega'}]]=\mathbb{E}_{\omega,\omega'}[\langle f_{|\omega},g_{|\omega'}\rangle-\mathbb{E}[f_{|\omega}]\mathbb{E}[g_{|\omega'}]]=\mathbb{E}_{\omega,\omega'}[\langle f_{|\omega},g_{|\omega'}\rangle]=\langle E_j f,E_j g\rangle$. The claim then reduces to the identity $\langle f,g\rangle=\langle E_j f,E_j g\rangle+\langle L_j f,L_j g\rangle$ (Exercise 8.8). $\square$

<a id="pdf-50833afe7403-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.85 -->
**Proof of the OSSS Inequality.** More generally, for $g:\{-1,1\}^n\to\{-1,1\}$ in $L^2(\Omega^n,\pi^{\otimes n})$: $\mathrm{Cov}[f,g]\le\sum_{i=1}^n\delta_i^{(\pi)}(T)\cdot\mathrm{Inf}_i[g]$ (8.11); the result follows by taking $g=f$. May assume $T$ is a single deterministic tree computing $f$, since (8.11) is linear in the $\delta_i^{(\pi)}(T)$. Prove (8.11) by induction on the structure of $T$. If $T$ is depth-0, $f$ is constant, $\mathrm{Cov}[f,g]=0$ and (8.11) is trivial. Otherwise let $j\in[n]$ be the coordinate queried at the root; for $\omega\in\Omega$ let $T_\omega$ be the $\omega$-labeled child subtree, and apply Lemma 8.69 with induction (noting $T_\omega$ computes the corresponding restriction). [continues beyond supplied pages]

<a id="pdf-50833afe7403-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.90 -->
**Proof (continued).** Writing the covariance over independent draws $\omega,\omega'\sim\pi$ (with $f_{|\omega}$ the restricted function) and expanding via the $\mathrm{L}_j$ decomposition:
$$\mathrm{Cov}[f,g]=\mathbb{E}_{\omega,\omega'\sim\pi}[\mathrm{Cov}[f_{|\omega},g_{|\omega'}]]+\langle \mathrm{L}_jf,\mathrm{L}_jg\rangle$$
$$\le\mathbb{E}_{\omega,\omega'\sim\pi}\Big[\sum_{i\neq j}\delta_i^{(\pi)}(T_\omega)\cdot\mathrm{Inf}_i[g_{\omega'}]\Big]+\langle \mathrm{L}_jf,\mathrm{L}_jg\rangle$$
$$=\sum_{i\neq j}\delta_i^{(\pi)}(T)\cdot\mathrm{Inf}_i[g]+\langle f,\mathrm{L}_jg\rangle\quad(\text{in part since }\mathbb{E}[\mathrm{L}_jg]=0)$$
$$\le\sum_{i\neq j}\delta_i^{(\pi)}(T)\cdot\mathrm{Inf}_i[g]+\mathbb{E}[|\mathrm{L}_jg|]\quad(\text{since }|f|\le1)$$
$$=\sum_{i=1}^n\delta_i^{(\pi)}(T)\cdot\mathrm{Inf}_i[g],$$
where the last step used $\delta_j^{(\pi)}(T)=1$ and Proposition 8.24. This completes the inductive proof of (8.11).

<a id="pdf-50833afe7403-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.90 -->
**Definition 8.70.** Let (Ω, π) be a finite probability space and T a deterministic decision tree over Ω. The *decision tree process* associated to T generates a random string x ∼ π (with auxiliary variables) as follows:

(1) Start at the root of T, querying coordinate j₁; draw x_{j₁} ∼ π and follow the edge labeled by the outcome.

(2) At the node then reached, querying coordinate j₂, draw x_{j₂} ∼ π and follow the outcome edge.

(3) Repeat until a leaf is reached; set J = {j₁, j₂, j₃, …} ⊆ [n] to be the queried coordinates.

(4) Draw the unqueried coordinates x_{J̄} from π^{⊗J̄}.

Although coordinates are drawn in a random, dependent order, the final string x = (x_J, x_{J̄}) is distributed according to the product distribution π^{⊗n} (Exercise 8.42).

<a id="pdf-50833afe7403-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.93 -->
**Proof of the OS Inequality.** It suffices to prove $\sum_{i=1}^n \widehat{f}(i)\le\|f\|_2\cdot\sqrt{\Delta^{(p)}(f)}$; the "in particular" statement then follows from Proposition 8.45. Fix a deterministic decision tree $T$ achieving $\Delta^{(p)}(f)$ (Remark 8.63) and let $x=(x_J,x_{\bar J})$ be drawn from the associated decision tree process. Using the notation $\phi$ from Definition 8.39,
$$\sum_{i=1}^n \widehat{f}(i)=\mathbb{E}_{J,x_J,x_{\bar J}}\Big[f(x)\sum_{i=1}^n\phi(x_i)\Big]=\mathbb{E}_{J,x_J}\Big[f(x_J)\,\mathbb{E}_{x_{\bar J}}\Big[\sum_{i=1}^n\phi(x_i)\Big]\Big].$$

<a id="pdf-50833afe7403-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.85 -->
**Proof (continued).** Since f(x_J) is determined once x_J is fixed and E[φ(x_i)] = 0 for i ∉ J,

Σ_i f̂(i) = E_{J, x_J}[ f(x_J)·Σ_{i=1}^n 1{i∈J}·φ(x_i) ] ≤ √(E_{J,x_J}[f(x_J)²]) · √(E_{J,x_J}[(Σ_{i=1}^n 1{i∈J}·φ(x_i))²])

by Cauchy–Schwarz. Here E_{J,x_J}[f(x_J)²] = ‖f‖₂² since T computes f. It remains to show E_{J,x_J}[(Σ_i 1{i∈J}φ(x_i))²] = Δ^{(p)}(f). Expanding the square:

E[(Σ_i 1{i∈J}φ(x_i))²] = Σ_{i=1}^n E[1{i∈J}·φ(x_i)²] + Σ_{i≠i'} E[1{i,i'∈J}·φ(x_i)φ(x_{i'})].

Conditioned on i ∈ J, E[φ(x_i)²] = 1, so the diagonal sum equals Σ_{i=1}^n Pr[i∈J] = Δ^{(p)}(f). For a cross term, condition on i, i' ∈ J with i queried before i'; then x_{i'} still has conditional distribution π_p, so E[φ(x_{i'})] = 0 (and symmetrically if i' is queried first). Hence every E[1{i,i'∈J}φ(x_i)φ(x_{i'})] = 0, completing the proof.

<a id="pdf-50833afe7403-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.98 -->
**§8.7. Exercises and notes.**

<a id="pdf-50833afe7403-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.92 -->
**Exercise 8.1.** Generalize the definitions and results of Sections 8.1 and 8.2 to general finite product spaces L²(Ω₁ × ⋯ × Ω_n, π₁ ⊗ ⋯ ⊗ π_n).

<a id="pdf-50833afe7403-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.92 -->
**Exercise 8.2.** Verify that Definition 8.1 defines a real inner product space. (Where is the full support of π used?)

<a id="pdf-50833afe7403-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=0.92 -->
**Exercise 8.3.** Verify the formula for f̂(α) in Definition 8.14.

<a id="pdf-50833afe7403-p029-b006"></a>
<!-- pdf-source: page=29; block=6; confidence=0.92 -->
**Exercise 8.4.** Verify that φ₀, φ₁, φ₂ from Example 8.10 constitute a Fourier basis for Ω = {a, b, c} with the uniform distribution.

<a id="pdf-50833afe7403-p029-b007"></a>
<!-- pdf-source: page=29; block=7; confidence=0.92 -->
**Exercise 8.5.** Verify the Fourier expansion in Example 8.15.

<a id="pdf-50833afe7403-p029-b008"></a>
<!-- pdf-source: page=29; block=8; confidence=0.92 -->
**Exercise 8.6.** Complete the proof of Proposition 8.16.

<a id="pdf-50833afe7403-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.90 -->
**Exercise 8.7.** Prove that the expectation-over-I operator E_I is a linear operator on L²(Ωⁿ, π^{⊗n}), is self-adjoint (⟨E_I f, g⟩ = ⟨f, E_I g⟩), and is a projection (E_I ∘ E_I = E_I). Deduce that T_ρ is also self-adjoint.

<a id="pdf-50833afe7403-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.90 -->
**Exercise 8.8.** Show that for any f, g ∈ L²(Ωⁿ, π^{⊗n}) and j ∈ [n]: ⟨f, g⟩ = ⟨E_j f, E_j g⟩ + ⟨L_j f, L_j g⟩.

<a id="pdf-50833afe7403-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.90 -->
**Exercise 8.9.** Prove Proposition 8.24. (Hint: Exercise 1.17.)

<a id="pdf-50833afe7403-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.95 -->
**Exercise 8.10.** Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ have range $\{-1, 1\}$. Proposition 8.24 tells us that $\|\mathrm{L}_i f\|_1 = \|\mathrm{L}_i f\|_2^2 = \mathrm{Inf}_i[f]$. (a) Show that $\|\mathrm{L}_i f\|_p^p \le 2^p\,\mathrm{Inf}_i[f]$ for any $p \ge 1$. (b) In case $1 \le p \le 2$, show that in fact $\|\mathrm{L}_i f\|_p^p \le \mathrm{Inf}_i[f]$. (Hint: use the general form of Hölder's inequality to bound $\|\mathrm{L}_i f\|_p$ in terms of $\|\mathrm{L}_i f\|_1$ and $\|\mathrm{L}_i f\|_2$.)

<a id="pdf-50833afe7403-p030-b005"></a>
<!-- pdf-source: page=30; block=5; confidence=0.90 -->
**Exercise 8.11.** Generalize all of Exercise 2.35 to the setting of L²(Ωⁿ, π^{⊗n}). Caution: the two statements referring to ρ ∈ [−1, 1] should refer only to ρ ∈ [0, 1] in this more general setting.

<a id="pdf-50833afe7403-p030-b006"></a>
<!-- pdf-source: page=30; block=6; confidence=0.88 -->
**Exercise 8.12.** Assume |Ω| = m and let π be uniform on Ω. (a) For x ∈ Ωⁿ and y ∼ N_ρ(x), give a formula for Pr[y_i = ω] in terms of ρ (two cases, according to whether x_i = ω). (b) Verify the formula is a valid probability distribution on Ω even when −1/(m−1) ≤ ρ < 0, extending the definition of N_ρ to this range (cf. second half of Definition 2.40). (c) Verify that for x ∼ π^{⊗n} and y ∼ N_ρ(x), the distribution of (x, y) is symmetric in x and y. (d) Show that when y ∼ N_{−1/(m−1)}(x), each y_i is uniform on Ω \ {x_i}. (e) Verify the formula for T_ρ from Proposition 8.28 still holds for −1/(m−1) ≤ ρ < 0 (Hint: it holds for ρ ∈ [0, 1] and the part-(a) formula is a polynomial in ρ).

<a id="pdf-50833afe7403-p030-b007"></a>
<!-- pdf-source: page=30; block=7; confidence=0.90 -->
**Exercise 8.13.** Show that Definition 8.30 extends by continuity to Inf_i^{(0)}[f] = Σ_{α : #α = 1, α_i ≠ 0} f̂(α)². Extend also Proposition 8.31 to the case δ = 1.

<a id="pdf-50833afe7403-p030-b008"></a>
<!-- pdf-source: page=30; block=8; confidence=0.90 -->
**Exercise 8.14.** Prove explicitly that condition 5 holds in Theorem 8.35.

<a id="pdf-50833afe7403-p030-b009"></a>
<!-- pdf-source: page=30; block=9; confidence=0.90 -->
**Exercise 8.15.** Prove that condition 6 must hold in Theorem 8.35 directly from the uniqueness statement, i.e., without appealing to the explicit construction.

<a id="pdf-50833afe7403-p030-b010"></a>
<!-- pdf-source: page=30; block=10; confidence=0.90 -->
**Exercise 8.16.** Let f ∈ L²(Ωⁿ, π^{⊗n}). Prove directly from the defining Theorem 8.35 that (f^{=S})^{⊆T} equals f^{=S} if S ⊆ T and is 0 otherwise.

<a id="pdf-50833afe7403-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.98 -->
**§8.7. Exercises and notes** (p. 237).

<a id="pdf-50833afe7403-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.90 -->
**Exercise 8.17.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$, $x\sim\pi^{\otimes n}$, study how the conditional expectation evolves as $x_1,\dots,x_n$ are revealed one at a time.

(a) Since $f^{\subseteq[t]}(x)$ depends only on $x_1,\dots,x_t$ (with $f^{\subseteq[0]}:=f^{=\varnothing}$), show $(f^{\subseteq[t]}(x))_{t=0\dots n}$ is a martingale (the **Doob martingale** of $f$): $\mathbb{E}[f^{\subseteq[t]}(x)\mid f^{\subseteq[0]}(x),\dots,f^{\subseteq[t-1]}(x)]=f^{\subseteq[t-1]}(x)$ for all $t\in[n]$.

(b) For $t\in[n]$ define $d_tf=f^{\subseteq[t]}-f^{\subseteq[t-1]}=\sum_{S\subseteq[n],\,\max(S)=t} f^{=S}$. Show $\mathbb{E}[d_tf(x)\mid f^{\subseteq[0]}(x),\dots,f^{\subseteq[t-1]}(x)]=0$; $(d_tf)_{t=1\dots n}$ is the **martingale difference sequence**.

<a id="pdf-50833afe7403-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.90 -->
**Exercise 8.18.** For $f,g\in L^2(\Omega^n,\pi^{\otimes n})$, prove the following directly from Theorem 8.35: $\langle f,g\rangle=\sum_{S\subseteq[n]}\langle f^{=S},g^{=S}\rangle$; $\mathrm{Inf}_i[f]=\sum_{S\ni i}\lVert f^{=S}\rVert_2^2$; $\mathrm{I}[f]=\sum_{k=0}^n k\,\mathrm{W}^k[f]$; $\mathrm{T}_\rho(f^{=S})=(\mathrm{T}_\rho f)^{=S}=\rho^{|S|}f^{=S}$; and $\mathrm{Stab}_\rho[f]=\sum_{k=0}^n \rho^k\,\mathrm{W}^k[f]$.

<a id="pdf-50833afe7403-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.95 -->
**Exercise 8.19.** For $f\in L^2(\Omega^n,\pi^{\otimes n})$ and $S\subseteq[n]$, show $\lVert f^{=S}\rVert_\infty\le 2^{|S|}\lVert f\rVert_\infty$.

<a id="pdf-50833afe7403-p031-b005"></a>
<!-- pdf-source: page=31; block=5; confidence=0.97 -->
**Exercise 8.20.** Explicitly verify that Proposition 8.36 holds for the function in Examples 8.15 and 8.37.

<a id="pdf-50833afe7403-p031-b006"></a>
<!-- pdf-source: page=31; block=6; confidence=0.92 -->
**Exercise 8.21.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ and let $i\in S\subseteq[n]$. Suppose we take $f^{=S}$ and restrict its $i$th coordinate to have value $\omega_i$, forming the subfunction $g=(f^{=S})_{|\omega_i}$ on coordinates $S\setminus\{i\}$. Show that $g=g^{=S\setminus\{i\}}$. In particular $\mathbb{E}[g]=0$ assuming $|S|\ge 2$.

<a id="pdf-50833afe7403-p031-b007"></a>
<!-- pdf-source: page=31; block=7; confidence=0.92 -->
**Exercise 8.22.** Let $f\in L^2(\Omega^n,\pi^{\otimes n})$ be a symmetric function. Show that if $1\le|S|\le|T|\le n$, then $\tfrac{1}{|S|}\mathrm{Var}[f^{\subseteq S}]\le\tfrac{1}{|T|}\mathrm{Var}[f^{\subseteq T}]$.

<a id="pdf-50833afe7403-p031-b008"></a>
<!-- pdf-source: page=31; block=8; confidence=0.95 -->
**Exercise 8.23.** Prove the sharp threshold statement about the majority function made in Example 8.49 (Hint: Chernoff bound). In social choice this is the **Condorcet Jury Theorem**.

<a id="pdf-50833afe7403-p031-b009"></a>
<!-- pdf-source: page=31; block=9; confidence=0.85 -->
**Exercise 8.24.** For $p_1,\dots,p_n\in(0,1)$ let $\pi=\pi_{p_1}\otimes\cdots\otimes\pi_{p_n}$ be the associated product distribution on $\{-1,1\}^n$. Write $\mu_i=1-2p_i$ and $\sigma_i=2\sqrt{p_i(1-p_i)}$. Generalize Proposition 8.45 to the setting of $L^2(\{-1,1\}^n,\pi)$.

<a id="pdf-50833afe7403-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.88 -->
**Exercise 8.25.** For $f:\{-1,1\}^n\to\mathbb{R}$ in the general product setting of Ex. 8.24.

(a) For $S=\{i_1,\dots,i_k\}\subseteq[n]$, write $\mathrm{D}_{\phi_S}=\mathrm{D}_{\phi_{i_1}}\circ\cdots\circ\mathrm{D}_{\phi_{i_k}}$ (and $\mathrm{D}_{x_S}$ similarly); show $\mathrm{D}_{\phi_S}=\big(\prod_{i\in S}\sigma_i\big)\,\mathrm{D}_{x_S}$.

(b) Writing $f^{(\mu)}$ for $f$ viewed in $L^2(\{-1,1\}^n,\pi)$, show $\widehat{f^{(p)}}(S)=\big(\prod_{i\in S}\sigma_i\big)\,\mathrm{D}_{x_S}f(\mu_1,\dots,\mu_n)$.

(c) Show $\lVert\widehat{f^{(p)}}\rVert_\infty\le\big(\prod_{i\in S}\sigma_i\big)\,\lVert\widehat f\rVert_\infty$.

<a id="pdf-50833afe7403-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.90 -->
**Exercise 8.26.** (a) Generalize Ex. 2.10: for $f\in L^2(\{-1,1\}^n,\pi_p^{\otimes n})$ with range $\{-1,1\}$, $\Pr_{x\sim\pi_p^{\otimes n}}[\,i\text{ is }b\text{-pivotal for }f\text{ on }x\,]=\pi_p(b)\,\mathrm{Inf}_i[f]$ for $i\in[n]$, $b\in\{-1,1\}$.

(b) Generalize Proposition 4.7: if $\mathrm{DNFwidth}(f)\le w$ then $\mathrm{I}[f^{(p)}]\le 4pw\le 4w$; and if $\mathrm{CNFwidth}(f)\le w$ then $\mathrm{I}[f^{(p)}]\le 4qw\le 4w$ (where $q=1-p$).

<a id="pdf-50833afe7403-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.95 -->
**Exercise 8.27.** Fix $\alpha\in(0,1)$. For a nonconstant monotone $f:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$, show there exists $p\in(0,1)$ with $\Pr_{\pi_p}[f(x)=\text{True}]=\alpha$. (Hint: Intermediate Value Theorem.)

<a id="pdf-50833afe7403-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.88 -->
**Exercise 8.28.** Fix $0<\varepsilon<1/2$ and a nonconstant monotone $f$. Let $p_0,p_c,p_1$ be the unique $p\in(0,1)$ with $\Pr_{\pi_p}[f=\text{True}]=\varepsilon,\ 1/2,\ 1-\varepsilon$ respectively (well-defined by Ex. 8.27). Set $\sigma_c^2=4p_c(1-p_c)$ and threshold width $\delta=p_1-p_0$; threshold interval $[p_0,p_1]$. For a sequence $(f_n)_{n\in\mathbb{N}}$ of nonconstant monotone Boolean functions define $p_0(n),p_c(n),p_1(n),\sigma_c^2(n),\delta(n)$. $(f_n)$ has a **sharp threshold** if $\delta(n)/\sigma_c^2(n)\to0$; otherwise a **coarse threshold** (if $p_c(n)=1/2$ for all $n$, equivalent to $\delta(n)/p_c(n)\to0$). Show: if $(f_n)$ has a coarse threshold, there exist $C<\infty$, an infinite subsequence $n_1<n_2<n_3<\cdots$, and $(p(n_i))_{i\in\mathbb{N}}$ with, for all $i$: $\varepsilon<\Pr_{\pi_{p(n_i)}}[f_{n_i}(x)=\text{True}]<1-\varepsilon$ and $\mathrm{I}[f_{n_i}^{(p(n_i))}]\le C$. (Hint: Margulis–Russo and the Mean Value Theorem.)

<a id="pdf-50833afe7403-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.80 -->
**Exercise 8.29 (setup).** Let $f:\{-1,1\}^n\to\{-1,1\}$ be nonconstant monotone and $F:[0,1]\to[0,1]$ the strictly increasing function $F(p)=\Pr_{\pi_p}[f(x)=-1]$. Let $p_c$ be the critical probability with $F(p_c)=1/2$; assume $p_c\le1/2$ (WLOG, replacing $f$ by $f^\dagger$). [Parts (a)–(f) continue on p. 239.]

<a id="pdf-50833afe7403-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.92 -->
**Exercise 8.29 (cont.).** Thinking of $p_c\ll 1/2$, the goal is a weak threshold result: $F(p)=o(1)$ when $p=o(p_c)$ and $F(p)=1-o(1)$ when $p=\omega(p_c)$.

(a) Via Margulis–Russo and the Poincaré Inequality, show for all $0<p<1$: $F'(p)\ge\dfrac{F(p)(1-F(p))}{p(1-p)}$.

(b) For $p\le p_c$ show $F'(p)\ge\dfrac{F(p)}{2p}$, hence $\dfrac{d}{dp}\ln F(p)\ge\dfrac{1}{2p}$.

(c) Deduce for $0\le p_0\le p_c$: $F(p_0)\le\tfrac12\sqrt{p_0/p_c}$; i.e. $F(p_0)\le\varepsilon$ if $p_0\le(2\varepsilon)^2 p_c$.

(d) Show the factor $(2\varepsilon)^2$ can be improved to $\Theta(\tau)\varepsilon^{1+\tau}$ for any small constant $\tau>0$. (Hint: the quadratic dependence on $\varepsilon$ came from using $1-F(p)\ge1/2$ for $p\le p_c$; part (c) gives the improved $1-F(p)\ge1-\tau$ once $p\le(2\tau)^2 p_c$.)

(e) In the other direction, show that so long as $p_1=\tfrac{1}{(2\varepsilon)^2}p_c\le1/2$, we have $F(p_1)\ge1-\varepsilon$ (Hint: work with $\ln(1-F(p))$); if $p_1\le1/2$ does not hold, show at least $F(1/2)\ge1-\sqrt{p_c/2}$.

(f) Since (e) is uninteresting when $p_c$ is close to $1/2$, show additionally $F(1-\delta)\ge 1-\sqrt{\delta/2}$ (even when $p_c=1/2$).

<a id="pdf-50833afe7403-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.90 -->
**Exercise 8.30.** Define $f_n:\{\text{True},\text{False}\}^n\to\{\text{True},\text{False}\}$ for odd $n\ge3$ by $f_n(x_1,\dots,x_n)=\mathrm{Maj}_3(x_1,x_2,\mathrm{Maj}_{n-2}(x_3,\dots,x_n))$.

(a) Show $f_n$ is monotone with critical probability $p_c=1/2$.

(b) Sketch $\Pr_{\pi_p}[f_n(x)=\text{True}]$ versus $p$ (for very large $n$).

(c) Show $\mathrm{I}[f_n]=\Theta(\sqrt n)$.

(d) Show $(f_n)$ has a coarse threshold as defined in Ex. 8.28 (assuming $\varepsilon<1/4$).

<a id="pdf-50833afe7403-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.93 -->
**Exercise 8.31.** (a) Three distributions on $x\in\mathbb{F}_2^n$: (1) choose $k\in\{0,1,\dots,n\}$ uniformly, then $x$ uniformly among all Hamming-weight-$k$ strings; (2) choose a uniformly random permutation $\pi\in S_n$ (a random “path from $0^n$ to $1^n$”), with $\pi^{\le i}\in\mathbb{F}_2^n$ the string whose $j$th coordinate is $1$ iff $\pi(j)\le i$; choose $k\in\{0,\dots,n\}$ uniformly and set $x=\pi^{\le k}$; (3) choose $p\sim\mathrm{Unif}[0,1]$, then $x\sim\pi_p^{\otimes n}$. Show these are the same distribution. (Hint: place $n+1$ indistinguishable uniform points in $[0,1]$ and randomly label them “$p$”$,1,2,\dots,n$.)

<a id="pdf-50833afe7403-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.95 -->
# 8. Generalized domains

(Section 8.7, Exercises and notes.)

<a id="pdf-50833afe7403-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.85 -->
**Exercise 8.31 (continued).**

(b) Let $\nu_n$ be the distribution on $\mathbb{F}_2^{[n]}$ from part (a); more generally $\nu_N$ the analogous distribution on $\mathbb{F}_2^N$ for an abstract set $N$ of cardinality $n$. For nonempty $J \subseteq [n]$, show that if $x \sim \nu_n$ and $x_J$ is the restriction of $x$ to the coordinates $J$, then $x_J \sim \nu_J$.

(c) For $f : \mathbb{F}_2^n \to \mathbb{R}$ and $i \in [n]$, define the $i$th Shapley value $\mathrm{Shap}_i[f] = \mathbb{E}_{x \sim \nu_n}[\,f(x^{(i\mapsto 1)}) - f(x^{(i\mapsto 0)})\,]$. Show $\sum_{i=1}^n \mathrm{Shap}_i[f] = f(1,\dots,1) - f(0,\dots,0)$.

(d) For monotone $f : \mathbb{F}_2^n \to \{0,1\}$, show $\mathrm{Shap}_i[f] = \int_0^1 \mathrm{Inf}_i[f^{(p)}]\,dp$.

<a id="pdf-50833afe7403-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.90 -->
**Exercise 8.32.** Generalize the definitions and results of Sections 8.1–8.2 to the complex inner product space $L^2(\Omega^n, \pi^{\otimes n})$. In particular verify the following formulas from Proposition 8.16 (sums over $\alpha \in \mathbb{N}^n_{<m}$):

- $\mathbb{E}[f] = \widehat f(0)$;
- $\mathbb{E}[|f|^2] = \langle f,f\rangle = \sum_\alpha \langle \widehat f(\alpha), \widehat f(\alpha)\rangle = \sum_\alpha |\widehat f(\alpha)|^2$;
- $\mathrm{Var}[f] = \langle f - \mathbb{E}[f],\, f - \mathbb{E}[f]\rangle = \sum_{\alpha \neq 0} |\widehat f(\alpha)|^2$;
- $\langle f,g\rangle = \sum_\alpha \langle \widehat f(\alpha), \widehat g(\alpha)\rangle = \sum_\alpha \widehat f(\alpha)\overline{\widehat g(\alpha)}$;
- $\mathrm{Cov}[f,g] = \langle f - \mathbb{E}[f],\, g - \mathbb{E}[g]\rangle = \sum_{\alpha \neq 0} \widehat f(\alpha)\overline{\widehat g(\alpha)}$.

<a id="pdf-50833afe7403-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.72 -->
**Exercise 8.33.**

(a) As in Exercise 2.58, generalize Sections 8.1–8.2 to functions $f : \Omega^n \to V$ where $V$ is a real inner product space with inner product $\langle\cdot,\cdot\rangle$. The Fourier coefficients $\hat f(\alpha)$ lie in $V$, and $\langle f,g\rangle := \mathbb{E}_{x\sim\pi^{\otimes n}}[\langle f(x),g(x)\rangle_V]$. Verify Proposition 8.16, including Plancherel: $\langle f,g\rangle = \sum_\alpha \langle \hat f(\alpha), \hat g(\alpha)\rangle_V$.

(b) For a finite set $\Sigma$, write $\triangle_\Sigma$ for the set of probability distributions over $\Sigma$ (cf. Exercise 7.22), identified with the standard convex simplex in $\mathbb{R}^m$, $\{\mu \in \mathbb{R}^m : \mu_1 + \cdots + \mu_m = 1,\ \mu_i \geq 0\}$ ($m = |\Sigma|$, fixed ordering), and identify the elements of $\Sigma$ with the constant distributions (vertices $(0,\dots,0,1,0,\dots,0)$). Interpreting $f : \Omega^n \to \triangle_\Sigma$ as $f : \Omega^n \to \mathbb{R}^m$ via part (a) with $V = \mathbb{R}^m$, show that for $f : \Omega^n \to \triangle_\Sigma$ and a distribution $\pi$ on $\Omega$, $\mathrm{Stab}_\rho[f] = \Pr_{x\sim\pi^{\otimes n},\, y\sim N_\rho(x)}[f(x) = f(y)]$. (In $\mathrm{Stab}_\rho$ the range is treated as $\triangle_\Sigma \subset \mathbb{R}^m$; in $f(x)=f(y)$ it is treated as the abstract set $\Sigma$.)

<a id="pdf-50833afe7403-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.80 -->
**Exercise 8.34.** Call $f \in L^2(\Omega^n, \pi^{\otimes n})$ a *linear threshold function* if $f(x) = \mathrm{sgn}(\ell(x))$ for some $\ell : \Omega^n \to \mathbb{R}$ of degree at most 1 (in the sense of Definition 8.32).

(a) Given $\omega(+1), \omega(-1) \in \Omega^n$ and $x \in \{-1,1\}^n$, write $\omega(x) = (\omega(x_1),\dots,\omega(x_n)) \in \Omega^n$. Show that if $\omega(+1), \omega(-1)$ are drawn independently and $(x,y)$ is a $\rho$-correlated pair of binary strings, then $(\omega(x), \omega(y))$ is a $\rho$-correlated pair under $\pi^{\otimes n}$.

(b) Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ be a linear threshold function. For a pair $\omega(+1),\omega(-1)$, define $g_{\omega(+1),\omega(-1)} : \{-1,1\}^n \to \{-1,1\}$ by $g_{\omega(+1),\omega(-1)}(x) = f(\omega(x))$. Show $g_{\omega(+1),\omega(-1)}$ is a linear threshold function in the usual sense.

(c) Prove that Peres's Theorem (Chapter 5.5) applies to linear threshold functions in $L^2(\Omega^n, \pi^{\otimes n})$, with the same bounds.

<a id="pdf-50833afe7403-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.85 -->
**Exercise 8.35.** Let $G$ be a finite abelian group; by the Fundamental Theorem of Finitely Generated Abelian Groups $G \cong \mathbb{Z}_{m_1} \times \cdots \times \mathbb{Z}_{m_n}$ with each $m_j$ a prime power.

(a) For $\alpha \in G$, define $\chi_\alpha : G \to \mathbb{C}$ by $\chi_\alpha(x) = \prod_{j=1}^n \exp(2\pi i\,\alpha_j x_j / m_j)$. Show $\chi_\alpha$ is a character of $G$, that distinct $\alpha$ give distinct functions, and deduce the set of all $\chi_\alpha$ forms a Fourier basis for $L^2(G)$.

(b) Show these characters form a group under multiplication isomorphic to $G$ (generalizing Fact 8.58); this is the dual group $\hat G$, whose characters are identified with their indices $\alpha$.

<a id="pdf-50833afe7403-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=0.85 -->
**Exercise 8.36.** Verify that the convolution operation on $L^2(G)$ is associative and commutative, and that it satisfies $\widehat{f * g}(\alpha) = \hat f(\alpha)\,\hat g(\alpha)$ for all $\alpha \in \hat G$. (See Exercise 8.35 for the definition of $\hat G$.)

<a id="pdf-50833afe7403-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=0.93 -->
**Exercise 8.37.** (spanning pp. 241–242)

(a) Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ be transitive-symmetric and $\mathcal{T}$ a randomized decision tree computing $f$. Show there exists a randomized decision tree $\mathcal{T}'$ computing $f$ with $\Delta^{(\pi)}(\mathcal{T}') = \Delta^{(\pi)}(\mathcal{T})$ and such that $\delta_i^{(\pi)}(\mathcal{T}')$ is the same for all $i \in [n]$. (Hint: randomize over $\mathrm{Aut}(f)$ and use Exercise 2.47.)

(b) For a randomized decision tree $\mathcal{T}$, set $\delta^{(\pi)}(\mathcal{T}) = \max_{i\in[n]} \delta_i^{(\pi)}(\mathcal{T})$. For $f \in L^2(\{-1,1\}^n, \pi^{\otimes n})$ define $\delta^{(\pi)}(f)$ as the minimum of $\delta^{(\pi)}(\mathcal{T})$ over all $\mathcal{T}$ computing $f$ (the *revealment* of $f$). Show that if $f$ is transitive-symmetric then $\delta^{(\pi)}(f) = \tfrac{1}{n}\Delta^{(\pi)}(f)$.

<a id="pdf-50833afe7403-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.95 -->
**Exercise 8.38.**

(a) Show that $\mathrm{DT}(\mathrm{Maj}_3^{\otimes d}) = 3^d$, $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d}) \leq (8/3)^d$, and $\Delta(\mathrm{Maj}_3^{\otimes d}) \leq (5/2)^d$.

(b) Show that $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes 2}) < (8/3)^2$. How small can you make your upper bound?

<a id="pdf-50833afe7403-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.80 -->
**Exercise 8.39.**

(a) Show that for every deterministic decision tree $T$ computing the logical OR function on $n$ bits,
$$\Delta^{(p)}(T) = p\cdot 1 + (1-p)p\cdot 2 + (1-p)^2 p\cdot 3 + \cdots + (1-p)^{n-2}p\cdot(n-1) + (1-p)^{n-1}\cdot n = \frac{1-(1-p)^n}{p}.$$
Deduce $\Delta^{(p)}(\mathrm{OR}_n) = \dfrac{1-(1-p)^n}{p}$.

(b) Show $\Delta^{(p_c)}(\mathrm{OR}_n) \sim n/(2\ln 2)$ as $n \to \infty$, where $p_c$ denotes the critical probability for $\mathrm{OR}_n$.

<a id="pdf-50833afe7403-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.85 -->
**Exercise 8.40.** Let $\mathrm{NAND} : \{\text{True},\text{False}\}^2 \to \{\text{True},\text{False}\}$ output True unless both inputs are True.

(a) For $d$ even, show $\mathrm{NAND}^{\otimes d} = \mathrm{Tribes}_{2,2}^{\otimes d/2}$ (so recursive NAND is the AND-OR tree).

(b) Show $\mathrm{DT}(\mathrm{NAND}^{\otimes d}) = 2^d$.

(c) Show $\mathrm{RDT}(\mathrm{NAND}) = 2$.

(d) For $b \in \{\text{True},\text{False}\}$ and $T$ a randomized decision tree computing $f$, let $\mathrm{RDT}_b(T)$ be the maximum cost of $T$ over inputs $x$ with $f(x) = b$. Show there is a randomized decision tree $T$ computing NAND with $\mathrm{RDT}_{\text{False}}(T) = 3/2$.

(e) Show $\mathrm{RDT}(\mathrm{NAND}^{\otimes 2}) \leq 3$.

(f) Show there is a family $(T_d)_{d \in \mathbb{N}^+}$ with $T_d$ computing $\mathrm{NAND}^{\otimes d}$ satisfying $\mathrm{RDT}_{\text{False}}(T_d) \leq 2\,\mathrm{RDT}_{\text{True}}(T_{d-1})$ and $\mathrm{RDT}_{\text{True}}(T_d) \leq \mathrm{RDT}_{\text{False}}(T_{d-1}) + \tfrac{1}{2}\mathrm{RDT}_{\text{True}}(T_{d-1})$.

(g) Deduce $\mathrm{RDT}(\mathrm{NAND}^{\otimes d}) \leq \left(\tfrac{1+\sqrt{33}}{4}\right)^d \approx n^{.754}$, where $n = 2^d$.

<a id="pdf-50833afe7403-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.95 -->
**Exercise 8.41.** Let $C = \{\text{monotone } f : \{-1,1\}^n \to \{-1,1\} : \mathrm{DT}(f) \leq k\}$. Show $C$ is learnable from random examples with error $\varepsilon$ in time $n^{O(\sqrt{k/\varepsilon})}$. (Hint: OS Inequality and Corollary 3.32.)

<a id="pdf-50833afe7403-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.85 -->
**Exercise 8.42.** Verify that the decision tree process described in Definition 8.70 indeed generates strings distributed according to $\pi^{\otimes n}$. (Hint: induction on the structure of the tree.)

<a id="pdf-50833afe7403-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.98 -->
## 8.7. Exercises and notes

<a id="pdf-50833afe7403-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.95 -->
**Exercise 8.43.** For a deterministic decision tree $T$ of size $s$, show $\Delta(T) \le \log s$. Hint: bound the entropy of a random root-to-leaf path $P$ from the decision tree process.

<a id="pdf-50833afe7403-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.92 -->
**Exercise 8.44.** Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ be nonconstant with range $\{-1,1\}$.

(a) Show $\mathrm{MaxInf}[f] \ge \mathrm{Var}[f]/\Delta^{(\pi)}(f)$ (cf. the KKL Theorem, Ch. 4.2).

(b) For $\Omega = \{-1,1\}$, show $\mathrm{MaxInf}[f] \ge \mathrm{Var}[f]/\deg(f)^3$ (use Midrijānis's result cited in the Ch. 3.6 notes).

(c) Show $I[f] \ge \mathrm{Var}[f]/\delta^{(\pi)}(f)$, where $\delta^{(\pi)}(f)$ is the revealment of $f$ from Exercise 8.37(b).

<a id="pdf-50833afe7403-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.90 -->
**Exercise 8.45.** Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ have range $\{-1,1\}$.

(a) For a randomized decision tree $T$ computing $f$ and $i \in [n]$, show $\mathrm{Inf}_i[f] \le \delta^{(\pi)}_i(T)$ (hint: the decision tree process).

(b) If $f$ is transitive-symmetric, show $\Delta^{(\pi)}(f) \ge \mathrm{Var}[f]\cdot\sqrt{n}$ (hint: Exercise 8.37(b)). This is sharp up to an $O(\sqrt{\log n})$ factor even for $f:\{-1,1\}^n \to \{-1,1\}$ with $\mathrm{Var}[f]=1$; see [BSW05].

<a id="pdf-50833afe7403-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.90 -->
**Exercise 8.46.** An alternate proof of the OSSS Inequality, sharp when $\mathrm{Var}[f]=1$ and weaker by only a factor of 2 when $\mathrm{Var}[f]$ is small. Let $f \in L^2(\Omega^n, \pi^{\otimes n})$ have range $\{-1,1\}$; for a randomized tree $\mathcal{T}$ write $\mathrm{err}(\mathcal{T}) = \Pr_{x \sim \pi^{\otimes n}}[\mathcal{T}(x) \ne f(x)]$.

(a) Let $T$ be a depth-$k$ deterministic tree (not necessarily computing $f$) whose root queries coordinate $i$. Let $\mathbf{T}$ be the distribution over depth-$\le k-1$ deterministic trees given by following a random outgoing edge from $T$'s root (according to $\pi$). Show $\mathrm{err}(\mathbf{T}) \le \mathrm{err}(T) + \tfrac12 \mathrm{Inf}_i[f]$.

(b) For a randomized tree $\mathcal{T}$ of depth 0, show $\mathrm{err}(\mathcal{T}) \ge \min\{\Pr[f(x)=1],\, \Pr[f(x)=-1]\}$.

(c) By induction on depth, for any randomized tree $\mathcal{T}$: $\tfrac12 \sum_{i=1}^n \delta^{(\pi)}_i(\mathcal{T})\,\mathrm{Inf}_i[f] \ge \min\{\Pr[f(x)=1],\, \Pr[f(x)=-1]\} - \mathrm{err}(\mathcal{T})$. Verify this yields the OSSS Inequality when $\mathrm{Var}[f]=1$, and in general up to a factor of 2.

<a id="pdf-50833afe7403-p037-b006"></a>
<!-- pdf-source: page=37; block=6; confidence=0.95 -->
**Exercise 8.47.** Show the OSSS Inequality fails for functions $f:\{-1,1\}^n \to \mathbb{R}$. Hint: the simplest counterexample uses a decision tree with the shape in Figure 8.2.

<a id="pdf-50833afe7403-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.93 -->
**Figure 8.2.** The basis for a counterexample to the OSSS Inequality when $f:\{-1,1\}^n \to \mathbb{R}$. (Can you make the ratio of the left-hand side to the right-hand side equal to $\tfrac{130 + 20\sqrt{3}}{157}$? Larger?)

<a id="pdf-50833afe7403-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.95 -->
### Notes

<a id="pdf-50833afe7403-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.85 -->
History of the orthogonal decomposition (Section 8.3), dating to Hoeffding [Hoe48] (also von Mises [vM47]). Hoeffding introduced U-statistics: functions of independent $X_1,\dots,X_n$ of the form $\mathrm{avg}_{i_1<\cdots<i_k} g(X_{i_1},\dots,X_{i_k})$ with $g:\mathbb{R}^k \to \mathbb{R}$ symmetric (hence $f$ symmetric). For these he introduced $f^{\subseteq S}$ (depending only on $|S|$) and proved inequalities (cf. Exercise 8.22) relating $\mathrm{Var}[f]$ to the $\|f^{=S}\|^2$. Nonsymmetric $f$ were rarely studied for three decades; exception Hájek [Háj68] introduced $f^{\le 1}$ (the Hájek projection), and Bourgain [Bou79] described $f^{=k} = \sum_S f^{=S}$. General orthogonal decomposition for nonsymmetric $f$ first appears in Efron–Stein [ES81] (late 1970s), developed further by Karlin–Rinott [KR82]. Efron–Stein's main result $\mathrm{Var}[f] \le I[f]$ for symmetric $f$ is the Efron–Stein Inequality; Steele [Ste86a] extended it to nonsymmetric $f$ via the Fourier-basis approach to orthogonal decomposition, which originated in Rubin–Vitale [RV80] (also Takemura [Tak83], Vitale [Vit84]). The "Fourier basis" terminology is nonstandard.

<a id="pdf-50833afe7403-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.88 -->
The $p$-biased hypercube distribution is motivated by Erdős–Rényi [ER59] random graph theory (see Bollobás–Riordan [BR08]) and percolation theory (Broadbent–Hammersley [BH57]). Influences under the $p$-biased distribution and their link to threshold phenomena were studied by Russo [Rus81, Rus82]; the former proved the Margulis–Russo formula independently of Margulis.

<a id="pdf-50833afe7403-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.86 -->
Margulis had proven the Margulis–Russo formula earlier [Mar74]. $p$-biased Fourier analysis was first brought to TCS by Furst–Jackson–Smith [FJS91], extending the LMN learning algorithm for $\mathrm{AC}^0$. Talagrand [Tal93, Tal94] developed $p$-biased Fourier for threshold phenomena, proving the KKL Theorem in the $p$-biased setting; similar results by Friedgut–Kalai [FK96] via Bourgain–Kahn–Kalai–Linial–Katznelson [BKK+92] (a KKL version for general product spaces). Sharp thresholds for cliques and connectivity in Example 8.49 are due to Matula and Erdős–Rényi respectively (see Bollobás [Bol01]). Weak threshold results as in Exercise 8.29 were proved by Bollobás–Thomason [BT87] using Kruskal–Katona rather than the Poincaré Inequality.

<a id="pdf-50833afe7403-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.90 -->
Fourier analysis on finite (and locally compact) abelian groups is only touched on briefly; references: Rudin [Rud62] and Terras [Ter99] (the latter focused on finite groups).

<a id="pdf-50833afe7403-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.88 -->
Early work on randomized decision tree complexity: Saks–Wigderson [SW86] (Exercise 8.40). Note $\mathrm{RDT}(f)$ is usually written $R(f)$ and $\mathrm{DT}(f)$ as $D(f)$. A basic lower bound is $\mathrm{RDT}(f) \ge \sqrt{\mathrm{DT}(f)}$ for any $f:\{-1,1\}^n \to \{-1,1\}$, holding even for nondeterministic decision tree complexity [BI87, Tar89]. Yao's Conjecture is sometimes attributed to Richard Karp. For recursive majority-of-3, Ravi Boppana first noted $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d}) = o(3^d)$ though $\mathrm{DT}(\mathrm{Maj}_3^{\otimes d}) = 3^d$; Saks–Wigderson noted $\mathrm{RDT}(\mathrm{Maj}_3^{\otimes d}) \le (8/3)^d$ (not optimal). Best known bounds: upper $O(2.65^d)$ [MNSX11], lower $\Omega(2.55^d)$ [Leo12].

<a id="pdf-50833afe7403-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.87 -->
The presented OSSS Inequality proof is essentially Lee's [Lee10]; the alternate proof (Exercise 8.46) is due to Jain–Zhang [JZ11]. The Condorcet Jury Theorem (Exercise 8.23) is from [dC85]. The Shapley value (Exercise 8.31) was introduced by Shapley [Sha53] (see Roth [Rot88]). Exercise 8.34 is from Blais–O'Donnell–Wimmer [BOW10]. Exercises 8.37(a) and 8.45 are from Benjamini–Schramm–Wilson [BSW05]; "revealment" is from Schramm–Steif [SS10]. Exercise 8.47 is from [OSSS05]. (Text continues beyond the supplied pages.)

<a id="pdf-50833afe7403-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.90 -->
**Chapter 8. Generalized domains** (printed page 246).

<a id="pdf-50833afe7403-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.85 -->
It has been suggested that the property of Exercise 8.44(b) also holds for functions $f:\{-1,1\}^n \to [-1,1]$, with a conjectured affirmative answer.

<a id="pdf-50833afe7403-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.95 -->
**Aaronson–Ambainis Conjecture** [Aar08, AA11]. For $f:\{-1,1\}^n \to [-1,1]$, $\mathrm{MaxInf}[f] \ge \mathrm{poly}(\mathrm{Var}[f]/\deg(f))$.

<a id="pdf-50833afe7403-p040-b004"></a>
<!-- pdf-source: page=40; block=4; confidence=0.92 -->
If true, the conjecture would have significant consequences for the limitations of efficient quantum computation (see [AA11]). The best known result toward it, due to Dinur et al. [DFKO07], is the lower bound $\mathrm{MaxInf}[f] \ge \mathrm{poly}(\mathrm{Var}[f]/2^{\deg(f)})$.
