<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: cdca27e1b5fd476248b00c800b13ba2b3a166b02bdeeabe815ee2ebf9d3cf3fd -->

<a id="pdf-cdca27e1b5fd-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Chapter 1 — Boolean functions and the Fourier expansion

<a id="pdf-cdca27e1b5fd-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
This chapter introduces analysis of Boolean functions, emphasizing the Fourier expansion as the representation of a Boolean function by a real multilinear polynomial. Harmonic analysis over $\mathbb F_2^n$ is deferred to Chapter 3. Basic Fourier formulas are illustrated through the Blum–Luby–Rubinfeld linearity test.

<a id="pdf-cdca27e1b5fd-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
## 1.1. On analysis of Boolean functions

<a id="pdf-cdca27e1b5fd-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.99 -->
A Boolean function is a map
$$f:\{0,1\}^n\to\{0,1\}.$$
It maps each length-$n$ binary vector to one bit. Examples arise in circuit design, graph properties, extremal combinatorics (set systems), coding theory, learning theory, and social choice.

<a id="pdf-cdca27e1b5fd-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.99 -->
Bits may be represented as `True`/`False`, as $-1$ and $1$, or as $0$ and $1$ (as real numbers, elements of $\mathbb F_2$, or symbols). Most often the representation is
$$f:\{-1,1\}^n\to\{-1,1\}.$$
The domain is called the Hamming cube. For $x,y\in\{-1,1\}^n$,
$$\Delta(x,y)=\#\{i:x_i\ne y_i\}.$$
Problems involving Hamming distance, counting strings, or the uniform distribution on the cube are natural candidates for analysis by Fourier expansion.

<a id="pdf-cdca27e1b5fd-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.99 -->
## 1.2. The “Fourier expansion”: functions as multilinear polynomials

<a id="pdf-cdca27e1b5fd-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
The Fourier expansion of $f:\{-1,1\}^n\to\{-1,1\}$ is its representation as a real multilinear polynomial, meaning that no variable appears with exponent greater than one.

<a id="pdf-cdca27e1b5fd-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
For the two-bit maximum function,
$$\operatorname{max}_2(+1,+1)=+1,\quad \operatorname{max}_2(-1,+1)=+1,\quad \operatorname{max}_2(+1,-1)=+1,\quad \operatorname{max}_2(-1,-1)=-1.$$
Then
$$\operatorname{max}_2(x_1,x_2)=\tfrac12+\tfrac12x_1+\tfrac12x_2-\tfrac12x_1x_2.\tag{1.1}$$
For three-bit majority,
$$\operatorname{Maj}_3(x_1,x_2,x_3)=\tfrac12x_1+\tfrac12x_2+\tfrac12x_3-\tfrac12x_1x_2x_3.\tag{1.2}$$
The functions $\operatorname{max}_2$ and $\operatorname{Maj}_3$ will serve as running examples in this chapter.

<a id="pdf-cdca27e1b5fd-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.99 -->
For $a=(a_1,\ldots,a_n)\in\{-1,1\}^n$, define
$$1_{\{a\}}(x)=\prod_{i=1}^n\frac{1+a_ix_i}{2}.$$
It equals $1$ at $x=a$ and $0$ at every other cube point. Hence every $f:\{-1,1\}^n\to\mathbb R$ has the representation
$$f(x)=\sum_{a\in\{-1,1\}^n}f(a)1_{\{a\}}(x).$$

<a id="pdf-cdca27e1b5fd-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
For $\operatorname{max}_2$, expanding the interpolation formula gives (1.1). The procedure also works for real-valued functions and always produces a multilinear polynomial, since on the cube $x_i^2=1$.

<a id="pdf-cdca27e1b5fd-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.99 -->
For $S\subseteq[n]$, write
$$x^S=\prod_{i\in S}x_i$$
with $x^\varnothing=1$ by convention. The coefficient of the monomial $x^S$ in the multilinear representation of $f$ is denoted
$$\widehat f(S).$$

<a id="pdf-cdca27e1b5fd-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
Every function $f:\{-1,1\}^n\to\mathbb R$ has a unique multilinear representation
$$f(x)=\sum_{S\subseteq[n]}\widehat f(S)x^S.\tag{1.4}$$
This is the Fourier expansion; $\widehat f(S)$ is the Fourier coefficient on $S$, and all coefficients form the Fourier spectrum.

<a id="pdf-cdca27e1b5fd-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
Examples: $\widehat{\operatorname{max}_2}(\varnothing)=\widehat{\operatorname{max}_2}(\{1\})=\widehat{\operatorname{max}_2}(\{2\})=1/2$, $\widehat{\operatorname{max}_2}(\{1,2\})=-1/2$; for majority, the coefficients on $\{1\},\{2\},\{3\}$ are $1/2$, the coefficient on $\{1,2,3\}$ is $-1/2$, and the remaining coefficients are $0$.

<a id="pdf-cdca27e1b5fd-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.99 -->
For $x\in\mathbb R^n$, define
$$\chi_S(x)=\prod_{i\in S}x_i.$$
Then
$$f(x)=\sum_{S\subseteq[n]}\widehat f(S)\chi_S(x).$$
For the encoding $\chi:\mathbb F_2\to\mathbb R$ given by $\chi(0)=+1$ and $\chi(1)=-1$, this extends to $\mathbb F_2^n$ by
$$\chi_S(x)=\prod_{i\in S}\chi(x_i)=(-1)^{\sum_{i\in S}x_i}.$$

<a id="pdf-cdca27e1b5fd-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.99 -->
## 1.3. The orthonormal basis of parity functions

<a id="pdf-cdca27e1b5fd-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.99 -->
For $S\subseteq[n]$, define $\chi_S:\mathbb F_2^n\to\mathbb R$ by
$$\chi_S(x)=\prod_{i\in S}\chi(x_i)=(-1)^{\sum_{i\in S}x_i}.$$
It satisfies
$$\chi_S(x+y)=\chi_S(x)\chi_S(y).\tag{1.5}$$

<a id="pdf-cdca27e1b5fd-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
On $\{-1,1\}^n$, $\chi_S$ computes parity/XOR. Equation (1.6), $f=\sum_S\widehat f(S)\chi_S$, shows that parity functions span the real vector space $V$ of all functions on the cube. Since there are $2^n=\dim V$ parity functions, they form a linearly independent basis, proving uniqueness in Theorem 1.1.

<a id="pdf-cdca27e1b5fd-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.96 -->
The Fourier expansion of $\operatorname{max}_2$ is displayed as the vector decomposition
$$\operatorname{max}_2=\tfrac12\begin{bmatrix}+1\\+1\\+1\\-1\end{bmatrix}+\tfrac12\begin{bmatrix}+1\\+1\\-1\\+1\end{bmatrix}+\tfrac12\begin{bmatrix}+1\\-1\\+1\\-1\end{bmatrix}-\tfrac12\begin{bmatrix}+1\\-1\\-1\\+1\end{bmatrix}.\tag{1.7}$$

<a id="pdf-cdca27e1b5fd-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.99 -->
For $f,g:\{-1,1\}^n\to\mathbb R$,
$$\langle f,g\rangle=2^{-n}\sum_{x\in\{-1,1\}^n}f(x)g(x)=\mathbb E_{x\sim\{-1,1\}^n}[f(x)g(x)].\tag{1.8}$$
We also write $\|f\|_2=\langle f,f\rangle^{1/2}$ and, more generally,
$$\|f\|_p=\mathbb E[|f(x)|^p]^{1/p}.$$

<a id="pdf-cdca27e1b5fd-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.99 -->
The notation $x\sim\{-1,1\}^n$ means that $x$ is uniformly random; its coordinates are independent and each is $+1$ or $-1$ with probability $1/2$. Probabilities and expectations are with respect to this distribution unless specified otherwise.

<a id="pdf-cdca27e1b5fd-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.99 -->
The $2^n$ parity functions form an orthonormal basis for $V$:
$$\langle\chi_S,\chi_T\rangle=
\begin{cases}1&S=T,\\0&S\ne T.\end{cases}$$

<a id="pdf-cdca27e1b5fd-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
For every $x$,
$$\chi_S(x)\chi_T(x)=\chi_{S\triangle T}(x),$$
where $S\triangle T$ is symmetric difference.

<a id="pdf-cdca27e1b5fd-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
$$\mathbb E[\chi_S(x)]=
\begin{cases}1&S=\varnothing,\\0&S\ne\varnothing.\end{cases}$$

<a id="pdf-cdca27e1b5fd-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.99 -->
For Fact 1.7, the empty product has expectation $1$. If $S\ne\varnothing$, independence gives $\mathbb E[\prod_{i\in S}x_i]=\prod_{i\in S}\mathbb E[x_i]$, and each factor is $(+1)/2+(-1)/2=0$. Together with Fact 1.6, this proves Theorem 1.5.

<a id="pdf-cdca27e1b5fd-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.99 -->
## 1.4. Basic Fourier formulas

<a id="pdf-cdca27e1b5fd-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.99 -->
For $f:\{-1,1\}^n\to\mathbb R$ and $S\subseteq[n]$,
$$\widehat f(S)=\langle f,\chi_S\rangle=\mathbb E_x[f(x)\chi_S(x)].\tag{1.9}$$

<a id="pdf-cdca27e1b5fd-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
Using the Fourier expansion and linearity,
$$\langle f,\chi_S\rangle=\left\langle\sum_T\widehat f(T)\chi_T,\chi_S\right\rangle=\sum_T\widehat f(T)\langle\chi_T,\chi_S\rangle=\widehat f(S),$$
by Theorem 1.5.

<a id="pdf-cdca27e1b5fd-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.99 -->
For every $f:\{-1,1\}^n\to\mathbb R$,
$$\langle f,f\rangle=\mathbb E[f(x)^2]=\sum_{S\subseteq[n]}\widehat f(S)^2.$$
If $f$ is Boolean-valued, then $\sum_S\widehat f(S)^2=1$.

<a id="pdf-cdca27e1b5fd-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.99 -->
For $f,g:\{-1,1\}^n\to\mathbb R$,
$$\langle f,g\rangle=\mathbb E[f(x)g(x)]=\sum_{S\subseteq[n]}\widehat f(S)\widehat g(S).$$
This follows by expanding both functions and applying orthonormality.

<a id="pdf-cdca27e1b5fd-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.99 -->
For Boolean-valued $f,g$,
$$\langle f,g\rangle=\Pr[f=g]-\Pr[f\ne g]=1-2\operatorname{dist}(f,g).$$

<a id="pdf-cdca27e1b5fd-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.99 -->
The relative Hamming distance is
$$\operatorname{dist}(f,g)=\Pr_x[f(x)\ne g(x)].$$

<a id="pdf-cdca27e1b5fd-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.99 -->
The mean of $f$ is $\mathbb E[f]$. A mean-zero function is unbiased/balanced. For Boolean-valued $f$,
$$\mathbb E[f]=\Pr[f=1]-\Pr[f=-1].$$

<a id="pdf-cdca27e1b5fd-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.99 -->
$$\mathbb E[f]=\widehat f(\varnothing).$$
Indeed, $\mathbb E[f]=\langle f,1\rangle$ and Proposition 1.8 applies with $S=\varnothing$.

<a id="pdf-cdca27e1b5fd-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
$$\operatorname{Var}[f]=\langle f-\mathbb E[f],f-\mathbb E[f]\rangle=\mathbb E[f^2]-\mathbb E[f]^2=\sum_{S\ne\varnothing}\widehat f(S)^2.$$
This follows from Parseval and Fact 1.12.

<a id="pdf-cdca27e1b5fd-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.99 -->
For Boolean-valued $f$,
$$\operatorname{Var}[f]=1-\mathbb E[f]^2=4\Pr[f=1]\Pr[f=-1]\in[0,1].$$
Thus variance is $1$ for unbiased functions and $0$ for constant functions.

<a id="pdf-cdca27e1b5fd-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.98 -->
For $f:\{-1,1\}^n\to\{-1,1\}$,
$$\operatorname{Var}[f]=1-\mathbb E[f]^2=4\Pr[f(x)=1]\Pr[f(x)=-1]\in[0,1].$$
In particular, if
$$\varepsilon=\min\{\operatorname{dist}(f,1),\operatorname{dist}(f,-1)\},$$
then
$$2\varepsilon\le\operatorname{Var}[f]\le4\varepsilon.$$

<a id="pdf-cdca27e1b5fd-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.99 -->
$$\operatorname{Cov}[f,g]=\langle f-\mathbb E[f],g-\mathbb E[g]\rangle=\mathbb E[fg]-\mathbb E[f]\mathbb E[g]=\sum_{S\ne\varnothing}\widehat f(S)\widehat g(S).$$

<a id="pdf-cdca27e1b5fd-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.99 -->
The Fourier weight on $S$ is $\widehat f(S)^2$. For Boolean $f$, Parseval makes these weights a probability distribution on subsets of $[n]$. The spectral sample $\mathcal S_f$ is defined by
$$\Pr[\mathcal S_f=S]=\widehat f(S)^2.$$
For $\operatorname{max}_2$, it is uniform on all four subsets of $[2]$; for $\operatorname{Maj}_3$, it is uniform on the four odd-cardinality subsets.

<a id="pdf-cdca27e1b5fd-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
Figure 1.1 depicts the Fourier weight distribution of $\operatorname{Maj}_3$: white circles have weight $0$, shaded circles have weight $1/4$. Subsets are stratified by cardinality, also called height, level, or degree.

<a id="pdf-cdca27e1b5fd-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.99 -->
For $0\le k\le n$,
$$W_k[f]=\sum_{\substack{S\subseteq[n]\\|S|=k}}\widehat f(S)^2.$$
For Boolean $f$,
$$W_k[f]=\Pr_{S\sim\mathcal S_f}[|S|=k].$$
The degree-$k$ part is $f_{=k}=\sum_{|S|=k}\widehat f(S)\chi_S$, and $W_k[f]=\|f_{=k}\|_2^2$. Analogously, $W_{>k}[f]=\sum_{|S|>k}\widehat f(S)^2$ and $f_{\le k}=\sum_{|S|\le k}\widehat f(S)\chi_S$.

<a id="pdf-cdca27e1b5fd-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.99 -->
## 1.5. Probability densities and convolution

<a id="pdf-cdca27e1b5fd-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.99 -->
This section writes the cube as $\mathbb F_2^n$. Real-valued Boolean functions include probability densities, which are important in combinatorics.

<a id="pdf-cdca27e1b5fd-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.99 -->
A probability density on $\mathbb F_2^n$ is a nonnegative function $\phi:\mathbb F_2^n\to\mathbb R_{\ge0}$ satisfying
$$\mathbb E_{x\sim\mathbb F_2^n}[\phi(x)]=1.$$
The associated distribution is $y\sim\phi$ with
$$\Pr_{y\sim\phi}[y=y_0]=\phi(y_0)\frac1{2^n}.$$

<a id="pdf-cdca27e1b5fd-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.99 -->
If $\phi$ is a density and $g:\mathbb F_2^n\to\mathbb R$, then
$$\mathbb E_{y\sim\phi}[g(y)]=\langle\phi,g\rangle=\mathbb E_{x\sim\mathbb F_2^n}[\phi(x)g(x)].$$

<a id="pdf-cdca27e1b5fd-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
For $A\subseteq\mathbb F_2^n$, $1_A$ is the indicator function. If $A\ne\varnothing$, the density of the uniform distribution on $A$ is
$$\phi_A=\frac{1_A}{\mathbb E[1_A]}.$$
We write $y\sim A$ for $y\sim\phi_A$. For $A=\{0\}$, $\phi_{\{0\}}$ equals $2^n$ at $0$ and $0$ elsewhere.

<a id="pdf-cdca27e1b5fd-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.99 -->
Every Fourier coefficient of $\phi_{\{0\}}$ is $1$:
$$\phi_{\{0\}}(y)=\sum_{S\subseteq[n]}\chi_S(y).$$

<a id="pdf-cdca27e1b5fd-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.99 -->
For $f,g:\mathbb F_2^n\to\mathbb R$,
$$(f*g)(x)=\mathbb E_y[f(y)g(x-y)]=\mathbb E_y[f(x-y)g(y)].$$
Since subtraction equals addition in $\mathbb F_2^n$, this is also
$$(f*g)(x)=\mathbb E_y[f(y)g(x+y)]=\mathbb E_y[f(x+y)g(y)].$$
On $\{-1,1\}^n$, $x+y$ is replaced by entrywise multiplication $x\circ y$. Convolution is associative and commutative.

<a id="pdf-cdca27e1b5fd-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.99 -->
If $\phi$ is a density and $g:\mathbb F_2^n\to\mathbb R$, then
$$(\phi*g)(x)=\mathbb E_{y\sim\phi}[g(x-y)]=\mathbb E_{y\sim\phi}[g(x+y)],$$
and $\mathbb E_{y\sim\phi}[g(y)]=(\phi*g)(0)$. If $\phi,\psi$ are densities, then $\phi*\psi$ is the density of $y+z$ for independent $y\sim\phi,z\sim\psi$.

<a id="pdf-cdca27e1b5fd-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.99 -->
For $f,g:\mathbb F_2^n\to\mathbb R$ and every $S\subseteq[n]$,
$$\widehat{f*g}(S)=\widehat f(S)\widehat g(S).$$

<a id="pdf-cdca27e1b5fd-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.99 -->
By the Fourier coefficient formula and the definition of convolution,
$$\widehat{f*g}(S)=\mathbb E_x\mathbb E_y[f(y)g(x-y)]\chi_S(x).$$
For each fixed $x$, $z=x-y$ is uniform, so this equals
$$\mathbb E_{y,z}[f(y)g(z)\chi_S(y+z)].$$
Using $\chi_S(y+z)=\chi_S(y)\chi_S(z)$ and independence gives
$$\mathbb E_y[f(y)\chi_S(y)]\,\mathbb E_z[g(z)\chi_S(z)]=\widehat f(S)\widehat g(S).$$

<a id="pdf-cdca27e1b5fd-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.99 -->
## 1.6. Highlight: Almost linear functions and the BLR Test

<a id="pdf-cdca27e1b5fd-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
A function $f:\mathbb F_2^n\to\mathbb F_2$ is linear if either equivalent condition holds:
1. $f(x+y)=f(x)+f(y)$ for all $x,y$;
2. $f(x)=a\cdot x=\sum_{i\in S}x_i$ for some $a\in\mathbb F_2^n$ and $S\subseteq[n]$.
Under the $\pm1$ encoding, linear functions are exactly the parity functions $\chi_S$.

<a id="pdf-cdca27e1b5fd-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.99 -->
Approximate linearity can mean either (1′) $f(x+y)=f(x)+f(y)$ for almost all pairs, or (2′) $f$ agrees with some parity on almost all inputs. The implication (2′) $\Rightarrow$ (1′) is robust; this section proves the converse.

<a id="pdf-cdca27e1b5fd-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.99 -->
Boolean-valued functions are $\varepsilon$-close if their distance is at most $\varepsilon$, and $\varepsilon$-far otherwise. For a nonempty property $P$,
$$\operatorname{dist}(f,P)=\min_{g\in P}\operatorname{dist}(f,g).$$
The function is $\varepsilon$-close to $P$ when this distance is at most $\varepsilon$.

<a id="pdf-cdca27e1b5fd-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
Given query access to $f:\mathbb F_2^n\to\mathbb F_2$:
1. Choose independent uniform $x,y\in\mathbb F_2^n$.
2. Query $f(x),f(y),f(x+y)$.
3. Accept iff $f(x)+f(y)=f(x+y)$.

<a id="pdf-cdca27e1b5fd-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.99 -->
If the BLR Test accepts $f:\mathbb F_2^n\to\mathbb F_2$ with probability at least $1-\varepsilon$, then $f$ is $\varepsilon$-close to being linear.

<a id="pdf-cdca27e1b5fd-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.99 -->
Encode the output as $\pm1\in\mathbb R$. Acceptance becomes $f(x)f(y)=f(x+y)$. The indicator of acceptance is
$$\frac12+\frac12f(x)f(y)f(x+y).$$
Therefore
$$1-\varepsilon=\frac12+\frac12\mathbb E_{x,y}[f(x)f(y)f(x+y)].$$
Conditioning on $x$ and using convolution gives
$$1-\varepsilon=\frac12+\frac12\langle f,f*f\rangle.$$$

<a id="pdf-cdca27e1b5fd-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.98 -->
Since the BLR test accepts with probability $1-\varepsilon$,
$$1-\varepsilon=\frac12+\frac12\sum_{S\subseteq[n]}\widehat f(S)^3.$$
Thus
$$1-2\varepsilon=\sum_{S\subseteq[n]}\widehat f(S)^3\le\max_{S\subseteq[n]}\widehat f(S)\sum_{S\subseteq[n]}\widehat f(S)^2=\max_{S\subseteq[n]}\widehat f(S),$$
where Parseval gives the final equality.

<a id="pdf-cdca27e1b5fd-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.99 -->
By Proposition 1.9, $\widehat f(S)=\langle f,\chi_S\rangle=1-2\operatorname{dist}(f,\chi_S)$. Hence some $S^*$ satisfies
$$1-2\varepsilon\le1-2\operatorname{dist}(f,\chi_{S^*}),$$
so $\operatorname{dist}(f,\chi_{S^*})\le\varepsilon$. Thus $f$ is $\varepsilon$-close to the linear function $\chi_{S^*}$.

<a id="pdf-cdca27e1b5fd-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.98 -->
For small $\varepsilon$, the stronger bound $\varepsilon/3$ is possible and sharp (Exercise 1.28). The BLR test identifies closeness to some parity but not which parity; determining that parity requires at least $n$ queries.

<a id="pdf-cdca27e1b5fd-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.99 -->
If $f:\mathbb F_2^n\to\{-1,1\}$ is $\varepsilon$-close to $\chi_S$, then for every $x$ the following two-query algorithm outputs $\chi_S(x)$ with probability at least $1-2\varepsilon$:
- choose uniform $y$;
- query $f(y)$ and $f(x+y)$;
- output $f(y)f(x+y)$.

<a id="pdf-cdca27e1b5fd-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.99 -->
Both $y$ and $x+y$ are uniform. Each differs from the corresponding parity value with probability at most $\varepsilon$. By the union bound, either error occurs with probability at most $2\varepsilon$. Otherwise,
$$f(y)f(x+y)=\chi_S(y)\chi_S(x+y)=\chi_S(x).$$

<a id="pdf-cdca27e1b5fd-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
## 1.7. Exercises and notes

<a id="pdf-cdca27e1b5fd-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.99 -->
Compute Fourier expansions for: (a) $\min_2$; (b) $\min_3$ and $\max_3$; (c) $1_{\{a\}}$ on $\mathbb F_2^n$; (d) $\phi_{\{a\}}$; (e) $\phi_{\{a,a+e_i\}}$; (f) a product distribution on $\{-1,1\}^n$ with coordinate means $\rho$; (g) the inner-product-mod-2 function; (h) equality; (i) not-all-equal; (j) selection; (k) mod 3; (l) OXR; (m) sortedness; (n) the hemi-icosahedron/Kushilevitz function; (o) $\operatorname{Maj}_5,\operatorname{Maj}_7$; (p) the complete quadratic function.

<a id="pdf-cdca27e1b5fd-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.80 -->
The page lists definitions of the equality function $\mathrm{Equ}_n$, the not-all-equal function $\mathrm{NAE}_n$, the selection function $\mathrm{Sel}$, $\mathrm{mod}_3$, XOR, the sortedness function $\mathrm{Sort}_4$, the hemi-icosahedron function $\mathrm{HI}$, the majority functions $\mathrm{Maj}_5$ and $\mathrm{Maj}_7$, and the complete quadratic function $\mathrm{CQ}_n$, together with the suggested interpolation hint for $\mathrm{HI}$.

<a id="pdf-cdca27e1b5fd-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.92 -->
Exercises 1.2–1.9 ask for counting Boolean functions with exactly one nonzero Fourier coefficient; proving that an odd support hypothesis forces all Fourier coefficients to be nonzero; proving the multilinear extension identity; bounding Fourier coefficients; proving uniqueness using Parseval; analyzing random Boolean functions; deriving the Boolean dual and the odd and even parts; and proving existence, uniqueness, integrality, and the change-of-encoding formula for multilinear representations over $\{0,1\}$.

<a id="pdf-cdca27e1b5fd-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.96 -->
Further exercises concern degree under affine transformations, dependence on input coordinates, granular Fourier spectra, Fourier-support bounds, Walsh–Hadamard matrices, and the Fast Walsh–Hadamard Transform. For $H_{2^n}$, show that the $(\gamma,x)$ entry is $(-1)^{\gamma\cdot x}$, that
$$2^{-n}H_{2^n}f=\widehat f,$$
and that the transform can be computed using $n2^n$ additions and subtractions.

<a id="pdf-cdca27e1b5fd-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.90 -->
Exercises 1.13–1.23 cover monotonicity of $L_p$ norms; means and variances; restrictions; variance/distance identities; independent-copy variance formulas; orthogonality of degree parts; Fourier-support questions; convolution; affine functions; total variation; collision probability; and $\chi^2$ distance.

<a id="pdf-cdca27e1b5fd-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->
The exercises continue with bounds on total variation from uniform, density $L_2$ bounds, direct associativity/commutativity of convolution, query complexity of identifying a linear function, sharper BLR rejection bounds, and four-query tests for affine functions.

<a id="pdf-cdca27e1b5fd-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.99 -->
Exercise 1.30 studies permutation isomorphism of Boolean functions: prove the Fourier transformation rule $\widehat{f^\pi}(S)=\widehat f(\pi^{-1}(S))$; establish well-definedness and canonicity of the iterative lexicographic canonical form; analyze its running time; and extend the results to signed coordinate permutations.

<a id="pdf-cdca27e1b5fd-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.88 -->
The notes trace the Fourier expansion of real-valued Boolean functions to Walsh, who introduced a complete orthonormal basis for $L^2([0,1])$ consisting of $\pm1$-valued functions constant on dyadic intervals. They discuss the ordering introduced by Paley and the Walsh basis functions defined using Rademacher functions.

<a id="pdf-cdca27e1b5fd-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.99 -->
The historical notes continue: Walsh functions were studied in relation to trigonometric and Haar bases; later work treated Fourier characters symmetrically by set size and established hypercontractivity. Boolean Fourier coefficients were applied to switching functions and classification problems, and Fourier–Walsh analysis became established in the 1960s–1970s. The modern theoretical-computer-science viewpoint was advanced by Kahn, Kalai, and Linial.

<a id="pdf-cdca27e1b5fd-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.99 -->
The original BLR linearity-test analysis was combinatorial; the proof here is the analytic argument of Bellare, Coppersmith, Håstad, Kiwi, and Sudan, with related ideas already present in Roth’s work over cyclic groups.

<a id="pdf-cdca27e1b5fd-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.99 -->
The notes cite later improvements to the BLR analysis and identify the origins of the sortedness function, hemi-icosahedron function, and fast Fourier-transform algorithm.
