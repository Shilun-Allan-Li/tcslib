<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 6c10bfcc80801303a586f415265bdc336a4336277b45067f4b9b852d23df2f63 -->

<a id="pdf-6c10bfcc8080-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# Chapter 6: Pseudorandomness and $\mathbb{F}_2$-polynomials

<a id="pdf-6c10bfcc8080-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.85 -->
Overview: pseudorandomness notions for Boolean functions (properties of a fixed function characteristic of random ones), deterministic small-support pseudorandom densities with derandomization applications, and interplay between the real-polynomial and $\mathbb{F}_2$-polynomial representations of $f:\{0,1\}^n\to\{0,1\}$.

<a id="pdf-6c10bfcc8080-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
## 6.1. Notions of pseudorandomness

<a id="pdf-6c10bfcc8080-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.85 -->
A truly random $f:\{-1,1\}^n\to\{-1,1\}$ has all Fourier coefficients very small (Exercise 5.8). Switching to $f:\{-1,1\}^n\to\{0,1\}$, $\widehat{f}(\emptyset)$ is instead close to $1/2$, motivating the following generalization.

<a id="pdf-6c10bfcc8080-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.97 -->
**Proposition 6.1.** Let $n>1$ and let $f:\{-1,1\}^n\to\{0,1\}$ be a $p$-biased random function: each $f(x)$ is $1$ with probability $p$ and $0$ with probability $1-p$, independently for all $x\in\{-1,1\}^n$. Then except with probability at most $2^{-n}$, all of the following hold:
$$|\widehat{f}(\emptyset)-p|\le 2\sqrt{n}\,2^{-n/2},\qquad \forall\, S\ne\emptyset:\ |\widehat{f}(S)|\le 2\sqrt{n}\,2^{-n/2}.$$

<a id="pdf-6c10bfcc8080-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.95 -->
**Proof.** We have $\widehat{f}(S)=\sum_x \tfrac{1}{2^n}x^S f(x)$, where the random variables $f(x)$ are independent. If $S=\emptyset$, then the coefficients $\tfrac{1}{2^n}x^S$ sum to $1$ and the mean of $\widehat{f}(S)$ is $p$; otherwise the coefficients sum to $0$ and the mean of $\widehat{f}(S)$ is $0$. Either way we may apply the Hoeffding bound to conclude that $\Pr[\,|\widehat{f}(S)-\mathbb{E}[\widehat{f}(S)]|\ge t\,]\le 2\exp(-t^2\cdot 2^{n-1})$ for any $t>0$. Selecting $t=2\sqrt{n}\,2^{-n/2}$, the above bound is $2\exp(-2n)\le 4^{-n}$. The result follows by taking a union bound over all $S\subseteq[n]$. $\square$

<a id="pdf-6c10bfcc8080-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
**Definition 6.2.** $f:\{-1,1\}^n\to\mathbb{R}$ is $\epsilon$-regular (also called $\epsilon$-uniform) if $|\widehat{f}(S)|\le\epsilon$ for all $S\ne\emptyset$.

<a id="pdf-6c10bfcc8080-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.97 -->
**Remark 6.3.** By Exercise 3.9, every function $f$ is $\epsilon$-regular for $\epsilon=\lVert f\rVert_1$; for $f:\{-1,1\}^n\to[-1,1]$ attention is restricted to $\epsilon\le 1$.

<a id="pdf-6c10bfcc8080-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.96 -->
**Example 6.4.** A random $p$-biased function is $\big(2\sqrt{n}\,2^{-n/2}\big)$-regular w.h.p. (Prop. 6.1). $f$ is $0$-regular iff it is constant. If $A\subseteq\mathbb{F}_2^n$ is an affine subspace of codimension $k$ then $1_A$ is $2^{-k}$-regular (Prop. 3.12). For $n$ even, the inner-product-mod-2 and complete quadratic functions $IP_n, CQ_n:\mathbb{F}_2^n\to\{0,1\}$ are $2^{-n/2-1}$-regular (Exercise 1.1). Parity functions $\chi_S:\{-1,1\}^n\to\{-1,1\}$ are not $\epsilon$-regular for any $\epsilon<1$ (except $S=\emptyset$). By Exercise 5.21, $Maj_n$ is $\tfrac{1}{\sqrt n}$-regular.

<a id="pdf-6c10bfcc8080-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
**Definition 6.5.** A probability density $\phi:\mathbb{F}_2^n\to\mathbb{R}_{\ge 0}$ that is $\epsilon$-regular is called an $\epsilon$-biased density. Equivalently, $\phi$ is $\epsilon$-biased iff $\big|\mathbb{E}_{x\sim\phi}[\chi_\gamma(x)]\big|\le\epsilon$ for all $\gamma\in\mathbb{F}_2^n\setminus\{0\}$ (i.e. "at most $\epsilon$-biased on subspaces"). The marginal on any coordinate set $J\subseteq[n]$ is also $\epsilon$-biased. If $\phi=1_A/\mathbb{E}[1_A]$ for some $A\subseteq\mathbb{F}_2^n$, then $A$ is called an $\epsilon$-biased set.

<a id="pdf-6c10bfcc8080-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.85 -->
**Example 6.6.** Every probability density is $1$-biased. The uniform distribution on $\mathbb{F}_2^n$ (density $\phi\equiv 1$) is the only $0$-biased density. Uniform distributions on smaller affine subspaces are maximally biased: if $A\subseteq\mathbb{F}_2^n$ is an affine subspace of dimension $<n$, then $\phi_A$ is not $\epsilon$-biased for any $\epsilon<1$ (Prop. 3.12). If $E=\{(0,\dots,0),(1,\dots,1)\}$, then $E$ is a $1/2$-biased set (Exercise 1.1(h)).

<a id="pdf-6c10bfcc8080-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.85 -->
Introduces a combinatorial property roughly equivalent to $\epsilon$-regularity: by Exercise 1.29, $\lVert\widehat{f}\rVert_4^4$ has an equivalent non-Fourier formula (continued on the next page).

<a id="pdf-6c10bfcc8080-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.85 -->
The non-Fourier formula is $\lVert\widehat{f}\rVert_4^4=\mathbb{E}_{x,y,z}[f(x)f(y)f(z)f(x+y+z)]$. Informally, $f$ is regular iff this is not much larger than $\mathbb{E}[f]^4=\mathbb{E}_{x,y,z,w}[f(x)f(y)f(z)f(w)]$.

<a id="pdf-6c10bfcc8080-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.92 -->
**Proposition 6.7.** Let $f:\mathbb{F}_2^n\to\mathbb{R}$. Then:
(1) If $f$ is $\epsilon$-regular, then $\lVert\widehat{f}\rVert_4^4-\mathbb{E}[f]^4\le\epsilon^2\cdot\mathrm{Var}[f]$.
(2) If $f$ is not $\epsilon$-regular, then $\lVert\widehat{f}\rVert_4^4-\mathbb{E}[f]^4\ge\epsilon^4$.

<a id="pdf-6c10bfcc8080-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
**Proof.** Using $\mathbb{E}[f]^4=\widehat{f}(\emptyset)^4$ and $\sum_{S\ne\emptyset}\widehat{f}(S)^2=\mathrm{Var}[f]$: if $f$ is $\epsilon$-regular then $\lVert\widehat{f}\rVert_4^4-\mathbb{E}[f]^4=\sum_{S\ne\emptyset}\widehat{f}(S)^4\le\max_{S\ne\emptyset}\{\widehat{f}(S)^2\}\cdot\sum_{S\ne\emptyset}\widehat{f}(S)^2\le\epsilon^2\cdot\mathrm{Var}[f]$. If $f$ is not $\epsilon$-regular then $|\widehat{f}(T)|\ge\epsilon$ for some $T\ne\emptyset$, so $\sum_{S\ne\emptyset}\widehat{f}(S)^4\ge\widehat{f}(T)^4\ge\epsilon^4$. $\square$

<a id="pdf-6c10bfcc8080-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.85 -->
$\epsilon$-regularity (all nonempty-set coefficients small) is strong. As with the $\tfrac{2}{\pi}$ Theorem (Ch. 5.4), one may instead require only $|\widehat{f}(i)|\le\epsilon$ for all $i\in[n]$ (for monotone $f$, equivalently $\mathrm{Inf}_i[f]\le\epsilon$). This gives two weaker notions: all low-degree Fourier coefficients small, and all influences small; the second is treated first.

<a id="pdf-6c10bfcc8080-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.85 -->
A random $f:\{-1,1\}^n\to\{-1,1\}$ does not have all influences small ($\mathbb{E}[\mathrm{Inf}_i[f]]=1/2$, Exercise 2.12), but for any $\delta>0$ its $(1-\delta)$-stable influences are exponentially small (Def. 2.52).

<a id="pdf-6c10bfcc8080-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.97 -->
**Fact 6.8.** Fix $\delta\in[0,1]$ and let $f:\{-1,1\}^n\to\{-1,1\}$ be randomly chosen. Then for any $i\in[n]$, $\mathbb{E}\big[\mathrm{Inf}_i^{(1-\delta)}[f]\big]=\dfrac{(1-\delta/2)^n}{2-\delta}$.

<a id="pdf-6c10bfcc8080-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.92 -->
**Definition 6.9.** Motivated by "no notable coordinates" (cf. Prop. 2.54): $f:\{-1,1\}^n\to\mathbb{R}$ has $(\epsilon,\delta)$-small stable influences, or no $(\epsilon,\delta)$-notable coordinates, if $\mathrm{Inf}_i^{(1-\delta)}[f]\le\epsilon$ for all $i\in[n]$. The condition strengthens as $\epsilon,\delta$ decrease; when $\delta=0$ (so $\mathrm{Inf}_i[f]\le\epsilon$) we say $f$ has $\epsilon$-small influences.

<a id="pdf-6c10bfcc8080-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.90 -->
**Example 6.10.** Besides random functions, important examples of Boolean-valued functions with no notable coordinates are constants, majority, and large parities.

<a id="pdf-6c10bfcc8080-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
Examples contrasting influences with stable influences. Constant functions have $(0,0)$-small stable influences (indeed, they are the only functions with $0$-small influences); $\mathrm{Maj}_n$ has $\tfrac{1}{\sqrt n}$-small influences. For a parity $\chi_S$ ($S\neq\emptyset$), $\mathrm{Inf}_i^{(1-\delta)}[\chi_S]=(1-\delta)^{|S|-1}$ for $i\in S$ and $0$ otherwise, so $\chi_S$ has $((1-\delta)^{|S|-1},\delta)$-small stable influences, hence $(\epsilon,\delta)$-small ones whenever $|S|\ge \ln(e/\epsilon)/\delta$. The prototypical function lacking small stable influences is an unbiased $k$-junta: $\mathrm{Var}[f]=1$, so (Fact 2.53) the sum of its $(1-\delta)$-stable influences is at least $(1-\delta)^{k-1}$, whence $\mathrm{Inf}_i^{(1-\delta)}[f]\ge (1-\delta)^{k-1}/k$ for at least one $i$; thus $f$ does not have $((1-\delta)^k/k,\delta)$-small stable influences for any $\delta\in(0,1)$. A somewhat different example is $f(x)=x_0\,\mathrm{Maj}_n(x_1,\dots,x_n)$, which has $\mathrm{Inf}_0^{(1-\delta)}[f]\ge 1-\sqrt\delta$ (Exercise 6.5(d)). Returning to $|\hat f(i)|\le\epsilon$ for all $i$: this is $(\epsilon,1)$-regularity, equivalently $f^{\le 1}$ being $\epsilon$-regular, equivalently $|\langle f,\pm\chi_i\rangle|\le\epsilon$ for all $i$ (at most $\epsilon$ correlation with every dictator).

<a id="pdf-6c10bfcc8080-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
**Definition 6.11.** $f:\{-1,1\}^n\to\mathbb R$ is $(\epsilon,k)$-regular if $|\hat f(S)|\le\epsilon$ for all $0<|S|\le k$; equivalently, $f^{\le k}$ is $\epsilon$-regular. For $k=n$ (or $k=\infty$) this coincides with $\epsilon$-regularity. An $(\epsilon,k)$-regular probability density $\phi:\mathbb F_2^n\to\mathbb R_{\ge0}$ is called $(\epsilon,k)$-wise independent.

<a id="pdf-6c10bfcc8080-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.85 -->
Two rough characterizations of $(\epsilon,k)$-regularity, with exponential losses in $k$ (acceptable when $k$ is constant): (i) $f$ is $(\epsilon,k)$-regular iff fixing $k$ input coordinates changes $f$'s mean by at most $O(\epsilon)$; (ii) $f$ has $O(\epsilon)$ covariance with every $k$-junta.

<a id="pdf-6c10bfcc8080-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.92 -->
**Proposition 6.12.** Let $f:\{-1,1\}^n\to\mathbb R$, $\epsilon\ge0$, $k\in\mathbb N$. (1) If $f$ is $(\epsilon,k)$-regular, any restriction of at most $k$ coordinates changes $f$'s mean by at most $2^k\epsilon$. (2) If $f$ is not $(\epsilon,k)$-regular, some restriction to at most $k$ coordinates changes $f$'s mean by more than $\epsilon$.

<a id="pdf-6c10bfcc8080-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.85 -->
**Proposition 6.13.** Let $f:\{-1,1\}^n\to\mathbb R$, $\epsilon\ge0$, $k\in\mathbb N$. (Parts (1)–(2) stated on the following page.)

<a id="pdf-6c10bfcc8080-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.88 -->
**Proposition 6.13 (continued).** (1) If $f$ is $(\epsilon,k)$-regular then $\mathrm{Cov}[f,h]\le\|\hat h\|_1\,\epsilon$ for any $h:\{-1,1\}^n\to\mathbb R$ with $\deg(h)\le k$; in particular $\mathrm{Cov}[f,h]\le 2^{k/2}\epsilon$ for any $k$-junta $h:\{-1,1\}^n\to\{-1,1\}$. (2) If $f$ is not $(\epsilon,k)$-regular then $\mathrm{Cov}[f,h]>\epsilon$ for some $k$-junta $h:\{-1,1\}^n\to\{-1,1\}$.

<a id="pdf-6c10bfcc8080-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
Proposition 6.12 is proved below; the proof of Proposition 6.13 is left to the exercises.

<a id="pdf-6c10bfcc8080-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.85 -->
**Proof of Proposition 6.12.** (1) Let $f$ be $(\epsilon,k)$-regular, $J\subseteq[n]$, $z\in\{-1,1\}^J$, $|J|\le k$. By Exercise 1.15, $\mathrm E[f_{J\mid z}]=\hat f(\emptyset)+\sum_{\emptyset\neq T\subseteq J}\hat f(T)\,z^T$; each of the at most $2^k$ terms has $|\hat f(T)|\le\epsilon$, so the mean changes by at most $2^k\epsilon$. (2) Suppose $|\hat f(J)|>\epsilon$ with $0<|J|\le k$, and set $h(z)=\sum_{\emptyset\neq T\subseteq J}\hat f(T)\,z^T$. Then $\|h\|_\infty=\|h\chi_J\|_\infty\ge|\mathrm E[h\chi_J]|=|\hat h(J)|=|\hat f(J)|>\epsilon$, so some restriction changes the mean by more than $\epsilon$. $\square$

<a id="pdf-6c10bfcc8080-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.92 -->
**Corollary 6.14.** For $f:\{-1,1\}^n\to\mathbb R$ the following are equivalent: (1) $f$ is $(0,k)$-regular; (2) every restriction of at most $k$ coordinates leaves $f$'s mean unchanged; (3) $\mathrm{Cov}[f,h]=0$ for every $k$-junta $h:\{-1,1\}^n\to\{-1,1\}$. If $f$ is a probability density, (3) is equivalent to $\mathrm E_{x\sim f}[h(x)]=\mathrm E[h]$ for every such $k$-junta.

<a id="pdf-6c10bfcc8080-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.92 -->
**Definition 6.15.** A $(0,k)$-regular $f:\{-1,1\}^n\to\{-1,1\}$ is called $k$th-order correlation immune; if additionally unbiased, it is $k$-resilient. A $(0,k)$-regular probability density $\phi:\mathbb F_2^n\to\mathbb R_{\ge0}$ is called $k$-wise independent.

<a id="pdf-6c10bfcc8080-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.80 -->
**Example 6.16.** Any parity $\chi_S$ with $|S|=k+1$ is $k$-resilient; more generally so is $\chi_S\cdot g$ for any $g:\{-1,1\}^n\to\{-1,1\}$ not depending on the coordinates in $S$. A correlation-immune function that is not resilient: $h:\{-1,1\}^{3m}\to\{-1,1\}$ with $h=\chi_{\{1,\dots,2m\}}\wedge\chi_{\{m+1,\dots,3m\}}$ (continued next page).

<a id="pdf-6c10bfcc8080-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.88 -->
**Example 6.16 (continued).** This $h$ is not unbiased (True on a $1/4$-fraction of inputs), but its bias does not change unless at least $2m$ input bits are fixed; hence $h$ is $(2m-1)$th-order correlation immune.

<a id="pdf-6c10bfcc8080-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.85 -->
Figure 6.1 compares the notions of pseudorandomness, with arrows going from stronger notions to strictly weaker ones. Precise quantitative statements, separating counterexamples, and the reasons these notions essentially coincide for monotone functions are in Exercise 6.5.

<a id="pdf-6c10bfcc8080-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.90 -->
**§6.2. $\mathbb F_2$-polynomials.** Shifting from real polynomial representations to representations over the field $\mathbb F_2$, with False/True encoded as $0,1\in\mathbb F_2$; there the operations $+$ and $\cdot$ correspond to logical XOR and logical AND.

<a id="pdf-6c10bfcc8080-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.92 -->
**Example 6.17.** The parity (XOR) function $\chi_{[n]}$: over the reals with $\pm1$ encoding, $\chi_{[n]}:\{-1,1\}^n\to\{-1,1\}$ has representation $\chi_{[n]}(x)=x_1x_2\cdots x_n$ (degree $n$); over $\mathbb F_2$ with $0,1$ encoding, $\chi_{[n]}:\mathbb F_2^n\to\mathbb F_2$ has representation $\chi_{[n]}(x)=x_1+x_2+\cdots+x_n$ (degree $1$).

<a id="pdf-6c10bfcc8080-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.90 -->
Every $f:\mathbb F_2^n\to\mathbb F_2$ admits a multilinear polynomial representation by interpolation (as in Chapter 1.2). For $a\in\mathbb F_2^n$, the indicator $1_{\{a\}}:\mathbb F_2^n\to\mathbb F_2$ is, by equation (6.1), $1_{\{a\}}(x)=\prod_{i:\,a_i=1}x_i\;\prod_{i:\,a_i=0}(1-x_i)$.

<a id="pdf-6c10bfcc8080-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
Interpolation gives every $f:\mathbb{F}_2^n\to\mathbb{F}_2$ a multilinear expression $f(x)=\sum_{a\in\mathbb{F}_2^n} f(a)\,1_{\{a\}}(x)$ (6.2) (using $x_i^2=x_i$ over $\mathbb{F}_2$). Simplified, $f(x)=\sum_{S\subseteq[n]} c_S\,x^S$ (6.3) with $x^S=\prod_{i\in S}x_i$ and $c_S\in\mathbb{F}_2$; this is the **F2-polynomial representation** of $f$. Example (6.4): parity $\chi_{[3]}$, interpolated, reduces to $x_1+x_2+x_3$ (its integer interpolation being $x_1+x_2+x_3-2(x_1x_2+x_1x_3+x_2x_3)+4x_1x_2x_3$).

<a id="pdf-6c10bfcc8080-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->
**Proposition 6.18.** Every $f:\mathbb{F}_2^n\to\mathbb{F}_2$ has a unique F2-polynomial representation as in (6.3). Uniqueness follows by counting: there are $2^{2^n}$ functions $\mathbb{F}_2^n\to\mathbb{F}_2$ and equally $2^{2^n}$ choices of coefficient tuples $(c_S)_{S\subseteq[n]}$.

<a id="pdf-6c10bfcc8080-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.96 -->
**Example 6.19.** $\mathrm{AND}_n(x)=x_1 x_2\cdots x_n$. The inner-product-mod-2 function has degree-2 representation $\mathrm{IP}_{2n}(x_1,\dots,x_n,y_1,\dots,y_n)=x_1y_1+x_2y_2+\cdots+x_ny_n$.

<a id="pdf-6c10bfcc8080-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.97 -->
**Definition 6.20.** The **F2-degree** $\deg_{\mathbb{F}_2}(f)$ of $f:\{\text{False},\text{True}\}^n\to\{\text{False},\text{True}\}$ is the degree of its F2-polynomial representation; $\deg(f)$ is reserved for the degree of $f$'s Fourier expansion.

<a id="pdf-6c10bfcc8080-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.94 -->
**Proposition 6.21.** If $f:\mathbb{F}_2^n\to\mathbb{F}_2$ has representation $f(x)=\sum_{S\subseteq[n]}c_S x^S$, then $c_S=\sum_{x:\,\mathrm{supp}(x)\subseteq S} f(x)$.

<a id="pdf-6c10bfcc8080-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.95 -->
**Corollary 6.22.** For $f:\{\text{False},\text{True}\}^n\to\{\text{False},\text{True}\}$, $\deg_{\mathbb{F}_2}(f)=n$ iff $f(x)=\text{True}$ for an odd number of inputs $x$.

<a id="pdf-6c10bfcc8080-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.90 -->
Proposition 6.21 is Exercise 6.10; Corollary 6.22 is the case $S=[n]$, giving $c_{[n]}=\sum_x f(x)$, also visible from the $x_1x_2\cdots x_n$ monomial in the interpolation (6.1),(6.2).

<a id="pdf-6c10bfcc8080-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.85 -->
The F2-representation can be obtained from the R-representation. If $p(x)$ is $f$'s Fourier expansion ($\pm1$ encoding), then $q(x)=\tfrac12-\tfrac12 p(1-2x_1,\dots,1-2x_n)$ is the unique R-multilinear representation under the $0/1$ encoding (Exercise 1.9), and equals the interpolation carried out over $\mathbb{Z}$; reducing $q$'s integer coefficients mod 2 yields the F2-representation. Example: $\chi_{[3]}$ has $\pm1$-representation $x_1x_2x_3$; $q(x)=\tfrac12\bigl(1-(1-2x_1)(1-2x_2)(1-2x_3)\bigr)$ expands to (6.4) and reduces mod 2 to $x_1+x_2+x_3$.

<a id="pdf-6c10bfcc8080-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
This transformation can only decrease degree: forming $q(x)=\tfrac12-\tfrac12 p(1-2x_1,\dots,1-2x_n)$ preserves degree (except $p\equiv1\Rightarrow q\equiv0$; Exercise 1.11), and reducing mod 2 cannot increase it.

<a id="pdf-6c10bfcc8080-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.96 -->
**Proposition 6.23.** For $f:\{-1,1\}^n\to\{-1,1\}$, $\deg_{\mathbb{F}_2}(f)\le\deg(f)$.

<a id="pdf-6c10bfcc8080-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.86 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ is $k$-resilient ($\hat f(S)=0$ for all $|S|\le k$), let $g=f\cdot\chi_{[n]}$, so $\hat g(S)=\hat f([n]\setminus S)$ and $\deg(g)\le n-k-1$; by Proposition 6.23, $\deg_{\mathbb{F}_2}(g)\le n-k-1$. Over $\mathbb{F}_2$, $g=x_1+\cdots+x_n+f$, so $\deg_{\mathbb{F}_2}(g)=\deg_{\mathbb{F}_2}(f)$ (unless $f$ is parity or its negation), giving $\deg_{\mathbb{F}_2}(f)\le n-k-1$.

<a id="pdf-6c10bfcc8080-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.95 -->
**Proposition 6.24.** If $f:\{-1,1\}^n\to\{-1,1\}$ is $k$-resilient with $k<n-1$, then $\deg_{\mathbb{F}_2}(f)\le n-k-1$.

<a id="pdf-6c10bfcc8080-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.93 -->
**Siegenthaler's Theorem.** Proposition 6.24 holds; moreover if $f$ is merely $k$th-order correlation immune, then $\deg_{\mathbb{F}_2}(f)\le n-k$ (for $k<n$). Due to Siegenthaler (stream-cipher motivation, notes in Section 6.6); the proof does not use Fourier analysis.

<a id="pdf-6c10bfcc8080-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.90 -->
**Proof.** Take a monomial $x^J$ of maximal degree $d=\deg_{\mathbb{F}_2}(f)$ in $f$'s F2-representation; assume $d>1$ (else done). [continues on next page]

<a id="pdf-6c10bfcc8080-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.90 -->
**Proof (cont.).** Apply an arbitrary restriction to the $n-d$ coordinates outside $J$, forming a function $g:\mathbb{F}_2^J\to\mathbb{F}_2$; the monomial $x^J$ still appears in $g$'s $\mathbb{F}_2$-polynomial representation, so by Corollary 6.22, $g$ is $1$ for an odd number of inputs.

*Prop. 6.24 case:* a $k$-resilient $f$ is unbiased, but $g$ is $1$ for an odd number of inputs so it cannot be unbiased (since $2^{d-1}$ is even for $d>1$); thus the restriction changed the bias, forcing $n-d>k$, i.e. $d\le n-k-1$.

*Correlation-immune case:* picking one further input coordinate gives subfunctions $g_0,g_1$; since $g$ has an odd number of $1$'s, one of them has an odd number and the other an even number, so $g_0,g_1$ have different biases and one must differ from $f$'s. Hence $n-d+1>k$, i.e. $d\le n-k$. $\square$

<a id="pdf-6c10bfcc8080-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.94 -->
**Theorem 6.25.** If $f:\{-1,1\}^n\to\{-1,1\}$ is $k$th-order correlation immune but not $k$-resilient (i.e. $\mathbb{E}[f]\ne0$), then $k+1\le\tfrac23 n$.

<a id="pdf-6c10bfcc8080-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.93 -->
Proof is Exercise 6.14, via the Fourier expansion (not the F2-representation). Both Siegenthaler's Theorem and Theorem 6.25 can be sharp (Exercise 6.15).

<a id="pdf-6c10bfcc8080-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->
**6.3. Constructions of various pseudorandom functions.** Constructions of Boolean functions with strong pseudorandomness, starting with bent functions.

<a id="pdf-6c10bfcc8080-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.96 -->
**Definition 6.26.** $f:\mathbb{F}_2^n\to\{-1,1\}$ with $n$ even is **bent** if $|\hat f(\gamma)|=2^{-n/2}$ for all $\gamma\in\mathbb{F}_2^n$.

<a id="pdf-6c10bfcc8080-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.85 -->
Bent functions are $2^{-n/2}$-regular and are maximally regular / maximally distant from the affine class $\{\pm\chi_\gamma:\gamma\in\mathbb{F}_2^n\}$: since $\sum_\gamma \hat f(\gamma)^2=1$, some $|\hat f(\gamma)|\ge 2^{-n/2}$, so bentness attains the minimum possible maximum coefficient.

<a id="pdf-6c10bfcc8080-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.96 -->
The canonical bent function is inner-product-mod-2 $\mathrm{IP}_n(x)=\chi\bigl(x_1x_{n/2+1}+x_2x_{n/2+2}+\cdots+x_{n/2}x_n\bigr)$, where $\chi(b)=(-1)^b$. For $n=2$ this is $\mathrm{AND}_2=\tfrac12+\tfrac12 x_1+\tfrac12 x_2-\tfrac12 x_1x_2$, bent by inspection; general bentness follows from a fact in Exercise 6.16.

<a id="pdf-6c10bfcc8080-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
**Chapter 6. Pseudorandomness and $\mathbb{F}_2$-polynomials** (p. 152).

<a id="pdf-6c10bfcc8080-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.94 -->
**Proposition 6.27.** If $f:\mathbb{F}_2^n\to\{-1,1\}$ and $g:\mathbb{F}_2^{n_0}\to\{-1,1\}$ are bent, then $f\oplus g:\mathbb{F}_2^{n+n_0}\to\{-1,1\}$ defined by $(f\oplus g)(x,x_0)=f(x)g(x_0)$ is also bent.

<a id="pdf-6c10bfcc8080-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
Introduces the complete quadratic bent function $CQ_n(x)=\chi\!\big(\sum_{1\le i<j\le n} x_i x_j\big)$ (Exercise 1.1), noting it is essentially the "same" example as the inner-product function, explained next.

<a id="pdf-6c10bfcc8080-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.94 -->
**Proposition 6.28.** If $f:\mathbb{F}_2^n\to\{-1,1\}$ is bent, then $\chi_\gamma\cdot f$ is bent for any $\gamma\in\mathbb{F}_2^n$, and $f\circ M$ is bent for any invertible linear $M:\mathbb{F}_2^n\to\mathbb{F}_2^n$.

<a id="pdf-6c10bfcc8080-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.90 -->
**Proof.** Multiplying by $\pm 1$ preserves bentness; both $\chi_\gamma\cdot f$ and $f\circ M$ have the same Fourier coefficients as $f$ up to a permutation (Exercise 3.1). $\square$

<a id="pdf-6c10bfcc8080-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.82 -->
Claims $CQ_n$ arises from $f=IP_n$ via Proposition 6.28. For $n=4$: $\sum_{1\le i<j\le 4}x_ix_j=(x_1+x_3)(x_2+x_3)+(x_1+x_3)x_4+x_2+x_3+x_4$ over $\mathbb{F}_2$, giving $CQ_4(x)=IP_4(Mx)\cdot\chi_{(0,0,1,0)}(x)$ with the invertible matrix $M=\begin{psmallmatrix}1&0&1&0\\1&1&1&0\\0&1&1&0\\0&0&0&1\end{psmallmatrix}$. General case: Exercise 6.20. Every bent $f$ with $\deg_{\mathbb{F}_2}(f)\le 2$ arises this way from the mod-2 inner product (Exercise 6.19). Full classification of bent functions is open.

<a id="pdf-6c10bfcc8080-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.80 -->
**Proposition 6.29.** Define $f:\mathbb{F}_2^{2n}\to\{-1,1\}$ by $f(x,y)=IP_{2n}(x,y)\,g(y)$, where $g:\{-1,1\}^n\to\{-1,1\}$ is arbitrary. Then $f$ is bent.

<a id="pdf-6c10bfcc8080-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.92 -->
**Proof.** We will think of $y\in\widehat{\mathbb{F}_2^n}$, so $IP_{2n}(x,y)=\chi_y(x)$; writing a generic $\gamma=(\gamma_1,\gamma_2)$,
$$\widehat{f}(\gamma)=\mathbb{E}_{x,y}\big[\chi_y(x)g(y)\chi_{(\gamma_1,\gamma_2)}(x,y)\big]=\mathbb{E}_y\big[g(y)\chi_{\gamma_2}(y)\,\mathbb{E}_x[\chi_{y+\gamma_1}(x)]\big]$$
$$=\mathbb{E}_y\big[g(y)\chi_{\gamma_2}(y)\mathbf{1}\{y+\gamma_1=0\}\big]=2^{-n}g(\gamma_1)\chi_{\gamma_2}(\gamma_1)=\pm 2^{-n}.\quad\square$$

<a id="pdf-6c10bfcc8080-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.88 -->
Motivates explicit small $\varepsilon$-biased sets for derandomization: replacing $n$ uniform random bits by drawing $x$ from an $\varepsilon$-biased density supported on a deterministically constructible (multi)set $A$ of size $2^\ell$, using only $\ell$ random bits.

<a id="pdf-6c10bfcc8080-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**6.3. Constructions of various pseudorandom functions** (p. 153).

<a id="pdf-6c10bfcc8080-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
Setup: for $\ell\in\mathbb{N}^+$ there is a finite field $\mathbb{F}_{2^\ell}$ with $2^\ell$ elements, with an explicit representation computable in time $2^{O(\ell)}$ (even $\mathrm{poly}(\ell)$ deterministically). Elements $x\in\mathbb{F}_{2^\ell}$ are encoded by distinct $\ell$-bit vectors via a **linear** map $\mathrm{enc}:\mathbb{F}_{2^\ell}\to\mathbb{F}_2^\ell$: $\mathrm{enc}(0)=(0,\dots,0)$ and $\mathrm{enc}(x+y)=\mathrm{enc}(x)+\mathrm{enc}(y)$.

<a id="pdf-6c10bfcc8080-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.93 -->
**Theorem 6.30.** There is a deterministic algorithm that, given $n\ge 1$ and $0<\varepsilon\le 1/2$, runs in $\mathrm{poly}(n/\varepsilon)$ time and outputs a multiset $A\subseteq\mathbb{F}_2^n$ of cardinality at most $16(n/\varepsilon)^2$ such that $\varphi_A$ is an $\varepsilon$-biased density.

<a id="pdf-6c10bfcc8080-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.86 -->
**Proof.** Reduce to obtaining size $(n/\varepsilon)^2$ assuming $\varepsilon=2^{-t}$ and $n=2^\ell-t$ (powers of 2). Draw $y\sim\varphi$ using $2\ell$ random bits by picking $r,s\in\mathbb{F}_{2^\ell}$ independent uniform, and setting $y_i=\langle \mathrm{enc}(r^i),\mathrm{enc}(s)\rangle$ (inner product in $\mathbb{F}_2^\ell$) for $i\in[n]$; $A$ is the multiset of the $2^{2\ell}=(n/\varepsilon)^2$ outcomes. Fix $\gamma\in\mathbb{F}_2^n\setminus\{0\}$; by linearity of $\mathrm{enc}$,
$$\langle\gamma,y\rangle=\sum_{i=1}^n \gamma_i\langle \mathrm{enc}(r^i),\mathrm{enc}(s)\rangle=\big\langle \mathrm{enc}\big(\textstyle\sum_i\gamma_i r^i\big),\mathrm{enc}(s)\big\rangle,$$
so
$$\mathbb{E}[\chi_\gamma(y)]=\mathbb{E}_r\,\mathbb{E}_s\big[(-1)^{\langle \mathrm{enc}(p_\gamma(r)),\mathrm{enc}(s)\rangle}\big]\quad(6.5),$$
where $p_\gamma:\mathbb{F}_{2^\ell}\to\mathbb{F}_{2^\ell}$ is $a\mapsto\gamma_1 a+\gamma_2 a^2+\cdots+\gamma_n a^n$, of degree $\le n$ and nonzero (as $\gamma\ne 0$), hence with at most $n$ roots. If $r$ is a root, $\mathrm{enc}(p_\gamma(r))=0$ and the inner expectation is $1$; otherwise it is $0$ (Fact 1.7). Thus $\mathbb{E}[\chi_\gamma(y)]\le \Pr[r\text{ is a root of }p_\gamma]\le n/2^\ell=2^{-t}$, even stronger than required. $\square$

<a id="pdf-6c10bfcc8080-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.88 -->
The $O(n/\varepsilon)^2$ bound is near-optimal (Exercise 6.24). Transition to $k$-wise independent distributions: deterministic small sets $A\subset\mathbb{F}_2^n$ with $\varphi_A$ $k$-wise independent (i.e. $(0,k)$-regular), best realized when $A$ is a linear subspace.

<a id="pdf-6c10bfcc8080-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.93 -->
**Proposition 6.31.** Let $H$ be an $m\times n$ matrix over $\mathbb{F}_2$ and $A\subseteq\mathbb{F}_2^n$ the span of $H$'s rows. Then $\varphi_A$ is $k$-wise independent iff every nonempty sum of at most $k$ columns of $H$ is nonzero in $\mathbb{F}_2^m$.

<a id="pdf-6c10bfcc8080-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
**Proof.** Since $\varphi_A=\sum_{\gamma\in A^\perp}\chi_\gamma$ (Proposition 3.11), $\varphi_A$ is $k$-wise independent iff $|\gamma|>k$ for every $\gamma\in A^\perp\setminus\{0\}$. But $\gamma\in A^\perp$ iff $H\gamma=0$. $\square$

<a id="pdf-6c10bfcc8080-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.85 -->
A simple construction achieves $m\sim k\log n$ rows.

<a id="pdf-6c10bfcc8080-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.90 -->
**Theorem 6.32.** Let $k,\ell\in\mathbb{N}^+$ with $k\le n\le 2^\ell$. Then for $m=(k-1)\ell+1$ there is a matrix $H\in\mathbb{F}_2^{m\times n}$ such that any nonempty sum of at most $k$ columns of $H$ is nonzero in $\mathbb{F}_2^m$.

<a id="pdf-6c10bfcc8080-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.93 -->
**Proof.** Write $\alpha_1,\dots,\alpha_n$ for the elements of the finite field $\mathbb{F}_n$, and consider the matrix $H'\in\mathbb{F}_n^{k\times n}$ whose $i$-th column is $(1,\alpha_i,\alpha_i^2,\dots,\alpha_i^{k-1})$. Any submatrix of $H'$ formed by choosing $k$ columns is a Vandermonde matrix and is therefore nonsingular; hence any subset of $k$ columns of $H'$ is linearly independent in $\mathbb{F}_n^k$, and in particular any sum of at most $k$ columns of $H'$ is nonzero in $\mathbb{F}_n^k$. Now form $H\in\mathbb{F}_2^{m\times n}$ from $H'$ by replacing each entry $\alpha_j^{\,i}$ ($i>0$) with $\mathrm{enc}(\alpha_j^{\,i})$, thought of as a column vector in $\mathbb{F}_2^\ell$. Since $\mathrm{enc}$ is a linear map, any sum of at most $k$ columns of $H$ is nonzero in $\mathbb{F}_2^m$. $\square$

<a id="pdf-6c10bfcc8080-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.95 -->
**Corollary 6.33.** There is a deterministic algorithm that, given integers $1\le k\le n$, runs in $\mathrm{poly}(n^k)$ time and outputs a subspace $A\le\mathbb{F}_2^n$ of cardinality at most $2^k n^{k-1}$ such that $\varphi_A$ is $k$-wise independent.

<a id="pdf-6c10bfcc8080-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->
**Proof.** It suffices to assume $n=2^\ell$ is a power of $2$ and then obtain cardinality $2n^{k-1}=2^{(k-1)\ell+1}$. In this case, the algorithm constructs $H$ as in Theorem 6.32 and takes $A$ to be the span of its rows. The fact that $\varphi_A$ is $k$-wise independent is immediate from Proposition 6.31. $\square$

<a id="pdf-6c10bfcc8080-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.80 -->
For constant $k$ the upper bound $O(n^{k-1})$ is near-optimal: it improves to $O(n^{\lfloor k/2\rfloor})$, and there is a lower bound $\Omega(n^{\lceil k/2\rceil})$ for constant $k$ (Exercises 6.27, 6.28).

<a id="pdf-6c10bfcc8080-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.92 -->
**Lemma 6.34.** Suppose $H \in \mathbb{F}_2^{m\times n}$ is such that any sum of at most $k$ columns of $H$ is nonzero in $\mathbb{F}_2^m$. Let $\varphi$ be an $\epsilon$-biased density on $\mathbb{F}_2^m$. Draw $y \sim \varphi$ and set $z = y^\top H \in \mathbb{F}_2^n$. Then the density of $z$ is $(\epsilon, k)$-wise independent.

<a id="pdf-6c10bfcc8080-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
**Proof.** Suppose $\gamma \in \mathbb{F}_2^n$ has $0 < |\gamma| \le k$. Then $H\gamma$ is nonzero by assumption, and hence $|\mathbb{E}[\chi_\gamma(z)]| = |\mathbb{E}_{y\sim\varphi}[(-1)^{y^\top H\gamma}]| \le \epsilon$ since $\varphi$ is $\epsilon$-biased. $\square$

<a id="pdf-6c10bfcc8080-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.85 -->
**Theorem 6.35.** Combining the constructions of Theorems 6.30 and 6.32, there is a deterministic algorithm that, given integers $1 \le k \le n$ and $0 < \epsilon \le 1/2$, runs in time $\mathrm{poly}(n/\epsilon)$ and outputs a multiset $A \subseteq \mathbb{F}_2^n$ of cardinality $O(k\log(n)/\epsilon)^2$ (a power of 2) such that $\varphi_A$ is $(\epsilon, k)$-wise independent. Such a distribution can be sampled using only $O(\log k + \log\log n + \log(1/\epsilon))$ independent random bits.

<a id="pdf-6c10bfcc8080-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.95 -->
**6.4. Applications in learning and testing.** Applications of the study of pseudorandomness.

<a id="pdf-6c10bfcc8080-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.85 -->
Setup: learning $\mathcal{C} = \{f:\mathbb{F}_2^n \to \mathbb{F}_2 : f \text{ is a } k\text{-junta}\}$ with $k \le O(\log n)$. With query access, $\mathcal{C}$ is exactly learnable in $\mathrm{poly}(n)$ time (Exercise 3.37(a)). From random examples, no method is known better than the $n^k\cdot\mathrm{poly}(n)$ Low-Degree Algorithm (Theorem 3.36), which is superpolynomial once $k = \omega(1)$; the same holds for depth-$k$ decision trees and $\mathrm{poly}(n)$-size DNFs/CNFs. Learning $O(\log n)$-juntas is a prerequisite.

<a id="pdf-6c10bfcc8080-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.93 -->
**Theorem 6.36.** For $k \le O(\log n)$, the class $\mathcal{C} = \{f:\mathbb{F}_2^n \to \mathbb{F}_2 : f \text{ is a } k\text{-junta}\}$ can be exactly learned from random examples in time $n^{(3/4)k}\cdot\mathrm{poly}(n)$. The exponent $3/4$ can be replaced by $\omega/(\omega+1)$, where $\omega$ is any matrix-multiplication exponent ($n\times n$ multiply in $O(n^\omega)$).

<a id="pdf-6c10bfcc8080-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.92 -->
**Lemma 6.37.** Theorem 6.36 follows from a learning algorithm that, given random examples from a nonconstant $k$-junta $f:\mathbb{F}_2^n \to \mathbb{F}_2$, finds at least one relevant coordinate for $f$ (with probability $\ge 1-\delta$) in time $n^{(3/4)k}\cdot\mathrm{poly}(n)\cdot\log(1/\delta)$. (Proof: Exercise 6.31.)

<a id="pdf-6c10bfcc8080-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.87 -->
**Proof.** Given random-example access to a nonconstant $k$-junta $f$, estimate the Fourier coefficients $\widehat{f}(S)$ for all $1 \le |S| \le d$, where $d \le k$ is a parameter. By Proposition 3.30, all estimates are accurate to within $(1/3)2^{-k}$ except with probability $\delta/2$, in time $n^d\cdot\mathrm{poly}(n)\cdot\log(1/\delta)$ (using $2^k \le \mathrm{poly}(n)$). Since $f$ is a $k$-junta, each $\widehat{f}(S)$ is either $0$ or at least $2^{-k}$ in magnitude, so the sets $S$ with $\widehat{f}(S) \ne 0$ are exactly identified. For any such $S$, every coordinate $i \in S$ is relevant (Exercise 2.11). Hence unless $\widehat{f}(S)=0$ for all $1 \le |S| \le d$, a relevant coordinate is found in time $n^d\cdot\mathrm{poly}(n)\cdot\log(1/\delta)$.

<a id="pdf-6c10bfcc8080-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.85 -->
**Proof (continued).** Remaining case: $\widehat{f}(S)=0$ for all $1 \le |S| \le d$, i.e. $f$ is $d$th-order correlation immune. By Siegenthaler's Theorem, $\deg_{\mathbb{F}_2}(f) \le k-d$ (with $d < k$ since $f$ is nonconstant). There is a learning algorithm running in time $O(n)^{3\ell}\cdot\log(1/\delta)$ that exactly learns any $\mathbb{F}_2$-polynomial of degree at most $\ell$ (except w.p. $\delta/2$): draw $O(n)^\ell$ random examples and solve an $\mathbb{F}_2$-linear system for the coefficients (Exercise 6.30). Thus in time $n^{3(k-d)}\cdot\mathrm{poly}(n)\cdot\log(1/\delta)$ this exactly determines $f$ and finds a relevant coordinate. Choosing $d = \tfrac{3}{4}k$ balances the two running times; regardless of whether $f$ is $d$th-order correlation immune, one of the two algorithms finds a relevant coordinate, except with probability $\delta/2 + \delta/2 = \delta$, in time $n^{(3/4)k}\cdot\mathrm{poly}(n)\cdot\log(1/\delta)$. $\square$

<a id="pdf-6c10bfcc8080-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.88 -->
Using $\epsilon$-biased distributions to give a deterministic version of the Goldreich–Levin algorithm (hence the Kushilevitz–Mansour learning algorithm) for functions $f$ with small $\|\widehat{f}\|_1$.

<a id="pdf-6c10bfcc8080-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.92 -->
**Lemma 6.38.** If $f:\{-1,1\}^n \to \mathbb{R}$ and $\varphi:\{-1,1\}^n \to \mathbb{R}$ is an $\epsilon$-biased density, then $\left|\mathbb{E}_{x\sim\varphi}[f(x)] - \mathbb{E}[f]\right| \le \|\widehat{f}\|_1\,\epsilon.$ (Also follows from Proposition 6.13(1).)

<a id="pdf-6c10bfcc8080-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.90 -->
**Proof.** By Plancherel, $\mathbb{E}_{x\sim\varphi}[f(x)] = \langle \varphi, f\rangle = \widehat{f}(\emptyset) + \sum_{S\ne\emptyset}\widehat{\varphi}(S)\widehat{f}(S)$, and its difference from $\mathbb{E}[f] = \widehat{f}(\emptyset)$ has absolute value at most $\sum_{S\ne\emptyset}|\widehat{\varphi}(S)|\cdot|\widehat{f}(S)| \le \epsilon\sum_{S\ne\emptyset}|\widehat{f}(S)| \le \|\widehat{f}\|_1\,\epsilon.$ $\square$

<a id="pdf-6c10bfcc8080-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.90 -->
**Corollary 6.39.** Since $\|\widehat{f^2}\|_1 \le \|\widehat{f}\|_1^2$ (Exercise 3.6): if $f:\{-1,1\}^n \to \mathbb{R}$ and $\varphi$ is an $\epsilon$-biased density, then $\left|\mathbb{E}_{x\sim\varphi}[f(x)^2] - \mathbb{E}[f^2]\right| \le \|\widehat{f}\|_1^2\,\epsilon.$

<a id="pdf-6c10bfcc8080-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.90 -->
**Proposition 6.40.** There is a deterministic algorithm that, given query access to $f:\{-1,1\}^n \to \mathbb{R}$, a set $U \subseteq [n]$, $0 < \epsilon \le 1/2$, and $s \ge 1$, outputs an estimate $\widetilde{f}(U)$ satisfying $|\widetilde{f}(U) - \widehat{f}(U)| \le \epsilon$, provided $\|\widehat{f}\|_1 \le s$. The running time is $\mathrm{poly}(n, s, 1/\epsilon)$. (Deterministic version of Proposition 3.30.)

<a id="pdf-6c10bfcc8080-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.90 -->
**Proof.** It suffices to handle $U = \emptyset$: for general $U$ the algorithm simulates query access to $f\cdot\chi_U$ with $\mathrm{poly}(n)$ overhead, and $\widehat{f}(U) = \widehat{(f\cdot\chi_U)}(\emptyset)$. Use Theorem 6.30 to construct an $(\epsilon/s)$-biased density $\varphi$ uniform over a (multi)set of cardinality $O(n^2 s^2/\epsilon^2)$. Enumerating this set and querying $f$, deterministically output the estimate $\widetilde{f}(\emptyset) = \mathbb{E}_{x\sim\varphi}[f(x)]$ in time $\mathrm{poly}(n,s,1/\epsilon)$. The error bound follows from Lemma 6.38. $\square$

<a id="pdf-6c10bfcc8080-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->
Continuing the derandomization of Goldreich–Levin, recall that Proposition 3.40 lets one estimate, for $S\subseteq J\subseteq[n]$,
$$\mathbf{W}^{S|\overline{J}}[f]=\sum_{T\subseteq\overline{J}}\widehat{f}(S\cup T)^2=\mathbb{E}_{z\sim\{-1,1\}^{\overline{J}}}\big[\widehat{f_{J|z}}(S)^2\big].\quad(6.6)$$
For any $z\in\{-1,1\}^{\overline{J}}$ one can use Proposition 6.40 to deterministically estimate $\widehat{f_{J|z}}(S)$ to accuracy $\pm\varepsilon$: one can simulate query access to $f_{J|z}$, the $(\varepsilon/s)$-biased density $\varphi$ remains $(\varepsilon/s)$-biased on $\{-1,1\}^{\overline{J}}$, and $\|f_{J|z}\|_1\le\|f\|_1\le s$ by Exercise 3.7. This lets one deterministically estimate (6.6).

<a id="pdf-6c10bfcc8080-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.93 -->
**Proposition 6.41.** There is a deterministic algorithm that, given query access to $f:\{-1,1\}^n\to\{-1,1\}$, sets $S\subseteq J\subseteq[n]$, and parameters $0<\varepsilon\le 1/2$ and $s\ge 1$, outputs an estimate $\beta$ for $\mathbf{W}^{S|\overline{J}}[f]$ satisfying $|\mathbf{W}^{S|\overline{J}}[f]-\beta|\le\varepsilon$, provided $\|\hat f\|_1\le s$. Running time $\mathrm{poly}(n,s,1/\varepsilon)$.

<a id="pdf-6c10bfcc8080-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.50 -->
**Proof.** With the operator $\mathrm{F}^S_J f$ of Definition 3.20, where $(\mathrm{F}^S_J f)(z)=\widehat{f_{J|z}}(S)$, equation (6.6) makes the task to estimate $\mathbb{E}_{z\sim\{-1,1\}^J}[(\mathrm{F}^S_J f)^2(z)]$. If $\phi$ is an $\tfrac{\varepsilon}{4s^2}$-biased density, Corollary 6.39 gives
$$\Big|\mathbb{E}_{z\sim\phi}[(\mathrm{F}^S_J f)^2(z)]-\mathbb{E}_{z\sim\{-1,1\}^J}[(\mathrm{F}^S_J f)^2(z)]\Big|\le\|\widehat{\mathrm{F}^S_J f}\|_1^2\cdot\tfrac{\varepsilon}{4s^2}\le\|\hat f\|_1^2\cdot\tfrac{\varepsilon}{4s^2}\le\tfrac{\varepsilon}{4},\quad(6.7)$$
the second inequality from Proposition 3.21. For each $z\in\{-1,1\}^J$ the algorithm uses $\phi$ to deterministically estimate $(\mathrm{F}^S_J f)(z)=\widehat{f_{J|z}}(S)$ to within $\pm\tfrac{\varepsilon}{4s^2}\cdot s\le \tfrac{\varepsilon}{4}$ in $\mathrm{poly}(n,s,1/\varepsilon)$ time; since $|(\mathrm{F}^S_J f)(z)|\le1$, its square approximates $(\mathrm{F}^S_J f)^2(z)$ to within $\tfrac{3\varepsilon}{4}$. Enumerating the support of $\phi$ then estimates $\mathbb{E}_{z\sim\phi}[(\mathrm{F}^S_J f)^2(z)]$ to within $\pm\tfrac{3\varepsilon}{4}$, which with (6.7) gives the desired quantity to within $\varepsilon$. $\square$

<a id="pdf-6c10bfcc8080-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.85 -->
Propositions 6.40 and 6.41 are the only ingredients needed to derandomize the Goldreich–Levin Algorithm, yielding a derandomized version of its corollary Theorem 3.38 on learning functions of small Fourier 1-norm.

<a id="pdf-6c10bfcc8080-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.85 -->
**Theorem 6.42.** Let $\mathcal C=\{f:\{-1,1\}^n\to\{-1,1\}:\|\hat f\|_1\le s\}$. Then $\mathcal C$ is deterministically learnable from queries with error $\varepsilon$ in time $\mathrm{poly}(n,s,1/\varepsilon)$.

<a id="pdf-6c10bfcc8080-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.85 -->
Since any $f:\{-1,1\}^n\to\{-1,1\}$ with $\mathrm{sparsity}(\hat f)\le s$ also has $\|\hat f\|_1\le s$, Exercise 3.37(c) gives:

**Theorem 6.43.** Let $\mathcal C=\{f:\{-1,1\}^n\to\{-1,1\}:\mathrm{sparsity}(\hat f)\le 2^{O(k)}\}$. Then $\mathcal C$ is deterministically learnable exactly (0 error) from queries in time $\mathrm{poly}(n,2^k)$.

<a id="pdf-6c10bfcc8080-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.85 -->
Example concept classes: decision trees of size at most $s$ (for Theorem 6.42/6.43 by 1-norm/sparsity) and decision trees of depth at most $k$. The section concludes with a derandomized version of the Blum–Luby–Rubinfeld linearity test of Chapter 1.6.

<a id="pdf-6c10bfcc8080-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.96 -->
**Derandomized BLR Test.** Given query access to $f:\mathbb F_2^n\to\mathbb F_2$:
1. Choose $x\sim\mathbb F_2^n$ (uniform) and $y\sim\varphi$, where $\varphi$ is an $\varepsilon$-biased density.
2. Query $f$ at $x$, $y$, and $x+y$.
3. "Accept" if $f(x)+f(y)=f(x+y)$.

<a id="pdf-6c10bfcc8080-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.80 -->
The original BLR Test uses $2n$ independent random bits; the derandomized version needs only $n+O(\log(n/\varepsilon))$, near-minimal since a test using $\approx.99n$ bits could inspect only a $2^{-.01n}$ fraction of $f$'s values. An $\mathbb F_2$-linear $f$ is still accepted with probability 1. For the approximate converse one must concede affineness: any $f$ accepted with probability close to 1 need only be close to an affine function ($\deg_{\mathbb F_2}(f)\le1$), not linear — e.g. $f\equiv1$ except on the tiny support of $\phi$ almost always satisfies the acceptance criterion yet is far from linear while very close to the affine function $1$.

<a id="pdf-6c10bfcc8080-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.80 -->
**Theorem 6.44.** Suppose the Derandomized BLR Test accepts $f:\mathbb F_2^n\to\mathbb F_2$ with probability $\tfrac12+\tfrac12\theta$. Then $f$ has correlation at least $\sqrt{\theta^2-\varepsilon}$ with some affine $g:\mathbb F_2^n\to\mathbb F_2$; i.e. $\mathrm{dist}(f,g)\le\tfrac12-\tfrac12\sqrt{\theta^2-\varepsilon}$.

<a id="pdf-6c10bfcc8080-p017-b006"></a>
<!-- pdf-source: page=17; block=6; confidence=0.80 -->
**Remark 6.45.** The bound is useful both for $\theta$ near 0 and near 1; e.g. with $\theta=1-2\delta$, if $f$ is accepted with probability $1-\delta$ then $f$ is nearly $\delta$-close to an affine function, provided $\varepsilon\ll\delta$.

<a id="pdf-6c10bfcc8080-p017-b007"></a>
<!-- pdf-source: page=17; block=7; confidence=0.80 -->
**Proof.** As in the BLR analysis (Theorem 1.30), encode $f$'s outputs by $\pm1\in\mathbb R$. The hypothesis is equivalent to
$$\theta\le\mathbb{E}_{x\sim\mathbb F_2^n,\ y\sim\phi}[f(x)f(y)f(x+y)]=\mathbb{E}_{y\sim\phi}[f(y)\cdot(f*f)(y)].$$

<a id="pdf-6c10bfcc8080-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.70 -->
**Proof (continued).** By Cauchy–Schwarz,
$$\mathbb{E}_{y\sim\phi}[f(y)(f*f)(y)]\le\sqrt{\mathbb{E}_{y\sim\phi}[f(y)^2]}\,\sqrt{\mathbb{E}_{y\sim\phi}[(f*f)^2(y)]}=\sqrt{\mathbb{E}_{y\sim\phi}[(f*f)^2(y)]},$$
hence, using Corollary 6.39 and $\widehat{f*f}(\gamma)=\hat f(\gamma)^2$,
$$\theta^2\le\mathbb{E}_{y\sim\phi}[(f*f)^2(y)]\le\mathbb{E}[(f*f)^2]+\|\widehat{f*f}\|_1\varepsilon=\sum_{\gamma\in\mathbb F_2^n}\hat f(\gamma)^4+\varepsilon.$$
Concluding as in the original analysis (cf. Proposition 6.7, Exercise 1.29),
$$\theta^2-\varepsilon\le\sum_\gamma\hat f(\gamma)^4\le\max_\gamma\{\hat f(\gamma)^2\}\cdot\sum_\gamma\hat f(\gamma)^2=\max_\gamma\{\hat f(\gamma)^2\},$$
so there exists $\gamma^*$ with $|\hat f(\gamma^*)|\ge\sqrt{\theta^2-\varepsilon}$. $\square$

<a id="pdf-6c10bfcc8080-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.95 -->
**6.5. Highlight: Fooling $\mathbb F_2$-polynomials**

<a id="pdf-6c10bfcc8080-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.85 -->
A density $\phi$ is $\varepsilon$-biased if its correlation with every $\mathbb F_2$-linear function is at most $\varepsilon$ in magnitude; in pseudorandomness terms, $\phi$ fools the class of $\mathbb F_2$-linear functions.

<a id="pdf-6c10bfcc8080-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.90 -->
**Definition 6.46.** Let $\phi:\mathbb F_2^n\to\mathbb R_{\ge0}$ be a density and $\mathcal C$ a class of functions $\mathbb F_2^n\to\mathbb R$. We say $\phi$ **$\varepsilon$-fools** $\mathcal C$ if
$$\Big|\mathbb{E}_{y\sim\phi}[f(y)]-\mathbb{E}_{x\sim\mathbb F_2^n}[f(x)]\Big|\le\varepsilon\quad\text{for all }f\in\mathcal C.$$

<a id="pdf-6c10bfcc8080-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.85 -->
By Theorem 6.30, $O(\log(n/\varepsilon))$ independent random bits generate a density $\varepsilon$-fooling the class of $f:\mathbb F_2^n\to\{-1,1\}$ with $\deg_{\mathbb F_2}(f)\le1$. Open question: how many random bits $\varepsilon$-fool all functions of $\mathbb F_2$-degree at most $d$? The naive hope that $\varepsilon$-biased densities automatically fool degree $d>1$ fails badly, even for $d=2$.

<a id="pdf-6c10bfcc8080-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.85 -->
**Example 6.47.** Let $\mathrm{IP}_n:\mathbb F_2^n\to\{0,1\}$ be inner product mod 2 (of $\mathbb F_2$-degree 2), and let $\phi:\mathbb F_2^n\to\mathbb R_{\ge0}$ be the density of the uniform distribution on the support of $\mathrm{IP}_n$. $\mathrm{IP}_n$ is extremely regular (Example 6.4) and $\phi$ is roughly $2^{-n/2}$-biased (Exercise 6.7), yet $\phi$ fails to fool $\mathrm{IP}_n$ itself: $\mathbb{E}_{x\sim\mathbb F_2^n}[\mathrm{IP}_n(x)]\approx1/2$ while $\mathbb{E}_{y\sim\phi}[\mathrm{IP}_n(y)]=1$.

<a id="pdf-6c10bfcc8080-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.97 -->
## 6.5. Highlight: Fooling F2-polynomials

<a id="pdf-6c10bfcc8080-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.90 -->
**History.** The problem of fooling $n$-bit $\mathbb{F}_2$-degree-$d$ functions with few random bits was first taken up by Luby, Veličković, and Wigderson [LVW93], who generated a fooling distribution using $\exp\!\big(O(\sqrt{d\log(n/d)+\log(1/\varepsilon)})\big)$ independent random bits. Bogdanov and Viola [BV07] later achieved $O(\log(n/\varepsilon))$ random bits for $d=2$ and $O(\log n)+\exp(\mathrm{poly}(1/\varepsilon))$ random bits for $d=3$, and suggested that $\mathbb{F}_2$-degree-$d$ functions might be fooled by the sum of $d$ independent draws from a small-bias distribution. Lovett [Lov08] showed that a sum of $2^d$ independent draws from a small-bias distribution suffices: if $\varphi$ is any $\varepsilon$-biased density on $\mathbb{F}_2^n$,
$$\left|\ \mathbb{E}_{y^{(1)},\dots,y^{(2^d)}\sim\varphi}\big[f(y^{(1)}+\cdots+y^{(2^d)})\big]\;-\;\mathbb{E}_{x\sim\mathbb{F}_2^n}[f(x)]\ \right|\ \le\ O\!\big(\varepsilon^{1/4^d}\big).$$
In other words, the $2^d$-fold convolution $\varphi^{*2^d}$ fools functions of $\mathbb{F}_2$-degree $d$, using just $2^{O(d)}\log(n/\varepsilon)$ random bits.

<a id="pdf-6c10bfcc8080-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.95 -->
**Viola's Theorem.** Let $\phi$ be any $\varepsilon$-biased density on $\mathbb{F}_2^n$, $0\le\varepsilon\le1$. Let $d\in\mathbb{N}^+$ and define $\varepsilon_d=9\varepsilon^{1/2^{d-1}}$. Then the class of all $f:\mathbb{F}_2^n\to\{-1,1\}$ with $\deg_{\mathbb{F}_2}(f)\le d$ is $\varepsilon_d$-fooled by the $d$-fold convolution $\phi^{*d}$; i.e.,
$$\left|\ \mathbb{E}_{y^{(1)},\dots,y^{(d)}\sim\phi}\big[f(y^{(1)}+\cdots+y^{(d)})\big]\;-\;\mathbb{E}_{x\sim\mathbb{F}_2^n}[f(x)]\ \right|\ \le\ 9\varepsilon^{1/2^{d-1}}.$$

<a id="pdf-6c10bfcc8080-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.92 -->
By Theorem 6.30, Viola's Theorem implies one can $\varepsilon$-fool $n$-bit functions of $\mathbb{F}_2$-degree $d$ using only $O(d\log n)+O(d\,2^d\log(1/\varepsilon))$ independent random bits. The proof is by induction on $d$, reducing the degree-$(d+1)$ case to degree $d$ via directional derivatives.

<a id="pdf-6c10bfcc8080-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.96 -->
**Definition 6.48.** For $f:\mathbb{F}_2^n\to\mathbb{F}_2$ and $y\in\mathbb{F}_2^n$, the directional derivative $\Delta_y f:\mathbb{F}_2^n\to\mathbb{F}_2$ is defined by $\Delta_y f(x)=f(x+y)-f(x)$. Over $\mathbb{F}_2$ equivalently $\Delta_y f(x)=f(x+y)+f(x)$.

<a id="pdf-6c10bfcc8080-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.96 -->
**Fact 6.49.** For any $f:\mathbb{F}_2^n\to\mathbb{F}_2$ and $y\in\mathbb{F}_2^n$, $\deg_{\mathbb{F}_2}(\Delta_y f)\le \deg_{\mathbb{F}_2}(f)-1$.

<a id="pdf-6c10bfcc8080-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.95 -->
**Proposition 6.50.** Let $f:\mathbb{F}_2^n\to\mathbb{F}_2$ have $\deg_{\mathbb{F}_2}(f)=d$ and fix $y,y'\in\mathbb{F}_2^n$. Define $g:\mathbb{F}_2^n\to\mathbb{F}_2$ by $g(x)=f(x+y)-f(x+y')$. Then $\deg_{\mathbb{F}_2}(g)\le d-1$.

<a id="pdf-6c10bfcc8080-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.93 -->
**Proof.** Passing from the $\mathbb{F}_2$-polynomial representation of $f(x)$ to that of $g(x)$, each maximal-degree-$d$ monomial $x_S$ is replaced by $(x+y)_S-(x+y')_S$. Upon expansion the monomials $x_S$ cancel, leaving a polynomial of degree at most $d-1$. $\square$

<a id="pdf-6c10bfcc8080-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.92 -->
**Proof of Viola's Theorem.** By induction on $d$. The $d=1$ case is immediate (even without the factor 9) since $\phi$ is $\varepsilon$-biased. Assume the theorem for all degrees $\le d$; let $f:\mathbb{F}_2^n\to\{-1,1\}$ have $\deg_{\mathbb{F}_2}(f)\le d+1$. Split into two cases according to whether the bias of $f$ is large or small.

<a id="pdf-6c10bfcc8080-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.90 -->
**Proof (Case 1: $\mathbb{E}[f]^2>\varepsilon_d$).** Multiplying the target deviation by $|\mathbb{E}[f]|$ and introducing an independent copy $x'$:
$$|\mathbb{E}[f]|\cdot\left|\mathbb{E}_{z\sim\phi^{*(d+1)}}[f(z)]-\mathbb{E}_{x\sim\mathbb{F}_2^n}[f(x)]\right| = \left|\mathbb{E}_{x'\sim\mathbb{F}_2^n,\,z\sim\phi^{*(d+1)}}[f(x')f(z)]-\mathbb{E}_{x',x\sim\mathbb{F}_2^n}[f(x')f(x)]\right|.$$
Writing $x'=z+y$ (resp. $x+y$) with $y\sim\mathbb{F}_2^n$ and using $\Delta_y f$:
$$=\left|\mathbb{E}_{y\sim\mathbb{F}_2^n}\!\left[\mathbb{E}_{z\sim\phi^{*(d+1)}}[\Delta_y f(z)]-\mathbb{E}_{x\sim\mathbb{F}_2^n}[\Delta_y f(x)]\right]\right|\ \le\ \mathbb{E}_{y\sim\mathbb{F}_2^n}\left|\mathbb{E}_{z\sim\phi^{*(d+1)}}[\Delta_y f(z)]-\mathbb{E}_{x}[\Delta_y f(x)]\right|.$$
For each $y$, $\Delta_y f$ has $\mathbb{F}_2$-degree $\le d$ (Fact 6.49); by induction $\phi^{*d}$ $\varepsilon_d$-fools it, and by Exercise 6.29 so does $\phi^{*(d+1)}$, so each inner term is $\le\varepsilon_d$. Since $|\mathbb{E}[f]|>\sqrt{\varepsilon_d}$,
$$\left|\mathbb{E}_{z\sim\phi^{*(d+1)}}[f(z)]-\mathbb{E}_x[f(x)]\right|\le\frac{\varepsilon_d}{\sqrt{\varepsilon_d}}=\sqrt{\varepsilon_d}\le\tfrac13\varepsilon_{d+1}\le\varepsilon_{d+1}.$$

<a id="pdf-6c10bfcc8080-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.90 -->
**Proof (Case 2: $\mathbb{E}[f]^2\le\varepsilon_d$, part 1).** Goal: show $\mathbb{E}_{w\sim\phi^{*(d+1)}}[f(w)]^2$ is nearly as small. By Cauchy–Schwarz,
$$\mathbb{E}_{w\sim\phi^{*(d+1)}}[f(w)]^2=\left(\mathbb{E}_{y\sim\phi,\,z\sim\phi^{*d}}[f(z+y)]\right)^2\le\mathbb{E}_{z\sim\phi^{*d}}\!\left[\big(\mathbb{E}_{y\sim\phi}[f(z+y)]\big)^2\right]=\mathbb{E}_{y,y'\sim\phi}\,\mathbb{E}_{z\sim\phi^{*d}}[f(z+y)f(z+y')].$$

<a id="pdf-6c10bfcc8080-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.89 -->
**Proof (Case 2, part 2).** For each outcome $y,y'$, the function $f(z+y)f(z+y')$ has $\mathbb{F}_2$-degree $\le d$ in $z$ (Proposition 6.50), so by induction
$$\mathbb{E}_{y,y'\sim\phi}\,\mathbb{E}_{z\sim\phi^{*d}}[f(z+y)f(z+y')]\le\varepsilon_d+\mathbb{E}_{x\sim\mathbb{F}_2^n,\,y,y'\sim\phi}[f(x+y)f(x+y')]=\varepsilon_d+\mathbb{E}_{x\sim\mathbb{F}_2^n}\big[(\phi*f)(x)^2\big].$$
By Parseval, $\mathbb{E}_x[(\phi*f)(x)^2]=\sum_{\gamma\in\mathbb{F}_2^n}\widehat{\phi}(\gamma)^2\widehat{f}(\gamma)^2\le\widehat{f}(0)^2+\varepsilon^2\sum_{\gamma\ne0}\widehat{f}(\gamma)^2\le\varepsilon_d+\varepsilon^2$, using $\widehat{f}(0)^2=\mathbb{E}[f]^2\le\varepsilon_d$ (Case 2 hypothesis). Hence
$$\mathbb{E}_{w\sim\phi^{*(d+1)}}[f(w)]^2\le2\varepsilon_d+\varepsilon^2\le3\varepsilon_d\le4\varepsilon_d,$$
so $|\mathbb{E}_{w\sim\phi^{*(d+1)}}[f(w)]|\le2\sqrt{\varepsilon_d}$. Since $|\mathbb{E}[f]|\le\sqrt{\varepsilon_d}$,
$$\left|\mathbb{E}_{w\sim\phi^{*(d+1)}}[f(w)]-\mathbb{E}[f]\right|\le3\sqrt{\varepsilon_d}=\varepsilon_{d+1}. \qquad\square$$

<a id="pdf-6c10bfcc8080-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.87 -->
**Tightness.** Ignoring the error parameter, the result is sharp: a counting argument (see [BV07]) shows the $d$-fold convolution of $\varepsilon$-biased densities cannot in general fool functions of $\mathbb{F}_2$-degree $d+1$. More explicitly, for any $d\in\mathbb{N}^+$ and $\ell\ge2d+1$, Lovett and Tzur [LT09] gave an explicit $\tfrac{\ell}{2^n}$-biased density $\varphi$ on $\mathbb{F}_2^{(\ell+1)n}$ and an explicit function $f:\mathbb{F}_2^{(\ell+1)n}\to\{-1,1\}$ of degree $d+1$ for which
$$\left|\mathbb{E}_{w\sim\varphi^{*d}}[f(w)]-\mathbb{E}[f]\right|\ge1-\frac{2d}{2^n}.$$

<a id="pdf-6c10bfcc8080-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.90 -->
**Remark.** It is not known whether $\varepsilon^{1/2^{d-1}}$ can be improved, even for $d=2$. Even a modest improvement to $\varepsilon^{1/1.99^d}$ (for $d$ as large as $\log n$) would be a major advance, implying progress on correlation bounds for polynomials [Vio09a].

<a id="pdf-6c10bfcc8080-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.97 -->
## 6.6. Exercises and notes

<a id="pdf-6c10bfcc8080-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.90 -->
**Exercise 6.1.** For $f$ chosen as in Proposition 6.1, compute $\mathrm{Var}[\widehat{f}(S)]$ for each $S\subseteq[n]$.

<a id="pdf-6c10bfcc8080-p021-b006"></a>
<!-- pdf-source: page=21; block=6; confidence=0.95 -->
**Exercise 6.2.** Prove Fact 6.8.

<a id="pdf-6c10bfcc8080-p021-b007"></a>
<!-- pdf-source: page=21; block=7; confidence=0.85 -->
**Exercise 6.3.** Show that any nonconstant $k$-junta has $\mathrm{Inf}_i^{(1-\delta)}[f]\ge(1/2-\delta/2)^{k-1}/k$ for at least one coordinate $i$.

<a id="pdf-6c10bfcc8080-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.95 -->
**Exercise 6.4.** Let $\phi:\mathbb{F}_2^n\to\mathbb{R}_{\ge 0}$ be an $\epsilon$-biased density. Show that for each $d\in\mathbb{N}^+$ the $d$-fold convolution $\phi^{*d}$ is an $\epsilon^d$-biased density.

<a id="pdf-6c10bfcc8080-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.95 -->
**Exercise 6.5.**
(a) If $f:\{-1,1\}^n\to\mathbb{R}$ has $\epsilon$-small influences, then it is $\sqrt{\epsilon}$-regular.
(b) For every even $n$ there is $f:\{-1,1\}^n\to\{-1,1\}$ that is $2^{-n/2}$-regular but does not have $\epsilon$-small influences for any $\epsilon<1/2$.
(c) There is $f:\{-1,1\}^n\to\{-1,1\}$ with $((1-\delta)^{n-1},\delta)$-small stable influences that is not $\epsilon$-regular for any $\epsilon<1$.
(d) For $f(x)=x_0\,\mathrm{Maj}_n(x_1,\dots,x_n)$ (Example 6.10), verify $\mathrm{Inf}_0^{(1-\delta)}[f]=\mathbf{Stab}_{1-\delta}[\mathrm{Maj}_n]$ for $\delta\in(0,1)$; hence $f$ does not have $(\epsilon,\delta)$-small stable influences unless $\epsilon\ge 1-\sqrt{\delta}$.
(e) Show the function $f:\{-1,1\}^{n+1}\to\{-1,1\}$ of part (d) is $\tfrac{1}{\sqrt n}$-regular.
(f) If $f:\{-1,1\}^n\to\mathbb{R}$ has $(\epsilon,\delta)$-small stable influences, then $f$ is $(\eta,k)$-regular for $\eta=\sqrt{\epsilon/(1-\delta)^{k-1}}$.
(g) $f$ has $(\epsilon,1)$-small stable influences if and only if $f$ is $(\sqrt{\epsilon},1)$-regular.
(h) If $f:\{-1,1\}^n\to\{-1,1\}$ is monotone and $(\epsilon,1)$-regular, then $f$ is $\epsilon$-regular and has $\epsilon$-small influences.

<a id="pdf-6c10bfcc8080-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.90 -->
**Exercise 6.6.**
(a) For $f:\{-1,1\}^n\to\mathbb{R}$, a partition $(J,\bar J)$ of $[n]$, and $z\sim\{-1,1\}^{\bar J}$ uniform, give a formula for $\mathrm{Var}_z\!\big[\mathbf{E}[f_{J\mid z}]\big]$ in terms of $f$'s Fourier coefficients. (Hint: direct application of Corollary 3.22.)
(b) Using that formula and the probabilistic method, give an alternate proof of the second statement of Proposition 6.12.

<a id="pdf-6c10bfcc8080-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.92 -->
**Exercise 6.7.** Let $\phi:\mathbb{F}_2^n\to\mathbb{R}_{\ge 0}$ be the density of the uniform distribution on the support of $\mathrm{IP}_n:\mathbb{F}_2^n\to\{0,1\}$. Show that $\phi$ is $\epsilon$-biased for $\epsilon=2^{-n/2}/(1-2^{-n/2})$, but not for any smaller $\epsilon$.

<a id="pdf-6c10bfcc8080-p022-b005"></a>
<!-- pdf-source: page=22; block=5; confidence=0.97 -->
**Exercise 6.8.** Prove Proposition 6.13.

<a id="pdf-6c10bfcc8080-p022-b006"></a>
<!-- pdf-source: page=22; block=6; confidence=0.95 -->
**Exercise 6.9.** Compute the $\mathbb{F}_2$-polynomial representation of the equality function $\mathrm{Equ}_n:\{0,1\}^n\to\{0,1\}$, defined by $\mathrm{Equ}_n(x)=1$ if and only if $x_1=\cdots=x_n$.

<a id="pdf-6c10bfcc8080-p022-b007"></a>
<!-- pdf-source: page=22; block=7; confidence=0.92 -->
**Exercise 6.10.**
(a) Let $f:\{0,1\}^n\to\mathbb{R}$ with unique multilinear representation $q(x)=\sum_{S\subseteq[n]}c_S x^S$ over $\mathbb{R}$. Show that
$$c_S=\sum_{R\subseteq S}(-1)^{|S|-|R|}f(R),$$
identifying $R\subseteq[n]$ with its $0$-$1$ indicator string (Möbius inversion).
(b) Prove Proposition 6.21.

<a id="pdf-6c10bfcc8080-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.95 -->
**Exercise 6.11.** (Cf. Lemma 3.5.) Let $f:\mathbb{F}_2^n\to\mathbb{F}_2$ be nonzero with $\deg_{\mathbb{F}_2}(f)\le k$. Show that $\Pr[f(x)\neq 0]\ge 2^{-k}$. (Hint: as in Exercise 3.4, use induction on $n$.)

<a id="pdf-6c10bfcc8080-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.90 -->
**Exercise 6.12.** Let $f:\{-1,1\}^n\to\{0,1\}$.
(a) Show $\deg_{\mathbb{F}_2}(f)\le \log(\mathrm{sparsity}(\hat f))$. (Hint: Exercises 3.7 and 1.3, and Corollary 6.22.)
(b) Suppose $\hat f$ is $2^{-k}$-granular. Show $\deg_{\mathbb{F}_2}(f)\le k$ — a stronger result than part (a), via Exercise 3.32.

<a id="pdf-6c10bfcc8080-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.80 -->
**Exercise 6.13.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be bent, $n\ge 2$. Show that $\deg_{\mathbb{F}_2}(f)\le n/2$. (Note the weaker upper bound $n/2+1$ follows from Exercise 6.12(b).)

<a id="pdf-6c10bfcc8080-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.75 -->
**Exercise 6.14.** (Prove Theorem 6.25.)
(a) Suppose $p(x)=c_0+r(x)$ is a real multilinear polynomial in $x_1,\dots,x_n$ with $c_0\neq 0$, and for the monomial $x^S$ (coefficient $c_S\neq 0$) $|S|>\tfrac{2}{3}n$, and $|T|>\tfrac{2}{3}n$ for every monomial $x^T$ appearing in $r(x)$. Show that after expansion and multilinear reduction (i.e. $x_i^2\mapsto 1$), $p(x)^2$ contains the term $2c_0 c_S x^S$.
(b) Deduce Theorem 6.25.

<a id="pdf-6c10bfcc8080-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.88 -->
**Exercise 6.15.** (Sharpness of Siegenthaler's Theorem and Theorem 6.25.)
(a) For all $n$ and $k<n-1$, find $f:\{0,1\}^n\to\{0,1\}$ that is $k$-resilient and has $\deg_{\mathbb{F}_2}(f)=n-k-1$.
(b) For all $n\ge 3$, find $f:\{0,1\}^n\to\{0,1\}$ that is $1$st-order correlation immune and has $\deg_{\mathbb{F}_2}(f)=n-1$.
(c) For all $n$ divisible by $3$, find a biased $f:\{0,1\}^n\to\{0,1\}$ that is $(\tfrac{2}{3}n-1)$th-order correlation immune.

<a id="pdf-6c10bfcc8080-p023-b006"></a>
<!-- pdf-source: page=23; block=6; confidence=0.97 -->
**Exercise 6.16.** Prove Proposition 6.27.

<a id="pdf-6c10bfcc8080-p023-b007"></a>
<!-- pdf-source: page=23; block=7; confidence=0.82 -->
**Exercise 6.17.** (Bent functions come in pairs.) Show that if $f:\mathbb{F}_2^n\to\{-1,1\}$ is bent, then its dual $2^{n/2}\hat f$ is also a bent function (with domain the dual $\mathbb{F}_2^n$).

<a id="pdf-6c10bfcc8080-p023-b008"></a>
<!-- pdf-source: page=23; block=8; confidence=0.96 -->
**Exercise 6.18.** Extend Proposition 6.29 to show that if $\pi$ is any permutation on $\mathbb{F}_2^n$, then $f(x,y)=\mathrm{IP}_{2n}(x,\pi(y))\,g(y)$ is bent.

<a id="pdf-6c10bfcc8080-p023-b009"></a>
<!-- pdf-source: page=23; block=9; confidence=0.90 -->
**Exercise 6.19.** (Dickson's Theorem.) Any polynomial $p:\mathbb{F}_2^n\to\mathbb{F}_2$ of degree at most $2$ can be expressed as
$$p(x)=\ell_0(x)+\sum_{j=1}^{k}\ell_j(x)\ell'_j(x),\qquad(6.8)$$
where $\ell_0$ is affine and $\ell_1,\ell'_1,\dots,\ell_k,\ell'_k$ are linearly independent linear functions; $k$ (the "rank" of $p$) depends only on $p$. Show that for $n$ even, $g:\mathbb{F}_2^n\to\{-1,1\}$ defined by $g(x)=\chi(p(x))$ is bent if and only if $k=n/2$, if and only if $g$ arises from $\mathrm{IP}_n$ as in Proposition 6.28.

<a id="pdf-6c10bfcc8080-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.90 -->
**Exercise 6.20.** Without appealing to Dickson's Theorem, prove that the complete quadratic $x\mapsto\sum_{1\le i<j\le n}x_i x_j$ can be expressed as in (6.8) with $k=\lfloor n/2\rfloor$. (Hint: induction on $n$, with different steps depending on the parity of $n$.)

<a id="pdf-6c10bfcc8080-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.84 -->
**Exercise 6.21.** Define $\mathrm{mod}_3:\{-1,1\}^n\to\{0,1\}$ by $\mathrm{mod}_3(x)=1$ iff $\sum_{j=1}^n x_j$ is divisible by $3$. Derive the Fourier expansion
$$\mathrm{mod}_3(x)=\tfrac{1}{3}+\tfrac{2}{3}\left(-\tfrac{1}{2}\right)^n\!\!\sum_{\substack{S\subseteq[n]\\ |S|\text{ even}}}(-1)^{(|S|\bmod 4)/2}\,\sqrt{3}^{\,|S|}\,x^S,$$
and conclude that $\mathrm{mod}_3$ is $\tfrac{2}{3}\big(\tfrac{\sqrt3}{2}\big)^n$-regular. (Hint: consider $\prod_{j=1}^n\big(-\tfrac{1}{2}+\tfrac{\sqrt{-3}}{2}x_j\big)$.)

<a id="pdf-6c10bfcc8080-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.90 -->
**Exercise 6.22.** In Theorem 6.30, show that given $r,s$, any fixed bit $y_i$ can be obtained in deterministic $\mathrm{poly}(\ell)$ time.

<a id="pdf-6c10bfcc8080-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.85 -->
**Exercise 6.23.**
(a) Slightly modify the construction in Theorem 6.30 to obtain a $(2^{-t}-2^{-\ell})$-biased density. (Hint: arrange for $p_\gamma$ to have degree at most $n-1$.)
(b) Since $F=\mathbb{F}_{2^\ell}$ is a dimension-$\ell$ vector space over $\mathbb{F}_2$, it has a basis $v_1,\dots,v_\ell$. Modify the construction so that $\phi$ is a density on $\mathbb{F}_2^{n\ell}$ with $y_{ij}=\langle \mathrm{enc}(v_j r^i),\mathrm{enc}(s)\rangle$ for $i\in[n],\,j\in[\ell]$. Show that $\phi$ remains $2^{-t}$-biased.

<a id="pdf-6c10bfcc8080-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.92 -->
**Exercise 6.24.** Fix $\epsilon\in(0,1)$ and $n\in\mathbb{N}$. Let $A\subseteq\mathbb{F}_2^n$ be a randomly chosen multiset in which $\lceil Cn/\epsilon^2\rceil$ elements are included, independently and uniformly. Show that if $C$ is a large enough constant, then $A$ is $\epsilon$-biased except with probability at most $2^{-n}$.

<a id="pdf-6c10bfcc8080-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.92 -->
**Exercise 6.25.** (Verifying matrix multiplication.) For the product $C=AB$ with $A,B\in\mathbb{F}_2^{n\times n}$, there is an algorithm [LG14] running in time $O(n^\omega)$, $\omega<2.373$, but very complicated. Given $A$, $B$, and the algorithm's output $C_0$, test whether $C_0=AB$.
(a) Give an algorithm using $n$ random bits and $O(n^2)$ time such that: if $C_0=AB$ it accepts with probability $1$; if $C_0\neq AB$ it accepts with probability at most $1/2$. (Hint: compute $C_0 x$ and $ABx$ for random $x\in\mathbb{F}_2^n$.)
(b) Reduce the number of random bits to $O(\log n)$ at the expense of false-acceptance probability $2/3$, keeping running time $O(n^2)$. (Use that in Theorem 6.30, $y$ can be computed from $r,s$ in $n\cdot\mathrm{polylog}(\ell)$ time.)

<a id="pdf-6c10bfcc8080-p024-b007"></a>
<!-- pdf-source: page=24; block=7; confidence=0.92 -->
**Exercise 6.26.** Simplify the exposition and analysis of Theorem 6.32 and Corollary 6.33 in the case $k=2$, and show that one can take $m$ to be one less (i.e. $m=\ell$).

<a id="pdf-6c10bfcc8080-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.98 -->
**Section 6.6. Exercises and notes.**

<a id="pdf-6c10bfcc8080-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.93 -->
**Exercise 6.27.** Consider the matrix $H'\in\mathbb{F}_n^{k\times n}$ constructed in Theorem 6.32, and suppose we delete all rows corresponding to even (nonzero) powers of the $\alpha_j$'s. Show that $H'$ retains the property that any sum of at most $k$ columns of $H'$ is nonzero in $\mathbb{F}_n^k$. (Hint: prove and use that $(\sum_j \beta_j)^2 = \sum_j \beta_j^2$ for any sequence of $\beta_j\in\mathbb{F}_n$.) Deduce that the cardinality of $A$ in Corollary 6.33 can be decreased to $2(2n)^{\lfloor k/2\rfloor}$.

<a id="pdf-6c10bfcc8080-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.85 -->
**Exercise 6.28.** Let $A\subseteq\{-1,1\}^n$ be a multiset whose probability density $\varphi_A$ is $k$-wise independent. Prove the lower bound $|A|\ge\Omega(n^{\lfloor k/2\rfloor})$.

(a) Suppose $F\subseteq 2^{[n]}$ is a family of subsets of $[n]$ with $|S\triangle T|\le k$ for all $S,T\in F$. For $S\in F$ let $\chi^A_S\in\mathbb{R}^{|A|}$ be the vector indexed by $A$ whose $a$-th entry is $\prod_{i\in S} a_i$. Show that $\{\tfrac{1}{\sqrt{|A|}}\chi^A_S : S\in F\}$ is orthonormal, hence $|A|\ge|F|$.

(b) Show one can find $F$ with $|F|\ge\sum_{j=0}^{k/2}\binom{n}{j}$ if $k$ is even, and $|F|\ge\sum_{j=0}^{(k-1)/2}\binom{n}{j}+\binom{n}{(k-1)/2}$ if $k$ is odd.

<a id="pdf-6c10bfcc8080-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.90 -->
**Exercise 6.29.** Let $\mathcal{C}$ be a class of functions $\mathbb{F}_2^n\to\mathbb{R}$ closed under translation ($f+z\in\mathcal{C}$ whenever $f\in\mathcal{C}$, $z\in\mathbb{F}_2^n$; cf. Definition 3.24); e.g. the class of functions of $\mathbb{F}_2$-degree at most $d$. Show that if a density $\psi$ $\epsilon$-fools $\mathcal{C}$, then $\psi*\phi$ also $\epsilon$-fools $\mathcal{C}$ for any density $\phi$.

<a id="pdf-6c10bfcc8080-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.86 -->
**Exercise 6.30.** Fix an integer $\ell\ge1$; generalize Exercise 3.43 to exactly learn $\mathbb{F}_2$-polynomials of degree $\le\ell$.

(a) Fix $p:\mathbb{F}_2^n\to\mathbb{F}_2$ with $\deg_{\mathbb{F}_2}(p)\le\ell$, and draw $x^{(1)},\dots,x^{(m)}$ uniformly and independently from $\mathbb{F}_2^n$ with $m\ge C\,2^\ell(n\ell+\log(1/\delta))$, $0<\delta\le1/2$, $C$ a large constant. Show that except with probability $\le\delta$, the only $q$ with $\deg_{\mathbb{F}_2}(q)\le\ell$ satisfying $q(x^{(i)})=p(x^{(i)})$ for all $i\in[m]$ is $q=p$. (Hint: Exercise 6.11 with $q-p$.)

(b) Show the concept class of all $\mathbb{F}_2$-polynomials of degree $\le\ell$ is learnable from random examples with error $0$ in time $O(n)^{3\ell}$. (Remark: the key step is solving a linear system, so it also runs in $O(n)^{\omega\ell}$ time given $O(n^\omega)$ matrix multiplication.)

(c) Extend so that in time $O(n)^{3\ell}\cdot\log(1/\delta)$ it succeeds with probability $\ge1-\delta$. (Hint: similar to Exercise 3.40.)

<a id="pdf-6c10bfcc8080-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.95 -->
**Exercise 6.31.** Prove Lemma 6.37. [Continued on next page.]

<a id="pdf-6c10bfcc8080-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.85 -->
**Exercise 6.31 (continued).**

(a) Give a $\mathrm{poly}(n,2^k)\cdot\log(1/\delta)$-time algorithm that, from random examples of a $k$-junta $f:\mathbb{F}_2^n\to\mathbb{F}_2$, determines (except with probability $\le\delta$) whether $f$ is constant, and if so which constant.

(b) Given random examples of a $k$-junta $f:\mathbb{F}_2^n\to\mathbb{F}_2$, a set $P\subseteq[n]$ of relevant coordinates, and $z\in\mathbb{F}_2^P$, show how to obtain $M$ independent random examples of the $(k-|P|)$-junta $f_{P\to z}$ in time $\mathrm{poly}(n,2^k)\cdot M\cdot\log(1/\delta)$ (except with probability $\le\delta$).

(c) Complete the proof of Lemma 6.37. (Hint: build a depth-$k$ decision tree for $f$.)

<a id="pdf-6c10bfcc8080-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.92 -->
**Exercise 6.32.** (a) Improve the bound in Lemma 6.38 to $\|\hat f\|_1\epsilon-|\hat f(\emptyset)|\epsilon$ and the bound in Corollary 6.39 to $\|\hat f\|_1^2\epsilon-\|f\|_2^2\epsilon$. (b) Improve the bound in Theorem 6.44 to $\sqrt{\theta^2-\epsilon}/\sqrt{1-\epsilon}$.

<a id="pdf-6c10bfcc8080-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.92 -->
**Exercise 6.33.** Improve on Theorem 6.44 by a factor of roughly $2$ in the case of acceptance probability near $1$. Specifically, show that if $f$ passes the Derandomized BLR Test with probability $1-\delta$, then there exists $\gamma^*\in\widehat{\mathbb{F}_2^n}$ with $|\hat f(\gamma^*)|\ge\sqrt{1-2\delta-\epsilon}/\sqrt{1-\epsilon}$.

<a id="pdf-6c10bfcc8080-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.83 -->
**Exercise 6.34.** Fix $k\in\mathbb{N}^+$. For a family $(f_s)_{s\in\{0,1\}^k}$ of functions $f_s:\mathbb{F}_2^n\to\mathbb{R}$, define the $k$-th Gowers inner product
$$\langle(f_s)_s\rangle_{U^k}=\mathbb{E}_{x,y_1,\dots,y_k}\Big[\prod_{s\in\{0,1\}^k} f_s\Big(x+\sum_{i:s_i=1} y_i\Big)\Big],$$
with $x,y_1,\dots,y_k$ independent uniform on $\mathbb{F}_2^n$, and the $k$-th Gowers norm $\|f\|_{U^k}=\langle(f,\dots,f)\rangle_{U^k}^{1/2^k}$ (all $2^k$ entries equal $f$); nonnegativity of $\langle\cdot\rangle_{U^k}$ is verified later.

(a) Check $\langle(f_0,f_1)\rangle_{U^1}=\mathbb{E}[f_0]\mathbb{E}[f_1]$, hence $\|f\|_{U^1}^2=\mathbb{E}[f]^2$.

(b) Check $\langle(f_{00},f_{10},f_{01},f_{11})\rangle_{U^2}=\sum_{\gamma\in\mathbb{F}_2^n}\hat f_{00}(\gamma)\hat f_{10}(\gamma)\hat f_{01}(\gamma)\hat f_{11}(\gamma)$, hence $\|f\|_{U^2}^4=\sum_\gamma\hat f(\gamma)^4=\|\hat f\|_4^4$ (cf. Exercise 1.29(b)).

(c) Show (6.9): $\langle(f_s)_s\rangle_{U^k}=\mathbb{E}_{y_1,\dots,y_k}\big[\mathbb{E}_x[\prod_{s:s_k=0}f_s(x+\sum_{i:s_i=1}y_i)]\cdot\mathbb{E}_{x'}[\prod_{s:s_k=1}f_s(x'+\sum_{i:s_i=1}y_i)]\big]$, where $x'$ is independent of $x,y_1,\dots,y_{k-1}$ and uniform.

<a id="pdf-6c10bfcc8080-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.84 -->
**Exercise 6.34 (continued).**

(d) Show $\langle(f,\dots,f)\rangle_{U^k}\ge0$ (nonnegativity, as promised).

(e) Using (6.9) and Cauchy–Schwarz, show $\langle(f_s)_s\rangle_{U^k}\le\sqrt{\langle(f_{(s_1,\dots,s_{k-1},0)})_s\rangle_{U^k}}\cdot\sqrt{\langle(f_{(s_1,\dots,s_{k-1},1)})_s\rangle_{U^k}}$.

(f) Show $\langle(f_s)_s\rangle_{U^k}\le\prod_{s\in\{0,1\}^k}\|f_s\|_{U^k}$ (6.10).

(g) For $f:\mathbb{F}_2^n\to\mathbb{R}$, show $\|f\|_{U^k}\le\|f\|_{U^{k+1}}$. (Hint: take the family on $\{0,1\}^{k+1}$ with $f_s=f$ if $s_{k+1}=0$ and $f_s=1$ if $s_{k+1}=1$.)

(h) Show $\|\cdot\|_{U^k}$ satisfies the triangle inequality and is thus a seminorm. (Hint: first show $\|f_0+f_1\|_{U^k}^{2^k}=\sum_{S\subseteq\{0,1\}^k}\langle(f_{1[s\in S]})_s\rangle_{U^k}$, then use (6.10).)

(i) Show $\|\cdot\|_{U^k}$ is in fact a norm for all $k\ge2$: $\|f\|_{U^k}=0\Rightarrow f=0$.

<a id="pdf-6c10bfcc8080-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.80 -->
**Notes.** The $\mathbb{F}_2$-polynomial representation of a Boolean function is its *algebraic normal form*, apparently first introduced explicitly by Zhegalkin (1927) [Zhe27].

For $f:\mathbb{Z}_n\to\mathbb{R}$, $\epsilon$-regularity as a pseudorandomness notion, and the equivalent combinatorial condition (Proposition 6.7), date to Chung–Graham [CG92] (in quasirandom graphs, to Thomason [Tho87] and Chung–Graham–Wilson [CGW89]). Treating small-(stable-)influence functions as "generic" originates with Kahn–Kalai–Linial [KKL88], brought forward in hardness-of-approximation work: implicitly by Håstad [Hås96, Hås99], explicitly by Khot–Kindler–Mossel–O'Donnell [KKMO07].

$\epsilon$-biased sets and $(\epsilon,k)$-wise independent distributions were introduced by Naor–Naor [NN93] (see also Peralta [Per90]). The Theorem 6.30 construction is due to Alon–Goldreich–Håstad–Peralta [AGHP92] (as is Exercise 6.23). $\epsilon$-biased sets are equivalent to linear error-correcting codes over $\mathbb{F}_2$ in which all codeword pairs have relative distance in $[\tfrac12-\epsilon,\tfrac12+\epsilon]$; the Theorem 6.30 construction concatenates Reed–Solomon and Hadamard codes (see MacWilliams–Sloane [MS77]). The nonconstructive upper bound of Exercise 6.24 is essentially the Gilbert–Varshamov bound, close to a known lower bound $\Omega\big(\tfrac{n}{\epsilon^2\log(1/\epsilon)}\big)$ (assuming $\epsilon\ge2^{-\Omega(n)}$) following from work of McEliece [text cut off].

<a id="pdf-6c10bfcc8080-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.90 -->
Bibliographic note (continuation): the referenced bound is attributed to Rodemich, Rumsey, and Welch [MRRW77] (see [MS77]). Additionally, constructive upper bounds of $O(n/\epsilon^3)$ and $O(n^{5/4}/\epsilon^{5/2})$ are known using tools from coding theory; see the work of Ben-Aroya and Ta-Shma [BT09] and Matthews and Peachey [MP11].

<a id="pdf-6c10bfcc8080-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.90 -->
Correlation immunity — condition (2) of **Corollary 6.14** — introduced by Siegenthaler [Sie84]. Independently, Chor, Friedman, Goldreich, Håstad, Rudich, and Smolensky [CFG+85] defined resilience and linked it to $(0,k)$-regularity of the Fourier spectrum, i.e. proved Corollary 6.14 (known in cryptography as the Xiao–Massey Theorem [XM88]). [CFG+85] also essentially contains **Theorem 6.25** and the function of **Example 6.16**; cf. Mossel et al. [MOS04].

<a id="pdf-6c10bfcc8080-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.90 -->
Explicit $k$-wise distributions of small support arose in orthogonal arrays (statistics), error-correcting codes, and derandomization. Alon, Babai, and Itai [ABI85] gave the construction of **Theorem 6.32** (in fact the stronger **Exercise 6.27**), via analysis of dual BCH codes in MacWilliams–Sloane [MS77]. The lower bound of **Exercise 6.28** is essentially due to Rao [Rao47], with independent proofs in [CFG+85, ABI85].

<a id="pdf-6c10bfcc8080-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.85 -->
Siegenthaler's Theorem (1984, [Sie84]) was motivated by stream ciphers: combining $n$ independent LFSR streams via $f:\mathbb{F}_2^n\to\mathbb{F}_2$. Attacks succeed if $f$ is correlated with any input bit (or pair/triple/etc.), motivating correlation-immunity. The parity $\chi_{[n]}$ is maximally correlation-immune but unusable due to $\mathbb{F}_2$-linearity (as is any low $\mathbb{F}_2$-degree function); Siegenthaler's theorem captures the tradeoff between correlation-immunity and $\mathbb{F}_2$-degree.

<a id="pdf-6c10bfcc8080-p028-b005"></a>
<!-- pdf-source: page=28; block=5; confidence=0.90 -->
Bent functions were named and first studied by Rothaus around 1966, though not published until 1976 [Rot76] (continues on next page).

<a id="pdf-6c10bfcc8080-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.90 -->
Bent functions (continued): by 1976 several works existed, e.g. [Dil72]; applications in cryptography and coding theory, see Carlet's survey [Car10]. The Section 6.3 constructions are due to Rothaus; the class in **Exercise 6.18** is the Maiorana–McFarland family. **Dickson's Theorem** is from a 1901 publication [Dic01, Theorem 199]; see also MacWilliams–Sloane [MS77, Theorem 15.4].

<a id="pdf-6c10bfcc8080-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.92 -->
**Theorem 6.36** is from Mossel et al. [MOS04]; an improved $k$-junta learning algorithm running in roughly $n^{0.6024k}\,\mathrm{poly}(n)$ time is due to G. Valiant [Val12]. Blum offers a $\$1{,}000$ prize for solving the case $k=\log\log n$ in $\mathrm{poly}(n)$ time [Blu03]. **Theorem 6.42** is due to Kushilevitz and Mansour [KM93]. The Derandomized BLR Test, **Theorem 6.44**, and **Exercise 6.32** are due to Ben-Sasson, Sudan, Vadhan, and Wigderson [BSSVW03].

<a id="pdf-6c10bfcc8080-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.92 -->
Attributions: **Exercise 6.11** to Muller [Mul54a, Theorem 6]; deriving **Exercise 6.30** from it and Blumer et al. [BEHW87] is folklore. **Exercise 6.12(a)** to Bernasconi and Codenotti [BC99]; **Exercise 6.13** from MacWilliams–Sloane [MS77]. In **Exercise 6.25**, part (a) is due to Freivalds [Fre79], part (b) to Naor and Naor [NN93]. The Gowers norm and **Exercise 6.34** are from Gowers [Gow01]. The second-statement proof in **Proposition 6.12** was suggested by Noam Lifshitz.
