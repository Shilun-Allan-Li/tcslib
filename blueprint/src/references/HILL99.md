<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 130039751e9f77848b6ddf8c5d97b0faf90a14f58860ce46a7f60fa0ab306bfb -->

<a id="pdf-130039751e9f-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# A Pseudorandom Generator from any One-way Function

<a id="pdf-130039751e9f-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.98 -->
The paper claims a construction of a pseudorandom generator from any one-way function; together with the reverse implication, this yields equivalence of their existence.

<a id="pdf-130039751e9f-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
## 1 Introduction

<a id="pdf-130039751e9f-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.97 -->
A pseudorandom generator is introduced as a basic primitive for feasible computation interacting with randomness; its description continues on page 2.

<a id="pdf-130039751e9f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
A polynomial-time computable map $g$ expands a short uniform random string $x$ into a longer output $g(x)$ that feasible algorithms cannot distinguish from a uniform string of the same length, meaning their acceptance probabilities differ only negligibly/essentially insignificantly. This expands a small supply of true randomness into many effectively random bits.

<a id="pdf-130039751e9f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.98 -->
The paper sketches the progression from unrestricted randomness tests to polynomial-time tests and notes that the commonly used definition is equivalent to the earlier formulation.

<a id="pdf-130039751e9f-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
Passing selected statistical tests is weaker than indistinguishability against every feasible test; cryptographic adversaries are modeled as maximally malicious subject to a time bound, and pseudorandom generators support private-key security.

<a id="pdf-130039751e9f-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
Pseudorandom generators offer a general way to replace long uniform random strings in probabilistic simulations with expanded short seeds; cited results use them to reduce randomness for polynomial-time algorithms and enable deterministic subexponential-time simulation.

<a id="pdf-130039751e9f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.94 -->
The cited deterministic-simulation results were later generalized.

<a id="pdf-130039751e9f-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
A function is one-way if it is efficiently computable but difficult to invert on average. The text notes that $P=NP$ rules out one-way functions, while $P\ne NP$ is not known to imply their existence.

<a id="pdf-130039751e9f-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.98 -->
Candidate one-way problems include discrete logarithms modulo random large primes, factoring products of two random large primes, coding-theory problems, and appropriately parameterized subset sum.

<a id="pdf-130039751e9f-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.94 -->
Earlier work obtained generators from discrete-logarithm hardness, one-way permutations, and several structured classes of one-way functions. For nonpermutations, successful inversion means finding any $x'$ with $f(x')=f(x)$. The paper identifies the remaining problem as constructing a generator from an arbitrary one-way function without structural assumptions and states that it resolves it.

<a id="pdf-130039751e9f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.97 -->
The paper combines results announced in [ILL:89] and [Håstad:90]. It contrasts iterative extraction of unpredictable bits from repeated applications of a one-way function with parallel entropy extraction from independent copies, combined with iterative pseudorandom-generator output stretching.

<a id="pdf-130039751e9f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=1.00 -->
## 1.1 Concepts and tools

<a id="pdf-130039751e9f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.98 -->
Earlier constructions used output bits that are computationally unpredictable given the other output bits but statistically correlated with them. Goldreich–Levin’s hidden input bit is the parity of a random subset of input bits; it simplifies and improves constructions from one-way permutations.

<a id="pdf-130039751e9f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.99 -->
Let $g$ be a polynomial-time computable function mapping strings of length $n$ to longer strings of length $\ell_n>n$. Let $X$ be uniformly distributed on strings of length $n$ and $Y$ uniformly distributed on strings of length $\ell_n$. Then $g$ is a pseudorandom generator if $g(X)$ and $Y$ are computationally indistinguishable.

<a id="pdf-130039751e9f-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.99 -->
Shannon entropy measures information and cannot increase under a function; in particular, $g(X)$ has at most $n$ bits of entropy when $X$ is uniform on $n$ bits (Proposition 2.2.4). The paper studies a computational analogue.

<a id="pdf-130039751e9f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.98 -->
The computational entropy of $g(X)$ is at least the Shannon entropy of $Y$ when $g(X)$ and $Y$ are computationally indistinguishable. Thus a pseudorandom generator has output computational entropy exceeding the Shannon entropy of its input, so it amplifies entropy.

<a id="pdf-130039751e9f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.98 -->
A pseudoentropy generator is a map $g$ for which $g(X)$ has computational entropy significantly greater than the Shannon entropy of $X$. A false entropy generator is a map $g$ for which $g(X)$ has computational entropy significantly greater than the Shannon entropy of $g(X)$.

<a id="pdf-130039751e9f-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
The paper constructs a false entropy generator from any one-way function, a pseudoentropy generator from any false entropy generator, and a pseudorandom generator from any pseudoentropy generator; the paper presents these results in reverse order.

<a id="pdf-130039751e9f-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.98 -->
Random inner products, as in Goldreich–Levin, act as hash functions from many bits to one bit. Lemma 4.5.1 is a hashing tool for manipulating entropy and can be interpreted as extracting nearly uniform bits from a slightly random source using random bits as a catalyst.

<a id="pdf-130039751e9f-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=1.00 -->
## 1.2 Outline

<a id="pdf-130039751e9f-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.99 -->
Section 2 sets notation for distributions and ensembles; Section 3 defines the primitives and quantitative security effects of reductions; Section 4 develops hidden-bit and hash-based entropy techniques and reduces false entropy generation to pseudorandom generation through pseudoentropy generation.

<a id="pdf-130039751e9f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.99 -->
Section 5 treats one-way functions with estimable preimage sizes; Section 6 constructs false entropy generators from arbitrary one-way functions, yielding the main result with Section 4; Section 7 gives a more direct, efficient pseudorandom-generator construction; Section 8 discusses cryptographic complexity context.

<a id="pdf-130039751e9f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=1.00 -->
## 2 Basic notation

<a id="pdf-130039751e9f-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.98 -->
$\mathbb N$ denotes the natural numbers; $|S|$ is the cardinality of a set $S$, and $S\setminus T$ contains elements of $S$ not in $T$. For a number $a$, $|a|$ is absolute value, $\lceil a\rceil$ the least integer at least $a$, and $\log(a)$ is base-two logarithm.

<a id="pdf-130039751e9f-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
Let $x$ and $y$ be bit strings. We let $\langle x,y\rangle$ denote the sequence $x$ followed by $y$, and when appropriate we also view this as the concatenation of $x$ and $y$. If $x\in\{0,1\}^n$ then $x_i$ is the $i$th bit of $x$, $x_{\{i,\ldots,j\}}=\langle x_i,\ldots,x_j\rangle$, and $x\oplus y=(x_1\oplus y_1,\ldots,x_n\oplus y_n)$.

<a id="pdf-130039751e9f-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
An $m\times n$ bit matrix $x$ is indicated by $x\in\{0,1\}^{m\times n}$. We write $x_{i,j}$ to refer to the $(i,j)$-entry in $x$. We can also view $x$ as a sequence $x=(x_1,\ldots,x_m)$ of $m$ strings, each of length $n$, where $x_i$ is the $i$th row of the matrix, or we can view $x$ as a bit string of length $mn$, which is the concatenation of the rows of the matrix. The $\odot$ operation indicates matrix multiplication over $\mathrm{GF}[2]$. If $x\in\{0,1\}^n$ appears to the left of $\odot$ then it is considered to be a row vector, and if it appears to the right it is considered to be a column vector. Thus, if $x,y\in\{0,1\}^n$, then $x\odot y=\sum_{i=1}^n x_i y_i\pmod 2$. More generally, if $x\in\{0,1\}^{\ell\times m}$ and $y\in\{0,1\}^{m\times n}$ then $x\odot y$ is the $\ell\times n$ bit matrix whose $(i,j)$-entry is $r\odot c$, where $r$ is the $i$th row of $x$ and $c$ is the $j$th column of $y$.

<a id="pdf-130039751e9f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=1.00 -->
## 2.1 Probability Notation

<a id="pdf-130039751e9f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.96 -->
Random variables and events use uppercase or Greek symbols; variables are assumed independent unless stated otherwise. A distribution $D$ on finite $S$ assigns nonnegative masses summing to $1$; $X\sim D$ means $\Pr[X=x]=D(x)$. The notation $D:\{0,1\}^{\ell}$ indicates support on strings of length $\ell$. Conditional variables use the conditional law, and applying $f:S\to T$ induces $f(D)(y)=\sum_{x\in S:f(x)=y}D(x)$. The notation $X\sim U_S$ means uniform on $S$, and lowercase samples denote fixed draws from the indicated law. $\mathbb E[X]$ and $\Pr[E]$ denote expectation and event probability.

<a id="pdf-130039751e9f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
**Definition 2.1.1 (statistical distance).** For distributions $D,E$ on $S$, $\|D-E\|_1=\frac12\sum_{x\in S}|D(x)-E(x)|$.

<a id="pdf-130039751e9f-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.99 -->
**Proposition 2.1.2.** For any $f$ with domain $S$ and distributions $D,E$ on $S$, $\|f(D)-f(E)\|_1\leq \|D-E\|_1$.

<a id="pdf-130039751e9f-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=1.00 -->
## 2.2 Entropy

<a id="pdf-130039751e9f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.99 -->
**Definition 2.2.1 (information and entropy).** Let $\mathcal D$ be a distribution on a set $S$. For each $x\in S$, define the information of $x$ with respect to $\mathcal D$ to be $I_{\mathcal D}(x)=-\log(\mathcal D(x))$. Let $X\in_{\mathcal D}S$. The (Shannon) entropy of $\mathcal D$ is $H(\mathcal D)=\mathbb E[I_{\mathcal D}(X)]$. Let $\mathcal D_1$ and $\mathcal D_2$ be distributions on $S$ that are not necessarily independent, and let $X_1\in_{\mathcal D_1}S$ and $X_2\in_{\mathcal D_2}S$. Then the conditional entropy of $\mathcal D_1$ with respect to $\mathcal D_2$, $H(\mathcal D_1\mid\mathcal D_2)$, is $\mathbb E_{x_2\in_{\mathcal D_2}}[H(X_1\mid X_2=x_2)]$.

<a id="pdf-130039751e9f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.99 -->
**Definition 2.2.2 (Rényi entropy).** For $D$ on $S$, let $X,Y$ be independent samples from $D$. Then $H_{\mathrm{Ren}}(D)=-\log\Pr[X=Y]$.

<a id="pdf-130039751e9f-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.98 -->
The text notes that Shannon entropy can be arbitrarily larger than Rényi entropy.

<a id="pdf-130039751e9f-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.99 -->
**Proposition 2.2.3.** For every distribution $D$, $H_{\mathrm{Ren}}(D)\leq H(D)$.

<a id="pdf-130039751e9f-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.99 -->
**Proposition 2.2.4.** For any function $f$ and distribution $D$ on its domain, $H(f(D))\leq H(D)$.

<a id="pdf-130039751e9f-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.98 -->
**Definition 2.2.5 (degeneracy of $f$).** For $f:\{0,1\}^n\to\{0,1\}^{\ell}$ and uniform $X\in\{0,1\}^n$, define $D(f)=H(X\mid f(X))=H(X)-H(f(X))$.

<a id="pdf-130039751e9f-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=1.00 -->
## 2.3 Ensembles

<a id="pdf-130039751e9f-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.99 -->
Ensembles express asymptotic definitions and results, including cryptographic primitives and adversaries.

<a id="pdf-130039751e9f-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
The index is $n\in\mathbb N$, with definitions and results understood for each $n$. Input and output lengths are polynomially related.

<a id="pdf-130039751e9f-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.99 -->
**Definition 2.3.1 (polynomial parameter).** We say parameter $k_n$ is a polynomial parameter if there is a constant $c>0$ such that for all $n\in\mathbb N$, $\frac{1}{c n^c}\leq k_n\leq c n^c$. We say $k_n$ is a $P$-time polynomial parameter if in addition there is a constant $c'>0$ such that, for all $n$, $k_n$ is computable in time at most $c'n^{c'}$.

<a id="pdf-130039751e9f-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.92 -->
**Definition 2.3.2 (function ensemble).** The notation $f:\{0,1\}^{t_n}\to\{0,1\}^{\ell_n}$ denotes a family of functions where $t_n,\ell_n$ are integer-valued polynomial-time parameters and each $f_n$ maps the indicated lengths. Injective families are one-to-one function ensembles; if also $\ell_n=t_n$, they are permutation ensembles. The notation $f:\{0,1\}^{t_n}\times\{0,1\}^{m_n}\to\{0,1\}^{\ell_n}$ denotes a two-input ensemble; with first input fixed at $x$, write $f_x(y)=f(x,y)$.

<a id="pdf-130039751e9f-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.94 -->
**Definition 2.3.3 (P-time function ensemble).** A two-input ensemble is a $T_n$-time ensemble if $f(x,y)$ is computable within $T_n$ for every valid $x,y$. It is a polynomial-time ensemble if $T_n\leq c n^c$ for some constant $c$. A mildly nonuniform polynomial-time ensemble additionally takes an advice input of integer-valued polynomial length, not necessarily polynomial-time computable.

<a id="pdf-130039751e9f-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.96 -->
The definitions extend to functions with more inputs. Variable-length strings are understood to be padded with a blank symbol; the text begins to introduce statistical quantities used in reductions.

<a id="pdf-130039751e9f-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
The text motivates mildly non-uniform ensembles: relevant approximation values may be few, and the final pseudorandom-generator construction later removes this mild non-uniformity.

<a id="pdf-130039751e9f-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.97 -->
**Definition 2.3.4.** For a function ensemble $f_n:\{0,1\}^n\to\{0,1\}^{\ell(n)}$, define $\operatorname{range}_{f_n}=\{f_n(x):x\in\{0,1\}^n\}$. For $y\in\operatorname{range}_{f_n}$, define $\operatorname{pre}_{f_n}(y)=\{x\in\{0,1\}^n:f_n(x)=y\}$.

<a id="pdf-130039751e9f-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.94 -->
**Definition 2.3.5.** A function ensemble $f_n:\{0,1\}^n\to\{0,1\}^{\ell(n)}$ is $\sigma$-regular if $|\operatorname{pre}_{f_n}(y)|=\sigma(n)$ for every $y\in\operatorname{range}_{f_n}$.

<a id="pdf-130039751e9f-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.99 -->
**Definition 2.3.6 ($\widetilde D_f$).** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble. For $z\in\operatorname{range}_f$, define the approximate degeneracy of $z$ as $\widetilde D_f(z)=\lfloor\log(|\operatorname{pre}_f(z)|)\rfloor$. Notice that $\widetilde D_f(z)$ is an approximation to within an additive factor of 1 of $n-I_{f(X)}(z)$. Furthermore, $\mathbb E[\widetilde D_f(f(X))]$ is within an additive factor of 1 of the degeneracy of $f$. If $f$ is a $\sigma_n$-regular function, then for each $z\in\operatorname{range}_f$, $\widetilde D_f(z)$ is within an additive factor of 1 of $\log(\sigma_n)$, which is the degeneracy of $f$.

<a id="pdf-130039751e9f-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.96 -->
**Definition 2.3.7.** A probability ensemble $D:\{0,1\}^{\ell(n)}$ has an integer-valued $P$-time polynomial parameter $\ell(n)$, and for each $n$, $D_n$ is a distribution on $\{0,1\}^{\ell(n)}$.

<a id="pdf-130039751e9f-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.95 -->
**Definition 2.3.8.** A probability ensemble $D$ on $\{0,1\}^{\ell(n)}$ is samplable if there is a function ensemble $f_n:\{0,1\}^{r(n)}\to\{0,1\}^{\ell(n)}$ such that uniform $X\in\{0,1\}^{r(n)}$ yields $f_n(X)\sim D_n$. It is $T_U$-samplable if every $f_n(x)$ is computable in time $T_U(n)$; it is $P$-samplable if $f$ is a $P$-time function ensemble, and mildly non-uniformly $P$-samplable if $f$ is mildly non-uniform $P$-time.

<a id="pdf-130039751e9f-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Definition 2.3.9.** Let $k(n)$ be an integer-valued $P$-time polynomial parameter. For a probability ensemble $D$, $D^{k(n)}_n$ is the distribution of the concatenation of $k(n)$ independent samples from $D_n$. For $f_n:\{0,1\}^{m(n)}\to\{0,1\}^{\ell(n)}$, define $f^{k(n)}_n:\{0,1\}^{k(n)m(n)}\to\{0,1\}^{k(n)\ell(n)}$ by $f^{k(n)}_n(y_1,\ldots,y_{k(n)})=\langle f_n(y_1),\ldots,f_n(y_{k(n)})\rangle$.

<a id="pdf-130039751e9f-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.99 -->
Introduces adversary security and the cryptographic primitives used in the paper.

<a id="pdf-130039751e9f-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
Defines adversarial breaking ability using a time-success ratio; distinguishes public inputs, known to the adversary, from private inputs, whose length is the security parameter.

<a id="pdf-130039751e9f-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.99 -->
Public inputs can still help constructions because they are randomly selected, so an adversary cannot tailor one strategy to every possible value in advance.

<a id="pdf-130039751e9f-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->
**Definition 3.1.1.** An adversary $A$ is a function ensemble. For primitive instance $f$ with private-input length $t_n$, define its time-success ratio as $R_n=T_n/\operatorname{sp}_n(A)$, where $T_n$ is the worst-case expected running time of $A$ over instances parameterized by $n$, and $\operatorname{sp}_n(A)$ is its success probability in breaking $f$. Then $A$ is an $R$-breaking adversary for $f$, and $f$ is $R$-secure if no such adversary exists. A mildly non-uniform adversary receives advice $a_n$ as an additional input; its success probability and ratio are defined as for uniform adversaries.

<a id="pdf-130039751e9f-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.99 -->
The definition of the success probability $sp_n(A)$ for $f$ depends on the primitive in question, i.e., this probability is defined when the primitive is defined. Intuitively, the smaller the time-success ratio of an adversary for a primitive, the better the adversary is able to break the primitive, i.e., it uses less time and/or has a larger success probability. The above definitions are a refinement of definitions that appear in the literature. Previously, an adversary was considered to be breaking if it ran in polynomial time and had inverse polynomial success probability. The advantage of the definition introduced here is that it is a more precise characterization of the security of a primitive. This is important because different applications require different levels of security. For some applications polynomial security is enough (e.g., $R_{t_n}=t_n^{10}$) and for other applications better security is crucial (e.g., $R_{t_n}=2^{\log^2(t_n)}$, or even better $R_{t_n}=2^{\sqrt{t_n}}$).

<a id="pdf-130039751e9f-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.99 -->
Introduces one-way functions.

<a id="pdf-130039751e9f-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.94 -->
**Definition 3.2.1.** Let $f_n:\{0,1\}^{t_n}\to\{0,1\}^{\ell(n)}$ be a $P$-time function ensemble and let $X$ be uniform on $\{0,1\}^{t_n}$. The inversion success probability of adversary $A$ is $\operatorname{sp}_n(A)=\Pr[f_n(A(f_n(X)))=f_n(X)]$. The function is an $R$-secure one-way function if no $R$-breaking adversary exists.

<a id="pdf-130039751e9f-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.99 -->
A function cannot be considered to be “one-way” in any reasonable sense in case the time to invert it is smaller than the time to evaluate it in the forward direction. Thus, for example, if there is an $O(t_n)$-breaking adversary for $f$ then it is not secure at all. On the other hand, an exhaustive adversary that tries all possible inputs to find an inverse is $t_n^{O(1)}\cdot 2^{t_n}$-breaking. Thus, the range of securities that can be hoped for fall between these two extremes.

<a id="pdf-130039751e9f-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=1.00 -->
## 3.3 Pseudorandom generator

<a id="pdf-130039751e9f-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
Computational indistinguishability models statistical distance against restricted adversaries; the cited origins are Goldreich–Micali and Yao.

<a id="pdf-130039751e9f-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.99 -->
**Definition 3.3.1 (computationally indistinguishable).** Let $\mathcal D:\{0,1\}^{\ell_n}$ and $\mathcal E:\{0,1\}^{\ell_n}$ be probability ensembles. The success probability of adversary $A$ for distinguishing $\mathcal D$ and $\mathcal E$ is $sp_n(A)=|\Pr[A(X)=1]-\Pr[A(Y)=1]|$, where $X$ has distribution $\mathcal D$ and $Y$ has distribution $\mathcal E$. $\mathcal D$ and $\mathcal E$ are $\mathbf R$-secure computationally indistinguishable if there is no $\mathbf R$-breaking adversary for distinguishing $\mathcal D$ and $\mathcal E$.

<a id="pdf-130039751e9f-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
An alternative measure squares the distinguishing advantage, reflecting that roughly $1/\operatorname{sp}_n(A)^2$ trials estimate the advantage within a constant factor.

<a id="pdf-130039751e9f-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.96 -->
**Definition 3.3.2.** As in Definition 3.3.1, but use $\operatorname{sp}'_n(A)=(\operatorname{sp}_n(A))^2$ as the success probability.

<a id="pdf-130039751e9f-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.88 -->
The text generally uses Definition 3.3.1; the alternative is invoked where it yields a linear-preserving reduction. Although the formal definition uses security parameter $n$, typical ensembles arise from samplers whose private-input length is the security parameter; some results require both distributions to be polynomial-time samplable.

<a id="pdf-130039751e9f-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.99 -->
**Definition 3.3.3 (pseudorandom generator).** Let $g:\{0,1\}^{t_n}\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble where $\ell_n>t_n$. Then, $g$ is a $\mathbf R$-secure pseudorandom generator if the probability ensembles $g(U_{t_n})$ and $U_{\ell_n}$ are $\mathbf R$-secure computationally indistinguishable.

<a id="pdf-130039751e9f-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
The next result extends a one-bit-stretch generator to a generator with polynomially many additional output bits; it is attributed to Goldreich and Micali.

<a id="pdf-130039751e9f-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.99 -->
**Proposition 3.3.4.** Suppose $g:\{0,1\}^n\to\{0,1\}^{n+1}$ is a pseudorandom generator that stretches by one bit. Define $g^{(1)}(x)=g(x)$, and inductively, for all $i\geq1$,
\[
g^{(i+1)}(x)=\langle g(g^{(i)}(x)_{\{1,\ldots,n\}}),\;g^{(i)}(x)_{\{n+1,\ldots,n+i\}}\rangle.
\]
Let $k_n$ be an integer-valued $P$-time polynomial parameter. Then $g^{(k_n)}$ is a pseudorandom generator. The reduction is linear-preserving.

<a id="pdf-130039751e9f-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.97 -->
The accompanying intuition is that security of the iterated generator is close to that of $g$; formal reduction terminology is deferred to page 16.

<a id="pdf-130039751e9f-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=1.00 -->
## 3.4 Pseudoentropy and false-entropy generators

<a id="pdf-130039751e9f-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.98 -->
A pseudoentropy generator need only resemble an ensemble with greater entropy than its input, rather than uniform output; its extra randomness is computational rather than necessarily statistical.

<a id="pdf-130039751e9f-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.99 -->
**Definition 3.4.1 (computational entropy).** Let $f:\{0,1\}^{t_n}\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble and let $s_n$ be a polynomial parameter. Then, $f$ has $\mathbf R$-secure computational entropy $s_n$ if there is a $P$-time function ensemble $f':\{0,1\}^{m_n}\to\{0,1\}^{\ell_n}$ such that $f(U_{t_n})$ and $f'(U_{m_n})$ are $\mathbf R$-secure computationally indistinguishable and $H(f'(U_{m_n}))\geq s_n$.

<a id="pdf-130039751e9f-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.91 -->
**Definition 3.4.2.** For polynomial-time $f:\{0,1\}^t\to\{0,1\}^{\ell}$ and polynomial parameter $s_n$, $f$ is an $R_n$-secure pseudoentropy generator with pseudoentropy $s_n$ when $f(U_t)$ has $R_n$-secure computational entropy $t+s_n$.

<a id="pdf-130039751e9f-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->
A pseudorandom generator with output length $\ell>t$ is a pseudoentropy generator with pseudoentropy at least $1$: its output is computationally indistinguishable from $U_\ell$, and $H(U_\ell)=\ell\ge t+1$.

<a id="pdf-130039751e9f-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.94 -->
A false-entropy generator may fail to increase actual randomness; it requires only computational entropy exceeding the output's Shannon entropy.

<a id="pdf-130039751e9f-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.88 -->
**Definition 3.4.3.** For polynomial-time $f:\{0,1\}^t\to\{0,1\}^{\ell}$ and polynomial parameter $s_n$, $f$ is an $R_n$-secure false-entropy generator with false-entropy $s_n$ if $f(U_t)$ has $R_n$-secure computational entropy $H(f(U_t))+s_n$.

<a id="pdf-130039751e9f-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.91 -->
The witness ensemble $f'$ in computational entropy is polynomial-time computable. A nonuniform variant drops that requirement; the text notes that such false-entropy generators are easier to construct from one-way functions, while uniform reductions through Proposition 4.6.2 require polynomial-time computability of $f'$.

<a id="pdf-130039751e9f-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=1.00 -->
## 3.5 Hidden bits

<a id="pdf-130039751e9f-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.96 -->
A key construction goal is an output bit computationally unpredictable from the other bits but statistically somewhat predictable; this idea appears in the discrete-log PRG construction and later work.

<a id="pdf-130039751e9f-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.00 -->


<a id="pdf-130039751e9f-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.96 -->
A bit-valued random variable $b(X)$ is computationally hidden given $f(X)$ when $(f(X),b(X))$ and $(f(X),U)$ are computationally indistinguishable, with $U$ an independent uniform bit.

<a id="pdf-130039751e9f-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
Introduces reductions between primitives and measures how much security they preserve.

<a id="pdf-130039751e9f-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.99 -->
**Definition 3.6.1 (reduction).** Let $t_n$ and $t'_n$ be polynomial parameters and let $S:\mathbb N\times\mathbb R^+\to\mathbb R^+$. An $S$-reduction from primitive 1 to primitive 2 is a pair of oracle TMs $g^{(\cdot)}$ and $M^{(\cdot)}$ so that: for each $P$-time function ensemble $f:\{0,1\}^{t_n}\to\{0,1\}^{\ell_n}$ that instantiates primitive 1, $g^{(f)}:\{0,1\}^{t'_n}\to\{0,1\}^{\ell'_n}$ instantiates primitive 2; $g^{(f)}$ is a $P$-time function ensemble and on inputs of length $t'_n$ only makes calls to $f$ on inputs of length $t_n$; and if $A$ is an adversary with time-success ratio $R'_{t'_n}$ for $g^{(f)}$ on inputs of length $t'_n$, define $R_{t_n}=S(n,R'_{t'_n})$. Then $M^{(A)}$ is an adversary with time-success ratio $R_{t_n}$ for $f$ on inputs of length $t_n$.

<a id="pdf-130039751e9f-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.98 -->
The reduction is linear-preserving if $R_N=N^{O(1)}\cdot O(R'_N)$; poly-preserving if $R_N=N^{O(1)}\cdot (R'_{O(N)})^{O(1)}$; and weak-preserving if $R_N=N^{O(1)}\cdot (R'_{N^{O(1)}})^{O(1)}$.

<a id="pdf-130039751e9f-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.96 -->
A mildly non-uniform reduction additionally lets $g$ and $M$ use an integer-valued polynomial parameter depending on $f$; the preservation classifications extend to this setting.

<a id="pdf-130039751e9f-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.98 -->
$f$ can always be broken in time exponential in $t_n$. Therefore, if $R'_{t'_n}\geq 2^{t_n}$, or even $R'_{t'_n}\geq 2^{n^{S(n,1)}}=2^{n^{S(1)}}$ in the case of a weak-preserving reduction, $M^{(A)}$ can ignore the oracle and break $f$ by brute force. Therefore, we can assume without loss of generality that $R'_{t'_n}\leq 2^{t_n}$.

<a id="pdf-130039751e9f-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.98 -->
**Proposition 3.6.2.** If $(g^{(\cdot)},M^{(\cdot)})$ is a (mildly non-uniform) $S$-reduction from primitive 1 to primitive 2 and $f$ is a (mildly non-uniform) $P$-time function ensemble that instantiates primitive 1 with security $R_{t_n}$, then $g^{(f)}$ is a (mildly non-uniform) $P$-time function ensemble that instantiates primitive 2 with security $R'_{t'_n}$, where $R_{t_n}=S(n,R'_{t'_n})$.

<a id="pdf-130039751e9f-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.92 -->
**Proposition 3.6.3.** Composition of an $S_1$-reduction from primitive 1 to 2 and an $S_2$-reduction from 2 to 3 gives a (possibly mildly non-uniform) reduction from 1 to 3 with $S(N,R)=S_1(N,S_2(N,R))$.

<a id="pdf-130039751e9f-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.88 -->
Typically $t_n\ge t'_n$ and $R\ge R'$. Security transfer improves as these inequalities approach equality. The number of calls to $A$ is at most polynomial in $R/R'$, so the main loss usually comes from the increase from $t'_n$ to $t_n$.

<a id="pdf-130039751e9f-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.96 -->
If $t'_n=t_n$, $M^{(A)}$ runs in time polynomial in $n$ (not counting the running time of $A$), and $sp_n(M^{(A)})=sp_n(A)/n^{O(1)}$, then the reduction is linear-preserving. If $t'_n=O(t_n)$, $M^{(A)}$ runs in time polynomial in $R'_{t'_n}$, and $sp_n(M^{(A)})=sp_n^{O(1)}(A)/n^{O(1)}$, then the reduction is poly-preserving. If $t'_n=t_n^{O(1)}$, $M^{(A)}$ runs in time polynomial in $R'_{t'_n}$, and $sp_n(M^{(A)})=sp_n^{O(1)}(A)/n^{O(1)}$, then the reduction is weak-preserving.

<a id="pdf-130039751e9f-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.95 -->
The strongest feasible reduction is desirable: regular or nearly regular one-way functions admit poly-preserving reductions to pseudorandom generators, whereas the general case is only weak-preserving.

<a id="pdf-130039751e9f-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.99 -->
Begins the treatment of hidden bits, hash functions, and computational entropy.

<a id="pdf-130039751e9f-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.99 -->
Introduces a method for making an output bit computationally unpredictable while statistically correlated with the other output bits.

<a id="pdf-130039751e9f-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.87 -->
**Proposition 4.1.1.** If $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ is one-way, then $X\oplus R$ is hidden given $\langle f(X),R\rangle$, for uniform $X,R\in\{0,1\}^n$. The reduction is linear-preserving under the alternative definition of computational indistinguishability.

<a id="pdf-130039751e9f-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.91 -->
**Proposition 4.1.2.** There is an oracle TM $M$ with the following properties. Let $A$ be any adversary that accepts as input $n$ bits and outputs a single bit. Then $M^{(A)}$ on input parameter $\delta_n>0$ outputs a list $L$ of $n$-bit strings with the following property: for any fixed $x\in\{0,1\}^n$, if
\[
|\Pr[A(R)=x\oplus R]-\Pr[A(R)\ne x\oplus R]|\geq\delta_n,
\]
where $R\in_U\{0,1\}^n$, then with probability at least $1/2$, $x\in L$. The running time of $M^{(A)}$ is polynomial in $n$, $1/\delta_n$, and the running time of $A$. Also, the number of $n$-bit strings in $L$ is bounded by $O(1/\delta_n^2)$.

<a id="pdf-130039751e9f-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.98 -->
The source begins specifying the runtime of $M^A$ at the page bottom, but the bound is cut off and cannot be recovered.

<a id="pdf-130039751e9f-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.99 -->
The running time of $M^{(A)}$ is polynomial in $n$, $1/\delta_n$, and the running time of $A$. Also, the number of $n$-bit strings in $L$ is bounded by $O(1/\delta_n^2)$.

<a id="pdf-130039751e9f-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.99 -->
**Proposition 4.1.3.** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a one-way function. Then, $\langle f(X),R,X\odot R\rangle$ and $\langle f(X),R,\beta\rangle$ are computationally indistinguishable, where $X,R\in_U\{0,1\}^n$ and $\beta\in_U\{0,1\}$. The reduction is linear-preserving with respect to the alternative definition of computational indistinguishability.

<a id="pdf-130039751e9f-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.99 -->
## 4.2 One-way permutation to a pseudorandom generator

<a id="pdf-130039751e9f-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.99 -->
A simpler construction than Yao’s uses any one-way permutation to obtain a pseudorandom generator, with stronger security preservation; the construction and proof are attributed to Goldreich–Levin.

<a id="pdf-130039751e9f-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.91 -->
**Proposition 4.2.1.** If f:{0,1}ⁿ→{0,1}ⁿ is a one-way permutation, then g(x,r)=⟨f(x),r,x·r⟩, for x,r∈{0,1}ⁿ, is a polynomial-time pseudorandom generator. Its reduction is linear-preserving under the alternative definition of computational indistinguishability.

<a id="pdf-130039751e9f-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.94 -->
**Proof.** Let X,R be uniform on {0,1}ⁿ and β uniform on {0,1}. Since f is a permutation, ⟨f(X),R,β⟩ is uniform on {0,1}²ⁿ⁺¹. Proposition 4.1.3 gives computational indistinguishability of g(X,R)=⟨f(X),R,X·R⟩ from that uniform ensemble, with the stated linear-preserving reduction.

<a id="pdf-130039751e9f-p019-b007"></a>
<!-- pdf-source: page=19; block=7; confidence=0.95 -->
The permutation ensures that f(X) is uniform and that f(x) uniquely determines x, so applying f loses no entropy. For general one-way functions, later constructions use hashing to smooth f(X)’s entropy and recover entropy lost from X.

<a id="pdf-130039751e9f-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.99 -->
Proposition 4.2.1 gives one-bit stretch; combining it with Proposition 3.3.4 yields a generator with larger stretch.

<a id="pdf-130039751e9f-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.99 -->
## 4.3 One-to-one one-way function to a pseudoentropy generator

<a id="pdf-130039751e9f-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.99 -->
The same construction as in Proposition 4.2.1 turns a one-to-one one-way function into a pseudoentropy generator; together with Theorem 4.6.4 this yields a pseudorandom generator.

<a id="pdf-130039751e9f-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.99 -->
**Proposition 4.3.1.** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a one-to-one one-way function. Let $x,r\in\{0,1\}^n$ and define the $P$-time function ensemble $g(x,r)=\langle f(x),r,x\odot r\rangle$. Then, $g$ is a pseudoentropy generator with pseudoentropy 1. The reduction is linear-preserving with respect to the alternative definition of computationally indistinguishable.

<a id="pdf-130039751e9f-p020-b005"></a>
<!-- pdf-source: page=20; block=5; confidence=0.99 -->
Because $f$ is a one-to-one function and $\beta$ is a random bit, $H(f(X),R,\beta)=2n+1$, and thus $g(X,R)$ has pseudoentropy 1.

<a id="pdf-130039751e9f-p020-b006"></a>
<!-- pdf-source: page=20; block=6; confidence=0.98 -->
The construction need not be pseudorandom: if f(x)=⟨0,f₀(x)⟩ for a one-way permutation f₀, then f is one-to-one and one-way, but g’s first output bit is always zero, which distinguishes it from uniform.

<a id="pdf-130039751e9f-p020-b007"></a>
<!-- pdf-source: page=20; block=7; confidence=0.99 -->
## 4.4 Universal hash functions

<a id="pdf-130039751e9f-p020-b008"></a>
<!-- pdf-source: page=20; block=8; confidence=0.99 -->
Universal hashing, introduced by Carter–Wegman, has broad applications in computation.

<a id="pdf-130039751e9f-p020-b009"></a>
<!-- pdf-source: page=20; block=9; confidence=0.99 -->
**Definition 4.4.1 (universal hash functions).** Let $h:\{0,1\}^{\ell_n}\times\{0,1\}^n\to\{0,1\}^{m_n}$ be a $P$-time function ensemble. Recall from Definition 2.3.2 that for fixed $y\in\{0,1\}^{\ell_n}$, we view $y$ as describing a function $h_y(\cdot)$ that maps $n$ bits to $m_n$ bits. Then, $h$ is a (pairwise independent) universal hash function if, for all distinct $x,x'\in\{0,1\}^n$ and all $a,a'\in\{0,1\}^{m_n}$,
\[
\Pr[(h_Y(x)=a)\text{ and }(h_Y(x')=a')]=1/2^{2m_n},
\]
where $Y\in_U\{0,1\}^{\ell_n}$.

<a id="pdf-130039751e9f-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.99 -->
For each distinct input pair, the two hash outputs are jointly uniform and independent over the random hash description Y. In the constructions below, the hash description is public and included in the output.

<a id="pdf-130039751e9f-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=0.99 -->
**Definition 4.4.2 (matrix construction).** Let $h:\{0,1\}^{(n+1)m_n}\times\{0,1\}^n\to\{0,1\}^{m_n}$ be the following $P$-time function ensemble. For $x\in\{0,1\}^n$ and $y\in\{0,1\}^{(n+1)\times m_n}$, $h_y(x)=\langle x,1\rangle\odot y$.

<a id="pdf-130039751e9f-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.99 -->
## 4.5 Smoothing distributions with hashing

<a id="pdf-130039751e9f-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=0.99 -->
The next lemma is a key ingredient in subsequent reductions.

<a id="pdf-130039751e9f-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=0.99 -->
**Lemma 4.5.1.** Let $\mathcal D:\{0,1\}^n$ be a probability ensemble that has Renyi entropy at least $m_n$. Let $e_n$ be a positive integer-valued parameter. Let $h:\{0,1\}^{\ell_n}\times\{0,1\}^n\to\{0,1\}^{m_n-2e_n}$ be a universal hash function. Let $X\in_{\mathcal D}\{0,1\}^n$, $Y\in_U\{0,1\}^{\ell_n}$, and $Z\in_U\{0,1\}^{m_n-2e_n}$. Then $L_1(\langle h_Y(X),Y\rangle,\langle Z,Y\rangle)\leq 2^{-(e_n+1)}$.

<a id="pdf-130039751e9f-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.98 -->
The lemma says a universal hash function turns much of the Rényi entropy of its input into nearly uniform output bits while retaining the independent seed; its parameter controls the uniformity–entropy tradeoff.

<a id="pdf-130039751e9f-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=0.99 -->
For all $a\in\{0,1\}^s$, the proof establishes
\[
\mathbb E_Y\left[\left|\mathbb E_X[\chi(h_Y(X)=a)]-2^{-s}\right|\right]\leq 2^{-(s+e)}.
\]
By Jensen, it suffices to show the second moment is at most $2^{-2(s+e)}$. Let $X'$ be an independent sample from $\mathcal D$. Expanding gives
\[
\mathbb E_{X,X'}\mathbb E_Y[(\chi(h_Y(X)=a)-2^{-s})(\chi(h_Y(X')=a)-2^{-s})].
\]
For $x\ne x'$, pairwise independence makes the expectation over $Y$ zero. For $x=x'$, it is $2^{-s}(1-2^{-s})\leq2^{-s}$. Since the Renyi entropy of $\mathcal D$ is at least $m$, $\Pr[X=X']\leq2^{-m}$. Thus the sum is at most $2^{-(m+s)}=2^{-2(s+e)}$, since $s=m-2e$.

<a id="pdf-130039751e9f-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.98 -->
Proposition 2.2.3 lets the preceding lemma apply when the source has enough Rényi entropy. For Shannon-entropy sources, Proposition 4.5.2 supplies a product-distribution conversion.

<a id="pdf-130039751e9f-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.97 -->
**Proposition 4.5.2.** Let $k_n$ be an integer-valued polynomial parameter.

- Let $\mathcal D:\{0,1\}^n$ be a probability ensemble. There is a probability ensemble $\mathcal E:\{0,1\}^{nk_n}$ satisfying
\[
H_{\rm Ren}(\mathcal E)\geq k_n H(\mathcal D)-n k_n^{2/3},\qquad L_1(\mathcal E,\mathcal D^{k_n})\leq2^{-k_n^{1/3}}.
\]
- Let $\mathcal D_1,\mathcal D_2:\{0,1\}^n$ be not necessarily independent probability ensembles, and let $\mathcal D=\langle\mathcal D_1,\mathcal D_2\rangle$. There is a probability ensemble $\mathcal E=\langle\mathcal E_1,\mathcal E_2\rangle$ on paired strings of length $2nk_n$ satisfying, for every $E_1$ with $\Pr_{\mathcal E_1}[E_1]>0$, $H_{\rm Ren}(\mathcal E_2\mid\mathcal E_1=E_1)\geq k_n H(\mathcal D_2\mid\mathcal D_1)-n k_n^{2/3}$, and $L_1(\mathcal E,\mathcal D^{k_n})\leq2^{-k_n^{1/3}}$.

<a id="pdf-130039751e9f-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=0.97 -->
**Corollary 4.5.3.** Let $k_n$ be an integer-valued $P$-time polynomial parameter.

- Let $\mathcal D:\{0,1\}^n$ be a probability ensemble, let $m_n=k_nH(\mathcal D)-2nk_n^{2/3}$, and let $h:\{0,1\}^{p_n}\times\{0,1\}^{nk_n}\to\{0,1\}^{m_n}$ be universal. Let $X'\in_{\mathcal D^{k_n}}\{0,1\}^{k_n\times n}$ and $Y\in_U\{0,1\}^{p_n}$. Then $L_1(\langle h_Y(X'),Y\rangle,\mathcal U_{m_n+p_n})\leq2^{1-k_n^{1/3}}$.
- Let $\mathcal D_1,\mathcal D_2:\{0,1\}^n$ be not necessarily independent probability ensembles, and let $\mathcal D=\langle\mathcal D_1,\mathcal D_2\rangle$. Let $m_n=k_nH(\mathcal D_2\mid\mathcal D_1)-2nk_n^{2/3}$. Let $h:\{0,1\}^{p_n}\times\{0,1\}^{nk_n}\to\{0,1\}^{m_n}$ be universal. Let $\langle X'_1,X'_2\rangle\in_{\mathcal D^{k_n}}\{0,1\}^{k_n\times2n}$ and let $Y\in_U\{0,1\}^{p_n}$. Then $L_1(\langle h_Y(X'_2),Y,X'_1\rangle,\langle\mathcal U_{m_n+p_n},X'_1\rangle)\leq2^{1-k_n^{1/3}}$.

<a id="pdf-130039751e9f-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.99 -->
**Proof.** Combine Proposition 4.5.2, Lemma 4.5.1, Proposition 2.1.2, and Proposition 2.2.3.

<a id="pdf-130039751e9f-p023-b005"></a>
<!-- pdf-source: page=23; block=5; confidence=0.98 -->
## 4.6 Pseudoentropy generator to a pseudorandom generator

The section constructs a pseudorandom generator from a pseudoentropy generator, beginning with two preliminary propositions.

<a id="pdf-130039751e9f-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.96 -->
**Proposition 4.6.1.** Let \(D_n,E_n\) be probability ensembles on \(\{0,1\}^n\), and let \(f_n:\{0,1\}^n\to\{0,1\}^{\ell_n}\) be a polynomial-time function ensemble. If \(D_n\) and \(E_n\) are computationally indistinguishable, then \(f_n(D_n)\) and \(f_n(E_n)\) are computationally indistinguishable, via a linear-preserving reduction.

<a id="pdf-130039751e9f-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=0.90 -->
**Proposition 4.6.2.** Let \(k_n\) be an integer-valued polynomial-time parameter and let \(D_n,E_n\) be \(\ell\)-samplable ensembles on \(\{0,1\}^n\). If they are computationally indistinguishable, then their \(k_n\)-fold product ensembles are computationally indistinguishable by a weak-preserving reduction. More precisely, an oracle probabilistic TM transforms any \(R\)-breaking distinguisher for the product ensembles into an \(R'_n\)-breaking distinguisher for \(D_n,E_n\), where \(R'_n\) is essentially \(k_n\). The sampler access is needed by the reduction; distinguishing products with private inputs of length \(nk_n\) yields only a distinguisher on private inputs of length \(n\).

<a id="pdf-130039751e9f-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=0.98 -->
The next construction builds a pseudorandom generator from a pseudoentropy generator.

<a id="pdf-130039751e9f-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=0.99 -->
**Construction 4.6.3.** Let $f:\{0,1\}^n\to\{0,1\}^{m_n}$ be a $P$-time function ensemble and let $s_n$ be a $P$-time polynomial parameter. Let $k_n=\lceil((2m_n+1)/s_n)^3\rceil$ and $j_n=\lfloor k_n(n+s_n)-2m_nk_n^{2/3}\rfloor$. Let $h:\{0,1\}^{p_n}\times\{0,1\}^{k_nm_n}\to\{0,1\}^{j_n}$ be a universal hash function. Let $u\in\{0,1\}^{k_n\times n}$, $y\in\{0,1\}^{p_n}$, and define $g(u,y)=\langle h_y(f^{k_n}(u)),y\rangle$.

<a id="pdf-130039751e9f-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=0.93 -->
**Theorem 4.6.4.** For \(f\) and \(g\) as in Construction 4.6.3, if \(f\) is a pseudoentropy generator with pseudoentropy \(s_n\), then \(g\) is a pseudorandom generator, with a weak-preserving reduction.

<a id="pdf-130039751e9f-p024-b006"></a>
<!-- pdf-source: page=24; block=6; confidence=0.98 -->
Let $f'$ be the $P$-time function ensemble that witnesses the pseudoentropy generator property of $f$: $f'(X')$ and $f(X)$ are $\mathbf R$-secure computationally indistinguishable and $H(f'(X'))\geq n+s_n$, where $X\in_U\{0,1\}^n$ and $X'\in_U\{0,1\}^{m_n}$. Let $U\in_U\{0,1\}^{k_n\times n}$, $W\in_U\{0,1\}^{k_n\times m_n}$, and $Y\in_U\{0,1\}^{p_n}$. By Proposition 4.6.2, $f^{k_n}(U)$ and $f'^{k_n}(W)$ are computationally indistinguishable. From Proposition 4.6.1 it follows that $g(U,Y)=\langle h_Y(f^{k_n}(U)),Y\rangle$ and $\langle h_Y(f'^{k_n}(W)),Y\rangle$ are computationally indistinguishable. The proof continues on page 25.

<a id="pdf-130039751e9f-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.99 -->
By choice of $k_n$ and $j_n$, using Corollary 4.5.3, it follows that $L_1(\langle h_Y(f'^{k_n}(W)),Y\rangle,\mathcal U_{j_n+p_n})\leq2^{-k_n^{1/3}}$. Thus, it follows that $g(U,Y)$ and $\mathcal U_{j_n+p_n}$ are computationally indistinguishable. Note that by choice of $k_n$, the output length $j_n+p_n$ of $g$ is longer than its input length $nk_n+p_n$.

<a id="pdf-130039751e9f-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=0.99 -->
### 4.7 False entropy generator to a pseudoentropy generator

<a id="pdf-130039751e9f-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=0.93 -->
Starting from a false entropy generator $f$ with false entropy $s_n$, the section seeks a mildly non-uniform pseudoentropy generator. It aims to extract entropy related to the degeneracy of $f$ while preserving false entropy; the challenge is that the inverse-count function may be non-polynomial-time and highly variable.

<a id="pdf-130039751e9f-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=0.88 -->
For an integer-valued polynomial parameter $k_n$ and uniform $U$, the false entropy and degeneracy of $f^{k_n}$ scale by $k_n$. A universal hash function is used to extract approximately the degeneracy of $f^{k_n}(U)$ bits.

<a id="pdf-130039751e9f-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.99 -->
**Construction 4.7.1.** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble. Let $s_n$ be a $P$-time polynomial parameter and assume for simplicity that $s_n\leq1$. Let $e_n$ be an approximation of $H(f(X))$ to within an additive factor of $s_n/8$, where $X\in_U\{0,1\}^n$. Fix $k_n=\lceil(4n/s_n)^3\rceil$ and $j_n=\lfloor k_n(n-e_n)-2n k_n^{2/3}\rfloor$. Let $h:\{0,1\}^{p_n}\times\{0,1\}^{nk_n}\to\{0,1\}^{j_n}$ be a universal hash function. For $u\in\{0,1\}^{k_n\times n}$ and $r\in\{0,1\}^{p_n}$, define $g(e_n,u,r)=\langle f^{k_n}(u),h_r(u),r\rangle$.

<a id="pdf-130039751e9f-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=0.94 -->
**Lemma 4.7.2.** For $f,g$ as in Construction 4.7.1, if $f$ is a false entropy generator with false entropy $s_n$, then $g$ is a mildly non-uniform pseudoentropy generator with pseudoentropy $1$. The reduction is weak-preserving.

<a id="pdf-130039751e9f-p025-b007"></a>
<!-- pdf-source: page=25; block=7; confidence=0.77 -->
First, note that $H(X\mid f(X))=n-H(f(X))=n-e_n$. From this and Corollary 4.5.3 (letting $X_1=f(X)$, $X_2=X$ in the corollary), it follows that $L_1(\langle g(e_n;U;R),\cdot\rangle,\langle f^{k_n}(U),Z,R\rangle)\leq2^{-k_n^{1/3}}$.

<a id="pdf-130039751e9f-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.91 -->
Since $H(f'(X'))\geq n+s_n$, by choice of $k_n$ and $j_n$, using Corollary 4.5.3, it follows that $L_1(\langle h_Y(f'^{k_n}(W)),Y\rangle,\mathcal U_{j_n+p_n})\leq2^{-k_n^{1/3}}$. Thus, $g(U,Y)$ and $\mathcal U_{j_n+p_n}$ are computationally indistinguishable. By the entropy bound in the proof, $g$ has computational entropy at least $p_n+nk_n+1$.

<a id="pdf-130039751e9f-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=0.99 -->
### 4.8 Mildly non-uniform to a uniform pseudorandom generator

<a id="pdf-130039751e9f-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=0.98 -->
**Proposition 4.8.1.** Let $a_n$ be any value in $\{0,\ldots,k_n\}$, where $k_n$ is an integer-valued $P$-time polynomial parameter. Let $g:\{0,1\}^{\lceil\log(k_n)\rceil}\times\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble, where $\ell_n>nk_n$. Let $x'\in\{0,1\}^{k_n\times n}$ and define $g'(x')=\bigoplus_{i=1}^{k_n}g(i,x'_i)$. Let $g$ be a mildly non-uniform pseudorandom generator when the first input is set to $a_n$. Then $g'$ is a pseudorandom generator. The reduction is weak-preserving.

<a id="pdf-130039751e9f-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.99 -->
For each $i=1,\ldots,k_n$, $M^{(A)}(i)$ works as follows. On input $u$ (and $i$), it randomly generates $x'_1,\ldots,x'_{i-1},x'_{i+1},\ldots,x'_{k_n}\in_U\{0,1\}^n$ and computes $v=\bigoplus_{j\ne i}g(j,x'_j)\oplus u$. Then $M^{(A)}(i)$ runs $A$ on input $v$ and outputs $A(v)$. By the nature of $\oplus$, if $u$ is chosen randomly according to $Z$ then $M^{(A)}(i)=1$ with probability $\Pr[A(Z)=1]$, whereas if $u$ is chosen randomly according to $g(i,X)$ then $M^{(A)}(i)=1$ with probability $\Pr[A(g'(X'))=1]$. Thus, for each value of $i$, $M^{(A)}(i)$ has distinguishing probability $sp_n(A)$ for $g(i,X)$ and $Z$.

<a id="pdf-130039751e9f-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.87 -->
For most fixed indices, $g(i;X)$ may be predictable, and a suitable pseudorandom index need not be polynomial-time computable; Proposition 4.8.1 addresses this by converting mild nonuniformity to uniformity. Its output stretch is strict when $\ell_n>nk_n$, and the reduction is weak-preserving because an adversary at input length $nk_n$ transfers to one at length $n$. If the strict stretch condition fails, apply Proposition 3.3.4 to stretch each fixed-index function and XOR the resulting outputs.

<a id="pdf-130039751e9f-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.99 -->
### 4.9 Summary

<a id="pdf-130039751e9f-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.96 -->
Section 4 establishes reductions from: one-way permutations to pseudorandom generators; one-to-one one-way functions to pseudorandom generators; pseudoentropy generators to pseudorandom generators; and false entropy generators to pseudorandom generators.

<a id="pdf-130039751e9f-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.99 -->
### 5 Extracting entropy from one-way functions

<a id="pdf-130039751e9f-p027-b005"></a>
<!-- pdf-source: page=27; block=5; confidence=0.94 -->
The section constructs a pseudoentropy generator from a one-way function whose number-of-inverses function is polynomial-time computable. Combined with the reductions summarized in Section 4, this yields a pseudorandom generator from such a one-way function.

<a id="pdf-130039751e9f-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=0.99 -->
To see where we get into trouble with the construction given in Proposition 4.3.1, suppose $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ is a $2^{n/4}$-regular one-way function, and let $X,R\in_U\{0,1\}^n$ and $\beta\in_U\{0,1\}$. Then, although $\langle f(X),R,X\odot R\rangle$ and $\langle f(X),R,\beta\rangle$ are computationally indistinguishable, $H(f(X),R,X\odot R)$ is only about $7n/4+1$, and thus we have lost about $n/4$ bits of the input entropy through the application of $f$. Similarly, although $X\odot R$ is hidden given $\langle f(X),R\rangle$, it is also almost completely statistically uncorrelated.

<a id="pdf-130039751e9f-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.99 -->
**Section 5.1. One-way function with approximable pre-image sizes to a pseudoentropy generator**

<a id="pdf-130039751e9f-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=0.91 -->
For a 2-regular one-way function, the earlier construction loses about n/4 bits of input entropy after applying f, despite computational indistinguishability of the stated distributions. The proposed repair appends a hash of x whose length depends on the degeneracy of f(x), then applies the earlier proposition.

<a id="pdf-130039751e9f-p028-b004"></a>
<!-- pdf-source: page=28; block=4; confidence=0.85 -->
The text first treats the case where the degeneracy function \(\widetilde D_f\) is a polynomial-time function ensemble.

<a id="pdf-130039751e9f-p028-b005"></a>
<!-- pdf-source: page=28; block=5; confidence=0.99 -->
**Construction 5.1.1.** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a $P$-time function ensemble, and suppose $\widetilde D_f$ is a $P$-time function ensemble. Let $h:\{0,1\}^{p_n}\times\{0,1\}^n\to\{0,1\}^{n+2}$ be a universal hash function. For $x\in\{0,1\}^n$ and $y\in\{0,1\}^{p_n}$, define $f'(x,y)=\langle f(x),h_y(x)_{\{1,\ldots,\widetilde D_f(f(x))+2\}},y\rangle$.

<a id="pdf-130039751e9f-p028-b006"></a>
<!-- pdf-source: page=28; block=6; confidence=0.89 -->
**Lemma 5.1.2.** For \(f,f'\) as in Construction 5.1.1: (1) if \(f\) is one-way, then \(f'\) is one-way, with a poly-preserving reduction; (2) for uniform independent \(X\in\{0,1\}^n\) and \(Y\in\{0,1\}^{p_n}\),
\[
H(f'(X,Y))\ge n+p_n-\tfrac12.
\]

<a id="pdf-130039751e9f-p028-b007"></a>
<!-- pdf-source: page=28; block=7; confidence=0.87 -->
**Proof.** Suppose adversary \(A\) inverts \(f'(X,Y)\) with probability \(\delta_n\) in time \(T_n\). The proof begins constructing an oracle Turing machine \(M^{(A)}\) which, on input \(z=f(x)\), finds a preimage of \(z\) with probability at least \(\delta_n^3/128\) for uniform \(x\).

<a id="pdf-130039751e9f-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.85 -->
Given \(z\), machine \(M^{(A)}\) computes \(\widetilde D_f(z)\), samples a uniform hash seed \(\alpha\in\{0,1\}^{\widetilde D_f(z)+2}\) and uniform \(y\in\{0,1\}^{p_n}\), then runs \(A(z;\alpha,y)\). It outputs the candidate \(x'\) if \(f(x')=z\).

<a id="pdf-130039751e9f-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.92 -->
Let $j_n=2\lceil\log(2/\delta_n)\rceil$. For all $z\in\operatorname{range}_f$, for all $y\in\{0,1\}^{p_n}$, define the random variable $\beta_{z,y}=h_y(W)_{\{1,\ldots,\widetilde D_f(z)-j_n\}}$, where $W\in_U\operatorname{pre}_f(z)$. By Lemma 4.5.1, $L_1(\langle\beta_{z,Y},Y\rangle,\langle\beta'_z,Y\rangle)\leq\delta_n/2$, for uniform $\beta'_z\in\{0,1\}^{\widetilde D_f(z)-j_n}$. Therefore, there is a $\gamma\in\{0,1\}^{2+j_n}$ such that $A$ inverts $f$ on input $\langle f(X),\langle\beta_{f(X),Y};\gamma\rangle,Y\rangle$ with probability at least $\delta_n/2$.

<a id="pdf-130039751e9f-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.82 -->
The collision bound implies that some seed \(\gamma\in\{0,1\}^{2+j}\) makes \(A\) invert \(f'\) on the augmented input with probability at least \(\delta_n/2\). Sampling \(\gamma\) uniformly gives success at least \(\delta_n^3/128\), matching the distribution used by \(M^{(A)}\). Its runtime is dominated by a call to \(A\), so the time-success ratio for inverting \(f\) is about \(128T_n/\delta_n^3\).

<a id="pdf-130039751e9f-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.99 -->
For any distinct $x,x'\in\operatorname{pre}_f(z)$, universality gives
\[
\Pr[h_Y(x)_{\{1,\ldots,\widetilde D_f(z)+2\}}=h_Y(x')_{\{1,\ldots,\widetilde D_f(z)+2\}}]=2^{-(\widetilde D_f(z)+2)}\leq\frac{1}{4|\operatorname{pre}_f(z)|}.
\]
By calculating the Renyi entropy it follows that $H(f'(X,Y))\geq-\log\bigl(\frac54\cdot2^{-n+p_n}\bigr)=n+p_n+2-\log(5)$. The result follows since $\log(5)\leq5/2$.

<a id="pdf-130039751e9f-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=0.99 -->
**Corollary 5.1.3.** Let $f,h$ and $f'$ be as described in Construction 5.1.1. Let $r\in\{0,1\}^n$ and define the $P$-time function ensemble $g(x,y,r)=\langle f'(x,y),r,x\odot r\rangle$. Let $f$ be a one-way function. Then, $g$ is a pseudoentropy generator with pseudoentropy $1/2$. The reduction is poly-preserving.

<a id="pdf-130039751e9f-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.86 -->
**Proof.** The argument follows Proposition 4.3.1. For uniform independent \(X,R,Y\) and \(\beta\), Lemma 5.1.2(1) and Proposition 4.1.3 give computational indistinguishability of \(g(X,Y,R)\) and \(\langle f'(X,Y),R,\beta\rangle\), with a poly-preserving reduction. Lemma 5.1.2(2) gives entropy at least \(2n+p_n+1/2\) for the latter, whereas the input entropy to \(g(X,Y,R)\) is \(2n+p_n\); hence the pseudoentropy is \(1/2\).

<a id="pdf-130039751e9f-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.93 -->
**Theorem 5.1.4.** If \(f\) is a one-way function and \(\widetilde D_f\) is a polynomial-time function ensemble, then a pseudorandom generator can be constructed from \(f\), with a weak-preserving reduction.

<a id="pdf-130039751e9f-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.96 -->
**Proof.** Combine Construction 5.1.1 with Construction 4.6.3, using Corollary 5.1.3 and Theorem 4.6.4.

<a id="pdf-130039751e9f-p030-b005"></a>
<!-- pdf-source: page=30; block=5; confidence=0.93 -->
The next result is noted as an earlier result of [GKL:93], obtained by different methods.

<a id="pdf-130039751e9f-p030-b006"></a>
<!-- pdf-source: page=30; block=6; confidence=0.99 -->
**Theorem 5.1.5.** Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a $\sigma_n$-regular one-way function, where $\sigma_n$ is a $P$-time polynomial parameter. Then, a pseudorandom generator can be constructed from $f$. The reduction is weak-preserving.

<a id="pdf-130039751e9f-p030-b007"></a>
<!-- pdf-source: page=30; block=7; confidence=0.85 -->
**Proof.** In this case \(\widetilde D_f(f(x))=\lceil\log\sigma_n\rceil\) for every \(x\), and \(\lceil\log\sigma_n\rceil\in\{0,\ldots,n\}\). The preceding constructions and results yield a mildly non-uniform pseudorandom generator; Theorem 4.8 converts it to a pseudorandom generator.

<a id="pdf-130039751e9f-p030-b008"></a>
<!-- pdf-source: page=30; block=8; confidence=0.94 -->
Luby [1996, Theorems 10.1 and 9.3] is cited for versions of Theorems 5.1.4 and 5.1.5 with poly-preserving reductions when the security parameter is polynomial-time computable.

<a id="pdf-130039751e9f-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=1.00 -->
## 6 Any one-way function to a false entropy generator

<a id="pdf-130039751e9f-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=1.00 -->
### 6.1 Finding determined hidden bits

<a id="pdf-130039751e9f-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.99 -->
The section constructs a false entropy generator from a one-way function; its main technical issue is obtaining an efficiently computable ensemble.

<a id="pdf-130039751e9f-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.98 -->
Let $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$ be a one-way function and let $h:\{0,1\}^{p_n}\times\{0,1\}^n\to\{0,1\}^{n+\lceil\log(2n)\rceil}$ be a universal hash function. Similar to Construction 5.1.1, for $x\in\{0,1\}^n$, $i\in\{0,\ldots,n-1\}$, and $r\in\{0,1\}^{p_n}$, define $f'(x,i,r)=\langle f(x),h_r(x)_{\{1,\ldots,i+\lceil\log(2n)\rceil\}},i,r\rangle$.

<a id="pdf-130039751e9f-p031-b005"></a>
<!-- pdf-source: page=31; block=5; confidence=0.94 -->
The restriction using $i=\widetilde D_f(f(x))$ is almost one-to-one by Lemma 5.1.2, but may fail to be a polynomial-time ensemble; this is the obstacle addressed next.

<a id="pdf-130039751e9f-p031-b006"></a>
<!-- pdf-source: page=31; block=6; confidence=0.99 -->
Let $T=\{\langle x,i\rangle\mid x\in\{0,1\}^n,\ i\in\{0,\ldots,\widetilde D_f(f(x))\}\}$ and $\overline T=\{\langle x,i\rangle\mid x\in\{0,1\}^n,\ i\in\{\widetilde D_f(f(x))+1,\ldots,n-1\}\}$.

<a id="pdf-130039751e9f-p031-b007"></a>
<!-- pdf-source: page=31; block=7; confidence=0.98 -->
**Lemma 6.1.1.** Let $W=(\widetilde X,I)\in_U T$, $R\in_U\{0,1\}^{p(n)}$, $Y\in_U\{0,1\}^n$, and $\beta\in_U\{0,1\}$. Let $f$ be a one-way function. Then $\langle f'(W;R),\widetilde X\odot Y,Y\rangle$ and $\langle f'(W;R),\beta,Y\rangle$ are computationally indistinguishable. The reduction is poly-preserving.

<a id="pdf-130039751e9f-p031-b008"></a>
<!-- pdf-source: page=31; block=8; confidence=0.78 -->
**Proof.** Suppose an adversary distinguishes the two displayed distributions. It then distinguishes the hidden bit $X\mathbin{\oplus}Y$ given $\langle f_0(W;R),Y\rangle$. Proposition 4.1.2 yields an oracle machine that inverts $f$; the argument continues on page 32.

<a id="pdf-130039751e9f-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.91 -->
By Proposition 4.1.2, there is an oracle TM $M'$ such that $M'^{(A)}$ is an $\mathbf R''$-breaking adversary for inverting $f'(W;R)$, where $\mathbf R''(n)=n^{O(1)}\cdot\mathbf R'(n)^{O(1)}$. Finally, we use the same idea as in Lemma 5.1.2: the success probability of $M'^{(A)}$ on input $\langle f(x),\alpha,i,r\rangle$, for $\alpha\in_U\{0,1\}^{i+\lceil\log(2n)\rceil}$, is at least inverse polynomial in the success probability of $M'^{(A)}$ on input $f'(x,i,r)$ for each fixed $\langle x,i\rangle\in T$. Consider the oracle TM $N$: $N^{(A)}$ on input $f(X)$ chooses $i\in_U\{0,\ldots,n-1\}$, $\alpha\in_U\{0,1\}^{i+\lceil\log(2n)\rceil}$, and $r\in_U\{0,1\}^{p_n}$ and runs $M'^{(A)}$ on input $\langle f(X),\alpha,i,r\rangle$. Since $\Pr[\langle X,i\rangle\in T]\geq1/n$ when $i$ is uniform in $\{0,\ldots,n-1\}$, it follows that $N^{(A)}(f(X))$ produces an inverse with probability at least $1/n$ times the probability that $M'^{(A)}(f'(W;R))$ produces an inverse.

<a id="pdf-130039751e9f-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.91 -->
For $i\ge\widetilde D_f(f(X))$, the hidden string is almost determined by the revealed value. The boundary case $i=\widetilde D_f(f(X))$ is computationally hidden by Lemma 6.1.1 while nearly determined information-theoretically, providing a source of false entropy.

<a id="pdf-130039751e9f-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=1.00 -->
### 6.2 Construction and Main Theorem

<a id="pdf-130039751e9f-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.98 -->
In particular, let $X'\in_U\{0,1\}^{k_n\times n}$, $I'\in_U\{0,1\}^{k_n\times\lceil\log(n)\rceil}$, and $R'\in_U\{0,1\}^{k_n\times p_n}$. Part of the construction is then $f'^{k_n}(X',I',R')$.

<a id="pdf-130039751e9f-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.99 -->
Let $I\in_U\{0,\ldots,n-1\}$, let $p_n=\Pr[I\leq\widetilde D_f(f(X))]$, and let $m_n=k_np_n-2k_n^{2/3}$.

<a id="pdf-130039751e9f-p032-b006"></a>
<!-- pdf-source: page=32; block=6; confidence=0.93 -->
The construction assumes the exact $p_n$ initially; later an additive approximation is shown sufficient. The choice of $k$ makes it likely that at least $m_n$ sampled indices satisfy the threshold condition.

<a id="pdf-130039751e9f-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.99 -->
The intuition is that these $m_n$ hashed bits will look random to a time-limited adversary, even though there are really at most $(p_n-1/n)k_n$ bits of randomness left in these $k_n$ bits after seeing $Y'$ and $f'^{k_n}(X',I',R')$, and thus there are approximately $m_n-(p_n-1/n)k_n\approx n^2$ bits of false entropy.

<a id="pdf-130039751e9f-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.98 -->
Let $h':\{0,1\}^{p'_n}\times\{0,1\}^{k_n}\to\{0,1\}^{m_n}$ be a universal hash function, let $U\in_U\{0,1\}^{p'_n}$, and define
\[
g(p_n;X',Y',I',R',U)=\langle h'_U(\langle X'_1\odot Y'_1,\ldots,X'_{k_n}\odot Y'_{k_n}\rangle),f'^{k_n}(X',I',R'),U,Y'\rangle.
\]

<a id="pdf-130039751e9f-p033-b003"></a>
<!-- pdf-source: page=33; block=3; confidence=0.99 -->
**Theorem 6.2.1.** Let $f$ be a one-way function and $g$ be as described above in Equations (1) through (8). Then $g$ is a mildly non-uniform false entropy generator with false entropy $10n^2$. The reduction is weak-preserving.

<a id="pdf-130039751e9f-p033-b004"></a>
<!-- pdf-source: page=33; block=4; confidence=0.84 -->
**Proof.** Let $D$ be the output distribution of $g$, and let $E$ be the same tuple with its $m_n$ hashed output bits replaced by an independent uniform string $Z$. Lemma 6.3.1 gives $H_2(E)\ge H_2(D)+10n^2$. Lemma 6.3.2 and Lemma 6.1.1 imply that $D$ and $E$ are computationally indistinguishable with a weak-preserving reduction. These establish the theorem, subject to the stated lemmas.

<a id="pdf-130039751e9f-p033-b005"></a>
<!-- pdf-source: page=33; block=5; confidence=1.00 -->
**Theorem 6.2.2.** One-way functions exist if and only if pseudorandom generators exist.

<a id="pdf-130039751e9f-p033-b006"></a>
<!-- pdf-source: page=33; block=6; confidence=0.98 -->
**Proof.** Pseudorandom generators imply one-way functions by [Levin : 87]. Conversely, Theorem 6.2.1 and the results summarized in Subsection 4.9 imply that one-way functions yield pseudorandom generators.

<a id="pdf-130039751e9f-p033-b007"></a>
<!-- pdf-source: page=33; block=7; confidence=1.00 -->
### 6.3 The Main Lemmas

<a id="pdf-130039751e9f-p033-b008"></a>
<!-- pdf-source: page=33; block=8; confidence=0.99 -->
**Lemma 6.3.1.** $H(\mathcal E)\geq H(\mathcal D)+10n^2$.

<a id="pdf-130039751e9f-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=0.98 -->
The entropy of $\mathcal D$ and $\mathcal E$ excluding the first $m_n$ bits is exactly the same. The additional entropy in the first $m_n$ bits of $\mathcal E$ is equal to $m_n$. An upper bound on the additional entropy in the first $m_n$ bits of $\mathcal D$ is the additional entropy in $\langle X'_1\odot Y'_1,\ldots,X'_{k_n}\odot Y'_{k_n}\rangle$. For each $j\in\{1,\ldots,k_n\}$ where $I'_j<\widetilde D_f(f(X'_j))$, the amount of entropy added by $X'_j\odot Y'_j$ is at most 1. On the other hand, under the condition that $I'_j\geq\widetilde D_f(f(X'_j))$, $X'_j\odot Y'_j$ is determined by $\langle f'(X'_j;I'_j;R'_j),Y'_j\rangle$ with probability at least $1-1/(2n)$, and thus the additional entropy under this condition is at most $1/(2n)$. Since $I'_j<\widetilde D_f(f(X'_j))$ with probability $p_n-1/n$, the additional entropy added by $X'_j\odot Y'_j$ is at most $p_n-1/(2n)$. Therefore, the additional entropy in the first $m_n$ bits of $\mathcal D$ is at most $k_n(p_n-1/(2n))=m_n+2k_n^{2/3}-k_n/(2n)<m_n-10n^2$ by choice of $k_n$.

<a id="pdf-130039751e9f-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=0.98 -->
**Lemma 6.3.2.** Let $A$ be an adversary with distinguishing probability $\delta_n=\Pr[A(\mathcal D)=1]-\Pr[A(\mathcal E)=1]$ for $\mathcal D$ and $\mathcal E$. Assume without loss of generality that $\Pr[A(\mathcal D)=1]>\Pr[A(\mathcal E)=1]$. Let $W=(\widetilde X,I)\in_U T$, $R\in_U\{0,1\}^{p(n)}$, $Y\in_U\{0,1\}^n$, and $\beta\in_U\{0,1\}$. There is an oracle TM $M^{(A)}$ such that $M^{(A)}$ distinguishes between $\langle f'(W;R),\widetilde X\odot Y,Y\rangle$ and $\langle f'(W;R),\beta,Y\rangle$ with probability at least $\delta_n/(16k_n)$. The running time of $M^{(A)}$ is polynomial in the running time of $A$.

<a id="pdf-130039751e9f-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.90 -->
The lemma is technically involved; the text states its consequence before motivating the reduction.

<a id="pdf-130039751e9f-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=0.95 -->
**Corollary 6.3.3.** If $f$ is one-way, then $D$ and $E$ are computationally indistinguishable, via a weak-preserving reduction.

<a id="pdf-130039751e9f-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.99 -->
**Proof.** Combine Lemmas 6.1.1 and 6.3.2.

<a id="pdf-130039751e9f-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=0.98 -->
The proof uses a nonstandard hybrid; a simpler but inefficient hybrid is introduced for intuition.

<a id="pdf-130039751e9f-p034-b007"></a>
<!-- pdf-source: page=34; block=7; confidence=0.65 -->
For each $j\in\{1,\ldots,k_n\}$, sample $C_j=1$ with probability $1/\sqrt n$ and otherwise $0$. Choose the corresponding input pair from one of the sets $T$ or $\widetilde T$ according to $C_j$; then use the construction of $D$ with these pairs. If $C_j=1$, replace the $j$th input bit of $h_U$ from $X'_j\oplus Y'_j$ by an independent uniform bit to obtain $D'$.

<a id="pdf-130039751e9f-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.94 -->
For all $j\in\{0,\ldots,k_n\}$, let $\mathcal F^{(j)}$ be the hybrid distribution between $\mathcal D$ and $\mathcal E$ which is the same as $\mathcal D'$ up to position $j$ and the same as $\mathcal D$ thereafter, i.e., it is the same as $\mathcal D$ except that for all $i\leq j$, if $C_i=1$ then change the $i$th input bit of $h'_U$ from $X'_i\odot Y'_i$ to $B_i\in_U\{0,1\}$. Then $\mathcal F^{(0)}=\mathcal D$ and $\mathcal F^{(k_n)}\approx\mathcal E$. Let $J\in_U\{1,\ldots,k_n\}$. Then $\mathbb E_J[A(\mathcal F^{(J-1)})-A(\mathcal F^{(J)})]=\delta_n/k_n$.

<a id="pdf-130039751e9f-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.82 -->
The efficient $M^{(A)}$ has two phases. Phase one builds $k_n$ coupled, polynomially samplable pairs $(D^{(j)},E^{(j)})$, initialized at $(D,E)$, by sampling from prior-stage distributions and using $A$; the endpoint pair is described as approximately equal.

<a id="pdf-130039751e9f-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.97 -->
The first $j-1$ positions in both $\mathcal D^{(j)}$ and $\mathcal E^{(j)}$ are already fixed in essentially the same way in $\mathcal D^{(j-1)}$ and $\mathcal E^{(j-1)}$, and these positions will be fixed the same way in $\mathcal D^{(j)}$ and $\mathcal E^{(j)}$. To fill in position $j$, many samples of $(x_j,i_j)$ are drawn uniformly from $\{0,1\}^n\times\{0,\ldots,n-1\}$, and then with high probability many of them will be in $T$ and many will be in $\overline T$. We cannot directly tell for each sample whether it is in $T$ or $\overline T$. Thus, we use another criteria to decide which samples to keep to fill in position $j$: use the sample for which the distinguishing probability of $A$ between $\mathcal D^{(j)}$ and $\mathcal E^{(j)}$ is highest when the $j$th position is fixed according to the sample. Let $\delta^{(j)}=\Pr[A(\mathcal D^{(j)})=1]-\Pr[A(\mathcal E^{(j)})=1]$. Because $\delta^{(0)}=\delta_n$ and $\delta^{(k_n)}\approx0$, $\mathbb E_{j\in_U\{1,\ldots,k_n\}}[\delta^{(j-1)}-\delta^{(j)}]\geq\delta_n/k_n$.

<a id="pdf-130039751e9f-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.69 -->
At stage $j$, choose a single control bit $c_j$ with probability $1/\sqrt n$ of being $1$. The $j$th input to $f$ is sampled, as are $y'_j,u$, and in $D^{(j)}$ the corresponding $h_U$ bit is uniform if $c_j=1$, otherwise it is the correct inner-product bit. $E^{(j)}$ uses the same $f$ input, correlating the pair. Repeat candidate choices with this same $c_j$, estimate $A$'s acceptance gap, and retain the choice maximizing it. Phase two picks a stage, modifies a sampled $D^{(j)}$ portion according to its challenge, runs $A$ on it and a corresponding $E^{(j)}$ sample, and outputs a bit; its expected distinguishing gap is at least $\delta/k_n$.

<a id="pdf-130039751e9f-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.99 -->
The source now begins the formal proof of Lemma 6.3.2.

<a id="pdf-130039751e9f-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=0.99 -->
**Phase 1:** Define $\mathcal D^{(0)}=\mathcal D$ and $\mathcal E^{(0)}=\mathcal E$. Let $B\in_U\{0,1\}^{k_n}$. Let $\rho=\delta_n/(16k_n)$ and $\tau=64n^2/\rho$.

<a id="pdf-130039751e9f-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.97 -->
$\tau=64n^2/\rho$. Stage $j=1,\ldots,k_n$ works as follows: randomly choose $c_j\in\{0,1\}$ so that $c_j=1$ with probability $p_n$. Choose $\hat x_1,\ldots,\hat x_\tau\in_U\{0,1\}^n$ and $\hat i_1,\ldots,\hat i_\tau\in_U\{0,\ldots,n-1\}$. For each $m\in\{1,\ldots,\tau\}$, define $w_m=\langle\hat x_m,\hat i_m\rangle$ and let $\mathcal D_{c_j}^{(j-1)}(w_m)$ be the same as $\mathcal D^{(j-1)}$ except that $(X'_j,I'_j)$ is fixed to $w_m$ and the $j$th input bit of $h'_U$ is set to $\hat x_m\odot Y'_j$ if $c_j=0$ and to $B_j$ if $c_j=1$. Similarly, define $\mathcal E^{(j-1)}(w_m)$ to be the same as $\mathcal E^{(j-1)}$ except that $(X'_j,I'_j)$ is fixed to $w_m$. Let $\delta_{c_j}^{(j-1)}(w_m)=\Pr[A(\mathcal D_{c_j}^{(j-1)}(w_m))=1]-\Pr[A(\mathcal E^{(j-1)}(w_m))=1]$. Estimate this difference by sampling from the distributions, choose an index maximizing the estimate, fix the corresponding pair, and continue.

<a id="pdf-130039751e9f-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.98 -->
**Phase 2:** Pick $j\in_U\{0,\ldots,k_n-1\}$. Let $\mathcal D^{(j)}(w,r,b,y)$ be the distribution $\mathcal D^{(j)}$ except that $f'(X'_{j+1},I'_{j+1},R'_{j+1})$ is set to $f'(w,r)$ and the $j+1$st input bit of $h'_U$ is set to $b$, and $Y'_{j+1}$ is set to $y$. Let $\mathcal E^{(j)}(w,r,y)$ be the same as $\mathcal E^{(j)}$ except that $f'(X'_{j+1},I'_{j+1},R'_{j+1})$ is set to $f'(w,r)$ and $Y'_{j+1}$ is set to $y$. Let $\beta\in_U\{0,1\}$, let $D$ be a sample of $\mathcal D^{(j)}(w,r,b,y)$ and let $E$ be a sample of $\mathcal E^{(j)}(w,r,y)$. If $A(D)=A(E)$ then output $\beta$ else output $A(D)$.

<a id="pdf-130039751e9f-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.75 -->
Let $d^{(j)}(w;r;b;y)=\mathbb E[A(D_U^{(j)}(w;r;b;y))]$ and $e^{(j)}(w;r;y)=\mathbb E[A(E_U^{(j)}(w;r;y))]$. The adversary's acceptance probability is $1/2+(d^{(j)}(w;r;b;y)-e^{(j)}(w;r;y))/2$. By the definitions, averaging over $R,Y$ gives $\mathbb E[d^{(j)}(w;R;x\oplus Y;Y)-e^{(j)}(w;R;Y)]=\delta_0^{(j)}(w)$ and $\mathbb E[d^{(j)}(w;R;\beta;Y)-e^{(j)}(w;R;Y)]=\delta_1^{(j)}(w)$.

<a id="pdf-130039751e9f-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.98 -->
Let $\epsilon^{(j)}=\mathbb E[\delta_0^{(j)}(W)-\delta_1^{(j)}(W)]$. Thus, the distinguishing probability of $M^{(A)}$ is $\mathbb E_j[\epsilon^{(j)}]/2$, where $j\in_U\{0,\ldots,k_n-1\}$. To prove the lemma, it is sufficient to show that $\mathbb E[\sum_{j=0}^{k_n-1}\epsilon^{(j)}]\geq2\rho k_n=\delta_n/8$.

<a id="pdf-130039751e9f-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.90 -->
Since $\Pr[c_j=1]=p_n$, applying Chernoff bounds, with probability at least $1-2^{-n}$, $\sum_{j=0}^{k_n-1}c_j\geq k_np_n-k_n^{2/3}=m_n+k_n^{2/3}$. The entropy of the input to $h'_U$ conditioned on the rest of the bits of $\mathcal D^{(k_n)}$ is at least $\sum_j c_j$. If this sum is at least $m_n+k_n^{2/3}$, applying Lemma 4.5.1 gives $L_1(\mathcal D^{(k_n)},\mathcal E^{(k_n)})\leq2^{-n}$. Thus $\mathbb E[\delta^{(k_n)}]\leq2^{-n}$.

<a id="pdf-130039751e9f-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.93 -->
Let $\overline W\in_U\overline T$, and recall that $W\in_U T$. Then, since the $j+1$st input of $h'_U$ is always $X'_{j+1}\odot Y'_{j+1}$ in $\mathcal D^{(j)}$,
\[
\delta^{(j)}=p_n\mathbb E[\delta_0^{(j)}(W)]+(1-p_n)\mathbb E[\delta_0^{(j)}(\overline W)]
=p_n\mathbb E[\delta_1^{(j)}(W)]+p_n\epsilon^{(j)}+(1-p_n)\mathbb E[\delta_0^{(j)}(\overline W)].
\]
It remains to show that $\mathbb E[\delta^{(j+1)}]\geq p_n\mathbb E[\delta_1^{(j)}(W)]+(1-p_n)\mathbb E[\delta_0^{(j)}(\overline W)]-4\rho$.

<a id="pdf-130039751e9f-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.93 -->
We now show that $\mathbb E[\delta^{(j+1)}]\geq p_n\mathbb E[\delta_1^{(j)}(W)]+(1-p_n)\mathbb E[\delta_0^{(j)}(\overline W)]-4\rho$. Let $c\in\{0,1\}$ and consider stage $j$ in phase 1. From our choice of $\tau$ and the fact that $1/n\leq p_n\leq1-1/n$, it follows that, with probability at least $1-2^{-n}$, at least $\tau/n$ of the $w_m$'s are in $T$, and at least $\tau/n$ are in $\overline T$. Chernoff bounds imply that the maximum sampled true gap is at least the larger corresponding expectation minus $\rho$, with probability at least $1-2^{-n}$. The estimates are within $\rho$ of the corresponding true gaps with probability at least $1-2^{-n}$. Therefore the selected pair has gap at least $\max\{\mathbb E[\delta_c^{(j)}(W)],\mathbb E[\delta_c^{(j)}(\overline W)]\}-3\rho$ with probability at least $1-3\cdot2^{-n}$. Averaging over the random choice of $c_{j+1}$ gives the stated lower bound with error $4\rho$.

<a id="pdf-130039751e9f-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.99 -->
Before we continue let us just check that a good approximation of $p_n$ is sufficient. Suppose $p_n\leq\widetilde p_n\leq p_n+\frac1n$ and we do the entire construction with $\widetilde p_n$ replacing $p_n$. Enlarge $T$ to density $\widetilde p_n$ by making it contain some elements $\langle x,i\rangle$ with $i=\widetilde D_f(f(x))+1$. Lemma 6.1.1 is easily seen to remain valid and Lemma 6.3.1 just becomes more true in that the entropy of $\mathcal D$ decreases. This implies that it is sufficient to try $O(n)$ different values of $p_n$.

<a id="pdf-130039751e9f-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.99 -->
## 7 A Direct Construction

<a id="pdf-130039751e9f-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.99 -->
The direct construction starts with a one-way function $f:\{0,1\}^n\to\{0,1\}^{\ell_n}$. Construct $f'$ as in equation (3), and let $p_n$ be the probability that $I\leq\widetilde D_f(f(X))$ as in the previous section. Let $\mathcal X=\langle X,I,R\rangle$ represent the input distribution to $f'$, and let $c_n$ be the length of $\mathcal X$ and $c'_n$ the length of $f'(\mathcal X)$. Let $e_n=H(f'(\mathcal X))$. Let $b(x,y)=x\odot y$. Set $k_n=2000n^6$.

<a id="pdf-130039751e9f-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.99 -->
Formally, let $m_n=k_n(c_n-e_n-p_n+1/(2n))-2n k_n^{2/3}$, $m'_n=k_np_n-2n k_n^{2/3}$, and $m''_n=k_ne_n-2n k_n^{2/3}$. Let $R_1,R_2,R_3$ be indices of hash functions so that $h_{R_1}$ maps $k_nc_n$ bits to $m_n$ bits, $h_{R_2}$ maps $k_n$ bits to $m'_n$ bits, and $h_{R_3}$ maps $k_nc'_n$ bits to $m''_n$ bits.

<a id="pdf-130039751e9f-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.99 -->
**Construction 7.0.4.**
\[
g(\mathcal X',Y',R_1,R_2,R_3)=\langle h_{R_1}(\mathcal X'),h_{R_2}(b^{k_n}(\mathcal X',Y')),h_{R_3}(f'^{k_n}(\mathcal X')),Y',R_1,R_2,R_3\rangle.
\]

<a id="pdf-130039751e9f-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.96 -->
**Theorem 7.0.5.** If \(f\) is a one-way function and \(g\) is defined by Construction 7.0.4, then \(g\) is a mildly non-uniform pseudorandom generator, and the reduction is weak-preserving.

<a id="pdf-130039751e9f-p041-b004"></a>
<!-- pdf-source: page=41; block=4; confidence=0.98 -->
As noted above, the conditional entropy of $\mathcal X$ given $f'(\mathcal X)$ and $b(\mathcal X,Y)$ is at least $c_n-e_n-p_n+1/(2n)$. Thus, from Corollary 4.5.3, $(h_{R_1}(\mathcal X'),R_1)$ is statistically indistinguishable from random bits given $(f'^{k_n}(\mathcal X'),b^{k_n}(\mathcal X',Y'),Y')$. Hence $g(\mathcal X',Y',R_1,R_2,R_3)$ is statistically indistinguishable from $\langle Z_1,h_{R_2}(b^{k_n}(\mathcal X',Y')),h_{R_3}(f'^{k_n}(\mathcal X')),Y',R_1,R_2,R_3\rangle$, where $Z_1\in_U\{0,1\}^{m_n}$. Now, from Lemmas 6.3.2 and 6.1.1, it follows that $h_{R_2}(b^{k_n}(\mathcal X',Y'))$ is computationally indistinguishable from random bits given $\langle f'^{k_n}(\mathcal X'),R_2,Y'\rangle$. Thus, $g(\mathcal X',Y',R_1,R_2,R_3)$ is computationally indistinguishable from $\langle Z_1,Z_2,h_{R_3}(f'^{k_n}(\mathcal X')),Y',R_1,R_2,R_3\rangle$, where $Z_2\in_U\{0,1\}^{m'_n}$. Finally, from Corollary 4.5.3, $(h_{R_3}(f'^{k_n}(\mathcal X')),R_3)$ is statistically indistinguishable from $(Z_3,R_3)$, where $Z_3\in_U\{0,1\}^{m''_n}$. Thus, the output of $g$ is computationally indistinguishable from a truly random output of the same length. With Toeplitz-matrix hash functions, $O(m)$ bits suffice to construct a hash function on $m$ bits, and the input length to $g$ is $O(nk_n)=O(n^7)$.

<a id="pdf-130039751e9f-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.99 -->
It is clear that an approximation of both $e_n$ and $p_n$ that is within $1/(8n)$ of their true values is sufficient. Since $0\leq e_n\leq n$ and $0\leq p_n<1$, there are at most $O(n^3)$ cases of pairs to consider. This means that we get a total of $O(n^3)$ generators, each needing an input of length $O(n^7)$. Thus the total input size to the pseudorandom generator is $O(n^{10})$, as claimed.

<a id="pdf-130039751e9f-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.99 -->
## 8 Conclusions

<a id="pdf-130039751e9f-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.87 -->
The paper situates cryptographic feasibility in complexity-theoretic assumptions such as \(P\ne NP\) and the existence of one-way functions. Since many secure protocols can be built from pseudorandom generators, the results here imply those protocols can instead be based on any one-way function. Prior results also relate pseudorandom generators to computationally indistinguishable yet statistically distinct samplable distributions, and derive one-way functions from several secure-protocol primitives, including nontrivial zero-knowledge proofs. Together these results make one-way functions central to complexity-based cryptography; exchanging secrets over a public channel is noted as a possible exception.

<a id="pdf-130039751e9f-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.98 -->
The general pseudorandom-generator construction from any one-way function has polynomial input-size blowup and is only weak-preserving; the text identifies poly-preserving or linear-preserving reductions as desirable for practical use.

<a id="pdf-130039751e9f-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=1.00 -->
## 9 Acknowledgements

<a id="pdf-130039751e9f-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.99 -->
The authors acknowledge colleagues’ contributions, advice, and comments on the work and its presentation.

<a id="pdf-130039751e9f-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=0.99 -->
Bibliography entries on randomness, cryptography, one-way functions, zero-knowledge, communication, and randomized algorithms, including works by McInnes, Motwani–Raghavan, Naor, Ostrovsky–Wigderson, Rényi, Rivest–Shamir–Adleman, Rompel, Santha–Vazirani, Shannon, Sipser, Vazirani, and Yao.
