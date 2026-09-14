<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 3eebfb23ab53af2c69ef3332811cbc6071b7afcebf95315df2460122cc6c3788 -->

<a id="pdf-3eebfb23ab53-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# 3 Randomized Protocols

Introduces randomized communication protocols via examples where randomness beats any deterministic protocol, then defines them formally. Lower bounds are deferred to Chapters 5 and 6.

<a id="pdf-3eebfb23ab53-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.92 -->
**Equality problem.** Alice holds $x\in\{0,1\}^n$, Bob holds $y\in\{0,1\}^n$; output whether $x=y$ (ref. 1.1). Deterministically at least $n+1$ bits are required.

**Public-coin protocol (Figure 3.1).** Alice and Bob sample a shared random function $h:\{0,1\}^n\to\{0,1\}^k$; Alice sends $h(x)$; Bob announces whether $h(x)=h(y)$. If $x=y$ then $h(x)=h(y)$; if $x\neq y$ then $\Pr[h(x)=h(y)]\le 2^{-k}$. Communication is a constant number of bits, but the number of shared random bits is $2^n k$.

<a id="pdf-3eebfb23ab53-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
**Private-coin protocol (Figure 3.2).** Alice and Bob agree on an error-correcting code $C:\{0,1\}^n\to\{0,1\}^m$. Alice picks $k$ random coordinates $i_1,\dots,i_k\in[m]$ and sends $(i_1,C(x)_{i_1}),\dots,(i_k,C(x)_{i_k})$; Bob announces whether this equals $(i_1,C(y)_{i_1}),\dots,(i_k,C(y)_{i_k})$. Communication is $k\log n$ bits and error probability is at most $2^{-\Omega(k)}$.

**Code (footnote 1).** $C$ maps $n$ bits to $m=O(n)$ bits such that $x\neq y$ implies $C(x)$ and $C(y)$ differ in $\Omega(m)$ coordinates; random functions are such codes with high probability and explicit constructions exist.

<a id="pdf-3eebfb23ab53-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
**Greater-than problem.** Alice and Bob hold $x,y\in[n]$; determine which is greater (ref. 1.3). Any deterministic protocol needs $\log n+1$ bits. A randomized protocol needs only $O(\log\log n)$ bits (described in Exercise 3.1).

**Protocol with $O(\log\log n\cdot\log\log\log n)$ bits (Figure 3.3).** Encode inputs as $\ell$-bit strings, $\ell=\log n$. To decide $x\ge y$, find the most significant bit where $x,y$ differ. Using the equality protocol and binary search: at each step use equality to test whether the top half of the current index set agrees; if equal, keep the remaining bits, otherwise restrict to that half. Formally, with $J=[n]$, while $|J|>1$ take $J_0$ the first $|J|/2$ elements, sample shared $h:\{0,1\}^{|J_0|}\to\{0,1\}^{2\log\log\ell}$, Alice sends $h(x_{J_0})$, Bob reports whether $h(x_{J_0})=h(y_{J_0})$; if equal set $J=J\setminus J_0$ else $J=J_0$; finally announce $x_J,y_J$. After $\log\ell$ steps the first bit of difference is found; set $k=\log\log\ell$.

<a id="pdf-3eebfb23ab53-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.86 -->
**k-Disjointness problem.** Alice and Bob hold sets $X,Y\subseteq[n]$ of size at most $k$; decide whether they intersect. The rank method gives a lower bound of about $\log\binom{n}{k}\approx k\log(n/k)$ bits. A randomized protocol (Håstad and Wigderson, 2007) uses only $O(k)$ bits, better when $k\ll n$; $\Omega(k)$ is shown later.

**Protocol (Figure 3.4).** Sample a shared random sequence of sets $R_1,R_2,\dots\subseteq[n]$. While $|X|>1$, $|Y|>1$, and at most $120k+20$ bits have been sent: Alice sends the smallest $i$ with $X\subseteq R_i$, Bob sends the smallest $j$ with $Y\subseteq R_j$, then Alice replaces $X$ with $X\cap R_j$ and Bob replaces $Y$ with $Y\cap R_i$. Terminate concluding disjoint if $X=\emptyset$ or $Y=\emptyset$, else intersecting. Two bits are exchanged to flag empty sets.

<a id="pdf-3eebfb23ab53-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
**Claim 3.1.** $\mathbb{E}[i]=2^{|X|}$ and $\mathbb{E}[j]=2^{|Y|}$.

**Proof (begins).** The probability that the first set in the sequence contains $X$ is $2^{-|X|}$. If it does not, one continues searching for the first containing set among the rest of the sequence.

<a id="pdf-3eebfb23ab53-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.88 -->
**Proof (continued).** Hence $\mathbb{E}[i]=2^{-|X|}\cdot 1+(1-2^{-|X|})(\mathbb{E}[i]+1)$, giving $\mathbb{E}[i]=2^{|X|}$; the bound on $\mathbb{E}[j]$ is identical. $\square$

Since a number of size $i$ is communicated with at most $2\log i$ bits, and using concavity of $\log$:
$$\mathbb{E}[2\log i]\le 2\log\mathbb{E}[i]=2|X|,\qquad \mathbb{E}[2\log j]\le 2\log\mathbb{E}[j]=2|Y|.\tag{3.1}$$

<a id="pdf-3eebfb23ab53-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.96 -->
**Claim 3.2.** If $X\cap Y=\emptyset$, the expected number of bits communicated by the protocol is at most $6|X|+6|Y|+2$.

**Proof.** By induction on $|X|+|Y|$, using that the sets only shrink. Base case: if $X$ or $Y$ is empty, at most $2\le 6(|X|+|Y|)+2$ bits. If both nonempty, (3.1) bounds the first step's expected communication by $2+2|X|+2|Y|$. By induction the rest costs $\mathbb{E}[6(|X\cap R_j|+|Y\cap R_i|)]+2$. Since $X,Y$ are disjoint, $\mathbb{E}[|X\cap R_j|]=|X|/2$ and $\mathbb{E}[|Y\cap R_i|]=|Y|/2$. Total:
$$2+2|X|+2|Y|+(6/2)|X|+(6/2)|Y|+2 = 6|X|+6|Y|+2-(|X|+|Y|-2)\le 6|X|+6|Y|+2.\ \square$$

<a id="pdf-3eebfb23ab53-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
By Claim 3.2, for disjoint $X,Y$ the expected number of steps is $6|X|+6|Y|+2$. By Markov's inequality, the probability of exceeding $10\cdot(6|X|+6|Y|+2)$ bits is at most $1/10$. Running the process until $120k+20$ bits are communicated bounds the error probability by $1/10$.

<a id="pdf-3eebfb23ab53-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.85 -->
## Variants of Randomized Protocols

**Definition (begins).** A randomized protocol is a deterministic protocol in which each party additionally has access to a random string beyond the inputs.

<a id="pdf-3eebfb23ab53-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
Randomness is sampled independently of inputs. **Public coins**: all parties share one random string; **private coins**: each party samples independently. Every private-coin protocol is simulable by a public-coin protocol (a partial converse is promised later). Two error measures: (i) **worst-case error e** — error probability at most e on every input; (ii) **average-case error e w.r.t. µ** — error probability at most e when inputs are drawn from µ. Error reduction: if worst-case error e < 1/2, repeat the protocol k times and output the majority; an error occurs only if ≥ k/2 runs err, so by the Chernoff bound the error probability is at most 2^{−Ω(k(1/2−e)^2)}.

<a id="pdf-3eebfb23ab53-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.97 -->
**Theorem 3.3.** The communication complexity of computing a function g in the worst case with error at most e equals the maximum, over all input distributions µ, of the communication complexity of computing g with error at most e with respect to µ.

<a id="pdf-3eebfb23ab53-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
**Theorem 3.4.** Let M be an m × n matrix. Then

min_{x≥0} max_{y≥0} xMy = max_{y≥0} min_{x≥0} xMy,

where x is a 1 × m row vector with ∑_i x_i = 1 and y is an n × 1 column vector with ∑_j y_j = 1. (Also derivable from LP duality.)

<a id="pdf-3eebfb23ab53-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.92 -->
**Proof (of Theorem 3.3).** Easy direction: a protocol with worst-case error e also has average-case error e under every input distribution. Conversely, assume that for every distribution µ there is a c-bit protocol computing g with average-case error e. Introduce the boolean matrix M whose rows index deterministic protocols and whose columns index inputs (definition continues on the next page).

<a id="pdf-3eebfb23ab53-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.94 -->
**Proof (continued).** Define M_{i,j} = 1 if deterministic protocol i computes g correctly on input j, else 0. An input distribution is a choice y ≥ 0 with ∑_j y_j = 1; a randomized protocol (a distribution over deterministic protocols) is a choice x ≥ 0 with ∑_i x_i = 1. The error probability of randomized protocol x under distribution y is exactly xMy. The hypothesis gives max_{y≥0} min_{x≥0} xMy ≤ e; Theorem 3.4 then gives min_{x≥0} max_{y≥0} xMy ≤ e, i.e. a single fixed randomized protocol has error at most e under every input distribution. ∎

<a id="pdf-3eebfb23ab53-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**Public Coins vs Private Coins.** Question of whether every public-coin protocol can be simulated by a private-coin protocol; answer (Newman) is yes, up to a small additive communication loss.

<a id="pdf-3eebfb23ab53-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.96 -->
**Theorem 3.5.** If g : {0,1}^n × {0,1}^n → {0,1} can be computed with c bits of communication and worst-case error e, then it can be computed by a private-coin protocol with c + log(n/e^2) + O(1) bits of communication and worst-case error 2e. (This additive log n term is tight, since private-coin equality requires Ω(log n) bits.)

<a id="pdf-3eebfb23ab53-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.93 -->
**Proof.** Probabilistic method. Pick t independent random strings, each usable as randomness for the public-coin protocol. For a fixed input, by the Chernoff bound the probability that a (1 − 2e) fraction of the t strings yields the wrong answer is at most 2^{−Ω(e^2 t)}. Choosing t = O(2n/e^2) makes this < 2^{−2n}; by a union bound over all inputs the probability that 2et strings err on some input is < 1, so a fixed set of strings works for every input. The private-coin protocol: Alice samples one of the t strings and sends its index, costing at most log(n/e^2) + O(1) bits, then both run the original public-coin protocol. ∎

<a id="pdf-3eebfb23ab53-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->
**Nearly Monochromatic Rectangles.** Nearly monochromatic rectangles serve for randomized protocols the role monochromatic rectangles serve for deterministic ones.

<a id="pdf-3eebfb23ab53-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.96 -->
**Definition 3.6.** Given a distribution µ on inputs, a rectangle R has bias (1 − e) under a function g if there is a constant b such that

Pr_µ[ g(x,y) = b | (x,y) ∈ R ] ≥ 1 − e.

Such a rectangle is called (1 − e)-monochromatic.

<a id="pdf-3eebfb23ab53-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.96 -->
**Theorem 3.7.** If a c-bit protocol computes g with error e under a distribution µ, then the inputs can be partitioned into 2^c rectangles such that the average bias of a random rectangle from the partition is at least 1 − e.

<a id="pdf-3eebfb23ab53-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.96 -->
**Theorem 3.8.** If a c-bit protocol computes g with error e under µ, then for every ℓ there exist disjoint (1 − ℓe)-monochromatic rectangles R_1, R_2, …, R_{2^c} such that Pr_µ[(x,y) ∈ ∪_i R_i] ≥ 1 − 1/ℓ. (Obtained by applying Markov's inequality to the average of Theorem 3.7; instrumental for randomized lower bounds.)

<a id="pdf-3eebfb23ab53-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.94 -->
**Proof.** Fix the randomness optimally, so the protocol may be assumed deterministic. By Theorem 1.7 it induces a partition of the space into 2^c rectangles. Consider the rectangles that are not (1 − ℓe)-monochromatic: if the probability that the input lands in one of them exceeded 1/ℓ, the protocol's error would exceed e. Hence the input lands in a (1 − ℓe)-monochromatic rectangle with probability at least 1 − 1/ℓ. ∎

<a id="pdf-3eebfb23ab53-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.96 -->
**Corollary 3.9.** If a c-bit protocol computes g with error e under µ, then for every ℓ there is a (1 − ℓe)-monochromatic rectangle of density at least 2^{−c}(1 − 1/ℓ).

<a id="pdf-3eebfb23ab53-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
# Randomized protocols

<a id="pdf-3eebfb23ab53-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.92 -->
**Exercise 3.1.** Develop a randomized protocol for greater-than using only $O(\log\log n)$ bits of communication. Given two strings $x,y\in\{0,1\}^{\ell}$, Alice and Bob want to find the smallest index $i$ with $x_i\neq y_i$.

<a id="pdf-3eebfb23ab53-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
**Exercise 3.2.** Design a randomized protocol finding the first difference between two $n$-bit strings $x\neq y$, i.e. the smallest $i$ with $x_i\neq y_i$, using $O(\log n)$ bits (improving the $O(\log n\,\log\log n)$ method from class).

Construction: a rooted tree where each vertex corresponds to an interval of coordinates in $[n]$. The root is $I=[n]$. Each internal vertex for interval $I$ has two children: the left child for the first half of $I$, the right child for the second half. This gives depth $\log n$, with leaves corresponding to size-1 intervals (single coordinates). To each leaf attach a path of length $3\log n$ whose vertices all represent that same size-1 interval, making the total depth $4\log n$.

<a id="pdf-3eebfb23ab53-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.90 -->
**Part 1.** Fill in the protocol and prove an upper bound on the expected number of communicated bits and a lower bound on the success probability. Protocol: using inputs and hashing, start at the root and navigate toward the smallest interval containing the target index $i$; each step moves to a parent or child. At a vertex for interval $I$, first exchange $O(1)$ hash bits to confirm the first difference lies in $I$; if not, move to the parent; otherwise exchange $O(1)$ hash bits to choose which child to move to. At size-1 interval nodes, use hashes to move to a parent or child.

<a id="pdf-3eebfb23ab53-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.92 -->
**Part 2.** Argue that whenever the number of nodes at which the protocol made the correct choice exceeds the number of nodes with a wrong choice by $\log n$, the protocol correctly computes $i$.

<a id="pdf-3eebfb23ab53-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.92 -->
**Part 3.** Use the Chernoff bound to show that the number of hashes giving the right answer is large enough to guarantee the protocol succeeds with high probability on any input.

<a id="pdf-3eebfb23ab53-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
**Exercise 3.3.** Show that when the inputs to greater-than are sampled uniformly and independently, there is a protocol communicating only $O(\log(1/\varepsilon))$ bits with error at most $\varepsilon$ under this distribution.
