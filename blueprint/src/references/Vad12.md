<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c -->

<a id="pdf-bf2ce5422088-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Pseudorandomness

Survey by Salil P. Vadhan, *Foundations and Trends in Theoretical Computer Science*, Vol. 7, Nos. 1–3 (2011), pp. 1–336.

<a id="pdf-bf2ce5422088-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
Contents listing: Introduction; The Power of Randomness; Basic Derandomization Techniques, with section topics including polynomial identity testing, sampling, random walks, enumeration, conditional expectations, and pairwise independence.

<a id="pdf-bf2ce5422088-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.99 -->
Contents listing: Expander Graphs; List-Decodable Codes; Randomness Extractors; Pseudorandom Generators. Topics include expansion, deterministic logspace connectivity, samplers, extractor constructions, cryptographic generators, hybrid arguments, and hardness-based constructions.

<a id="pdf-bf2ce5422088-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
Contents listing: Pseudorandom Generator exercises and references; Conclusions on a unified theory and other pseudorandomness topics; acknowledgments and references.

<a id="pdf-bf2ce5422088-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=1.00 -->
## Pseudorandomness

<a id="pdf-bf2ce5422088-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
Survey of efficiently generating objects that appear random using little or no randomness, emphasizing connections among expander graphs, extractors, list-decodable codes, samplers, and pseudorandom generators.

<a id="pdf-bf2ce5422088-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=1.00 -->
# Introduction

<a id="pdf-bf2ce5422088-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=1.00 -->
## 1.1 Overview of this Survey

<a id="pdf-bf2ce5422088-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
Randomization enables efficient algorithms for primality testing, approximate counting (including bipartite perfect-matching counts), and undirected $s$-$t$ connectivity; deterministic counterparts were discovered later or remain slower.

<a id="pdf-bf2ce5422088-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.98 -->
Randomized parallel algorithms for perfect matching are polylogarithmic-time, while known deterministic algorithms take polynomial time. Randomization also supports cryptographic key selection and encryption security, and probabilistic existence proofs such as Ramsey graphs.

<a id="pdf-bf2ce5422088-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=1.00 -->
**Main Question.** Can randomness use in these settings be reduced or eliminated?

<a id="pdf-bf2ce5422088-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.97 -->
The text begins listing motivations for reducing randomness, starting with understanding and comparing computational resources; the discussion continues beyond the supplied page.

<a id="pdf-bf2ce5422088-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=1.00 -->
## Introduction

<a id="pdf-bf2ce5422088-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.99 -->
The survey considers the cost of derandomization, use of biased and correlated physical randomness, efficient explicit constructions, and broader applications of pseudorandomness.

<a id="pdf-bf2ce5422088-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=1.00 -->
The proposed approach to derandomization is to efficiently generate objects that appear random using little or no randomness.

<a id="pdf-bf2ce5422088-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=1.00 -->
## 1.1 Overview of this Survey

<a id="pdf-bf2ce5422088-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.99 -->
**Pseudorandom Generators:** A pseudorandom generator is an algorithm that takes as input a short, perfectly random seed and then returns a (much longer) sequence of bits that “looks random.” Specifically, we require that no efficient algorithm can distinguish the output from a truly random sequence. An ideal theorem would be something like: “If $P\ne NP$, then pseudorandom generators exist.”

<a id="pdf-bf2ce5422088-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.99 -->
**Definition (Randomness extractor).** An extractor takes a source of biased, correlated bits and outputs an almost-uniform bit sequence. Deterministic extraction is impossible for general such sources; the survey considers seeded extractors using a small, logarithmic number of truly random bits.

<a id="pdf-bf2ce5422088-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.96 -->
**Definition (Expander graphs).** Expanders are sparse graphs that are well-connected; an example criterion is that every bisection cuts a constant fraction of edges.

<a id="pdf-bf2ce5422088-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
A random degree-3 graph is a good expander with high probability, while explicit constructions are needed for applications and may not attain the probabilistic method’s degree-expansion tradeoff.

<a id="pdf-bf2ce5422088-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.99 -->
**Definition (Error-correcting code).** An error-correcting code encodes messages as longer redundant codewords so that the original message can be recovered after some corruption.

<a id="pdf-bf2ce5422088-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.99 -->
Shannon’s probabilistic method shows that a random map from $n$-bit messages to $O(n)$-bit codewords is a good code with high probability, but its exponential description and lack of known efficient decoding motivate explicit constructions.

<a id="pdf-bf2ce5422088-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.99 -->
The survey focuses on corruption levels where unique decoding is impossible and decoding instead returns a short list guaranteed to include the transmitted message.

<a id="pdf-bf2ce5422088-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.99 -->
## A Unified Theory

<a id="pdf-bf2ce5422088-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
The survey connects pseudorandom generators, extractors, expander graphs, and error-correcting codes, using ideas across complexity, information theory, combinatorics, and algebra.

<a id="pdf-bf2ce5422088-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=1.00 -->
## 1.2 Background Required and Teaching Tips

<a id="pdf-bf2ce5422088-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.99 -->
The intended background is undergraduate computation theory and discrete mathematics, basic complexity (including P, NP, and reductions), and preferably elementary algebra with finite fields. Exercises develop key facts, introduce later concepts, and illustrate applications; especially challenging problems are starred.

<a id="pdf-bf2ce5422088-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=1.00 -->
## 1.3 Notational Conventions

<a id="pdf-bf2ce5422088-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.99 -->
We denote the set of numbers $\{1,\ldots,n\}$ by $[n]$. We write $\mathbb N$ for the set of nonnegative integers (so we consider $0$ to be a natural number). We write $S\subset T$ to mean that $S$ is a subset of $T$ (not necessarily strict), and $S\subsetneq T$ for $S$ being a strict subset of $T$. An inequality we use often is $\binom{n}{k}\le (ne/k)^k$. All logarithms are base 2 unless otherwise specified. We often use the convention that lowercase letters are the logarithm (base 2) of the corresponding capital letter (e.g., $N=2^n$).

<a id="pdf-bf2ce5422088-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
Random variables are denoted by uppercase letters and values by lowercase letters. $x\mathrel{\overset{R}{\leftarrow}}X$ denotes sampling from $X$, and $x\mathrel{\overset{R}{\leftarrow}}S$ denotes uniform sampling from $S$. Repeated occurrences of a random variable use the same sample. Define $\operatorname{Supp}(X)=\{x:\Pr[X=x]>0\}$; $X\mid E$ denotes conditioning on event $E$, and $U_S$ is uniform on set $S$. For $n\in\mathbb N$, $U_n$ is uniform on $\{0,1\}^n$.

<a id="pdf-bf2ce5422088-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=1.00 -->
## 1.4 Chapter Notes and References

<a id="pdf-bf2ce5422088-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.99 -->
This section points to general surveys, textbooks, and sources for results discussed in the survey.

<a id="pdf-bf2ce5422088-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.99 -->
The modern notion of a pseudorandom generator was formulated in the works of Blum and Micali [72] and Yao [421], motivated by cryptographic applications. We will spend most of our time on a variant of the Blum–Micali–Yao notion, proposed by Nisan and Wigderson [302], where the generator is allowed more running time than the algorithms it fools. A detailed treatment of the Blum–Micali–Yao notion can be found in [157]. Surveys on randomness extractors are [301, 352, 354]. The notion of extractor that we will focus on is the one due to Nisan and Zuckerman [303].

<a id="pdf-bf2ce5422088-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=1.00 -->
# The Power of Randomness

<a id="pdf-bf2ce5422088-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
The chapter introduces randomized algorithms and tools for studying their derandomization.

<a id="pdf-bf2ce5422088-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=1.00 -->
## 2.1 Polynomial Identity Testing

<a id="pdf-bf2ce5422088-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.99 -->
**Computational Problem 2.1. Polynomial Identity Testing:** Given two multivariate polynomials, $f(x_1,\ldots,x_n)$ and $h(x_1,\ldots,x_n)$, decide whether $f=g$.

<a id="pdf-bf2ce5422088-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
A (multivariate) polynomial is a finite expression of the form $f(x_1,\ldots,x_n)=\sum_{i_1,\ldots,i_n\in\mathbb N}c_{i_1,\ldots,i_n}x_1^{i_1}x_2^{i_2}\cdots x_n^{i_n}$. The coefficients are chosen from a field or, more generally, an integral domain. The degree (a.k.a. total degree) is the maximum sum of the exponents $i_1+\cdots+i_n$ over its monomials with nonzero coefficients. Its degree in $x_j$ is the maximum of $i_j$ over its monomials with nonzero coefficients.

<a id="pdf-bf2ce5422088-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.97 -->
Examples of coefficient fields include $\mathbb Q$, $\mathbb R$, and $\mathbb Z_p$ for prime $p$; $\mathbb Z$ is an integral domain but not a field, while $\mathbb Z_n$ for composite $n$ is not an integral domain. For every prime power $q=p^k$ there is a unique finite field of size $q$ up to isomorphism; it equals $\mathbb Z_q$ only when $k=1$.

<a id="pdf-bf2ce5422088-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.98 -->
Equality may mean equality as functions or equality as formal polynomials (coefficientwise). These notions agree over the integers but can differ over finite fields.

<a id="pdf-bf2ce5422088-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.97 -->
For a finite field $F$, the polynomial $f(x)=\prod_{\alpha\in F}(x-\alpha)$ vanishes at every $\alpha\in F$ but is not the zero formal polynomial. The text henceforth uses formal-polynomial equality unless specified otherwise; when the domain is larger than the degrees, the two notions agree by the Schwartz–Zippel lemma.

<a id="pdf-bf2ce5422088-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->
Three input models are distinguished: (1) coefficient lists, where identity testing reduces to comparison in linear time in input length; (2) an evaluation oracle, with explicit input including the field description, variable count $n$, and degree bound $d$, and efficiency measured polynomially in these input lengths and $n\log |F|$; (3) an arithmetic formula, a symbolic expression describing the polynomial. Expanding and collecting terms can produce a polynomial whose length is exponential in the formula length.

<a id="pdf-bf2ce5422088-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.99 -->
An arithmetic circuit is a directed acyclic graph with indegree-0 input nodes labeled by variables or constants and indegree-2 computation nodes labeled by addition or multiplication; one computation node is designated as output. It computes a polynomial. Formulas are circuits whose underlying graph is a tree.

<a id="pdf-bf2ce5422088-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
**Computational Problem 2.2.** Given a polynomial $f(x_1,\ldots,x_n)$, decide whether $f=0$. This is the special case of identity testing with $g=0$; the general problem reduces to it by testing $f-g=0$.

<a id="pdf-bf2ce5422088-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.99 -->
**Algorithm 2.3 (Polynomial Identity Testing).** Input: A multivariate polynomial $f(x_1,\ldots,x_n)$ of degree at most $d$ over a field/domain $\mathbb F$. (1) Let $S\subseteq\mathbb F$ be any set of size $2d$. (2) Choose $\alpha_1,\ldots,\alpha_n\xleftarrow{R} S$. (3) Evaluate $f(\alpha_1,\ldots,\alpha_n)$. If the result is $0$, accept. Otherwise, reject.

<a id="pdf-bf2ce5422088-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.99 -->
**Lemma 2.4 (Schwartz–Zippel).** For a nonzero polynomial $f$ of degree $d$ over a field or integral domain $F$, and a finite set $S\subseteq F$, independent uniform samples $\alpha_1,\ldots,\alpha_n\in S$ satisfy
$$\Pr[f(\alpha_1,\ldots,\alpha_n)=0]\leq \frac{d}{|S|}.$$

<a id="pdf-bf2ce5422088-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.99 -->
**Proof.** The univariate case follows because a degree-$d$ polynomial over a field has at most $d$ roots. The multivariate result follows by induction on $n$; details are assigned as an exercise (Problem 2.1).

<a id="pdf-bf2ce5422088-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.99 -->
The identity-testing algorithm always accepts when $f=0$; for nonzero $f$, the lemma bounds its error by $1/2$ when $|S|=2d$. Repetition or a larger sample set reduces this error. The randomness is over the algorithm's coin tosses for worst-case inputs; this differs from average-case analysis, which assumes randomly chosen inputs.

<a id="pdf-bf2ce5422088-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.99 -->
Efficiency requires a degree bound and the ability to evaluate $f$ at sampled field elements. For formulas, degree is bounded by formula length; for circuits, it can be exponential in size or depth. A set of size $2d$ must be available in the domain.

<a id="pdf-bf2ce5422088-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.97 -->
The domain must be explicitly represented so its elements can be manipulated and sampled from a subset of size at least $2d$; for an oracle, evaluation is available directly, while formulas and circuits can be evaluated gate by gate. Over infinite domains such as $\mathbb Z$, integer bit-length may grow exponentially (Problem 2.4 addresses this). Under the stated conditions, polynomial-time randomized identity testing applies to formulas over $\mathbb Z$ and, by Problem 2.4, circuits. The text reports no known subexponential deterministic algorithms even for $\Sigma\Pi\Sigma$ formulas and notes a 2005 deterministic polynomial-time result when the outer sum has constantly many terms.

<a id="pdf-bf2ce5422088-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.99 -->
## 2.1.1 Application to Perfect Matching

<a id="pdf-bf2ce5422088-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.99 -->
**Definition 2.5.** For a graph $G=(V,E)$, a matching is a subset $E'\subseteq E$ whose edges have pairwise disjoint endpoints. It is perfect if every vertex is incident to an edge in $E'$.

<a id="pdf-bf2ce5422088-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.99 -->
**Computational Problem 2.6.** Given a graph $G$, decide whether it has a perfect matching.

<a id="pdf-bf2ce5422088-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.95 -->
The text notes that perfect matching has deterministic polynomial-time algorithms and begins an example that continues beyond the supplied page.

<a id="pdf-bf2ce5422088-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.98 -->
**Algorithm 2.7.** For a bipartite graph with both sides indexed by $[n]$ and edge set \(E\subseteq[n]\times[n]\), form the matrix \(A(x)\) with \(A_{i,j}(x)=x_{i,j}\) when \((i,j)\in E\), and \(A_{i,j}(x)=0\) otherwise.

<a id="pdf-bf2ce5422088-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.99 -->
We construct an $n\times n$ matrix $A$ where $A_{i,j}(x)=x_{i,j}$ if $(i,j)\in E$ and $0$ otherwise, where $x_{i,j}$ is a formal variable. Consider the multivariate polynomial $\det(A(x))=\sum_{\sigma\in S_n}\operatorname{sign}(\sigma)\cdot\prod_i A_{i,\sigma(i)}$, where $S_n$ denotes the set of permutations on $[n]$. Note that the $\sigma$th term is nonzero if and only if the permutation $\sigma$ defines a perfect matching. That is, $(i,\sigma(i))\in E$ for all $1\le i\le n$. So $\det(A(x))=0$ iff $G$ has no perfect matching. Moreover, its degree is bounded by $n$, and given values $\alpha_{i,j}$ for the $x_{i,j}$s, we can evaluate $\det(A(\alpha))$ efficiently in parallel in polylogarithmic time using an appropriate algorithm for the determinant. To test for a perfect matching efficiently in parallel, just run the Polynomial Identity Testing algorithm with, say, $S=\{1,\ldots,2n\}\subset\mathbb Z$, to test whether $\det(A(x))=0$.

<a id="pdf-bf2ce5422088-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.95 -->
The method also gives a fast sequential algorithm via determinant and matrix multiplication, whose stated time is at most \(O(n^{2.38})\). More sophisticated variants extend to nonbipartite graphs; the second remark continues on page 20.

<a id="pdf-bf2ce5422088-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.96 -->
The nonbipartite matching variants are stated to achieve the same parallel or sequential time bounds. Polynomial identity testing has also yielded a randomized primality algorithm; the text notes that primality was derandomized in 2002 to obtain a deterministic polynomial-time algorithm.

<a id="pdf-bf2ce5422088-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=1.00 -->
## 2.2 The Computational Model and Complexity Classes

<a id="pdf-bf2ce5422088-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=1.00 -->
### 2.2.1 Models of Randomized Computation

<a id="pdf-bf2ce5422088-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.99 -->
Three ways to supply randomness are described: (1) request independent unbiased random bits at one step per bit; this is the adopted model. (2) Request a uniform element of \(\{1,\ldots,n\}\) given binary \(n\); it is polynomial-time equivalent to model 1. (3) Read an initially random infinite tape; for polynomial time it is equivalent to model 1, while for space bounds it appears stronger because the random tape uses no counted working storage. For space-bounded computation, model 1 corresponds to one-way access to an infinite random-bit tape.

<a id="pdf-bf2ce5422088-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=1.00 -->
“Random bits” and “random coins” both refer to an algorithm’s random choices.

<a id="pdf-bf2ce5422088-p021-b002"></a>
<!-- pdf-source: page=21; block=2; confidence=1.00 -->
### 2.2.2 Complexity Classes

<a id="pdf-bf2ce5422088-p021-b003"></a>
<!-- pdf-source: page=21; block=3; confidence=0.99 -->
The classes are defined for decision languages \(L\subseteq\{0,1\}^*\), with natural extensions to function and search problems. A deterministic algorithm runs in time \(t:\mathbb N\to\mathbb N\) if every input \(x\) takes at most \(t(|x|)\) steps; polynomial time means \(t(n)=O(n^c)\) for a constant \(c\).

<a id="pdf-bf2ce5422088-p021-b004"></a>
<!-- pdf-source: page=21; block=4; confidence=1.00 -->
**Definition 2.8.** \(P\) is the class of languages \(L\) admitting a deterministic polynomial-time algorithm \(A\) such that \(x\in L\Rightarrow A(x)\) accepts and \(x\notin L\Rightarrow A(x)\) rejects.

<a id="pdf-bf2ce5422088-p021-b005"></a>
<!-- pdf-source: page=21; block=5; confidence=1.00 -->
A randomized algorithm runs in time \(t:\mathbb N\to\mathbb N\) when it uses at most \(t(|x|)\) steps for every input and every random-bit sequence.

<a id="pdf-bf2ce5422088-p021-b006"></a>
<!-- pdf-source: page=21; block=6; confidence=1.00 -->
**Definition 2.9.** \(RP\) is the class of languages \(L\) with a probabilistic polynomial-time algorithm \(A\) satisfying \(x\in L\Rightarrow \Pr[A(x)\text{ accepts}]\ge 1/2\), and \(x\notin L\Rightarrow \Pr[A(x)\text{ accepts}]=0\). Probabilities are over the algorithm’s coin tosses.

<a id="pdf-bf2ce5422088-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.99 -->
RP algorithms have one-sided error: they may reject members but never accept nonmembers. Independent repetitions, accepting if any trial accepts, reduce the error to at most $2^{-p(n)}$ for polynomial $p$; replacing $1/2$ by any constant in $(0,1)$ or by $1/\operatorname{poly}(n)$ gives the same class.

<a id="pdf-bf2ce5422088-p022-b002"></a>
<!-- pdf-source: page=22; block=2; confidence=1.00 -->
**Open Problem 2.10.** Is $P=RP$?

<a id="pdf-bf2ce5422088-p022-b003"></a>
<!-- pdf-source: page=22; block=3; confidence=0.99 -->
**Definition 2.11.** $co\text{-}RP$ consists of languages $L$ whose complement is in RP. Equivalently, some probabilistic polynomial-time algorithm $A$ satisfies: if $x\in L$, then $\Pr[A(x)\text{ accepts}]=1$; if $x\notin L$, then $\Pr[A(x)\text{ accepts}]\le 1/2$. Thus errors can occur on nonmembers, unlike RP, whose errors can occur on members.

<a id="pdf-bf2ce5422088-p022-b004"></a>
<!-- pdf-source: page=22; block=4; confidence=0.99 -->
**Theorem 2.12.** Arithmetic Circuit Identity Testing over $\mathbb Z$ is in $co\text{-}RP$. Its language is $ACIT_{\mathbb Z}=\{C:C(x_1,\ldots,x_n)\text{ is an arithmetic circuit over }\mathbb Z\text{ and }C=0\}$.

<a id="pdf-bf2ce5422088-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=1.00 -->
**Definition 2.13.** $BPP$ is the class of languages $L$ for which a probabilistic polynomial-time algorithm $A$ has acceptance probability at least $2/3$ on members and at most $1/3$ on nonmembers.

<a id="pdf-bf2ce5422088-p023-b002"></a>
<!-- pdf-source: page=23; block=2; confidence=0.99 -->
Majority voting over repetitions reduces BPP error from $1/3$ (or even $1/2-1/\operatorname{poly}(n)$) to exponentially small. $PP$ instead accepts members with probability greater than $1/2$ and nonmembers with probability at most $1/2$; exponentially many repetitions may be needed for error reduction. $BPP$ is the usual class for probabilistic polynomial-time computation.

<a id="pdf-bf2ce5422088-p023-b003"></a>
<!-- pdf-source: page=23; block=3; confidence=1.00 -->
**Open Problem 2.14.** Is $BPP=P$?

<a id="pdf-bf2ce5422088-p023-b004"></a>
<!-- pdf-source: page=23; block=4; confidence=0.99 -->
For an input $x$, algorithm $A$ has expected running time at most $t(|x|)$ when the expected number of steps of $A(x)$, over its random coin tosses, is at most $t(|x|)$. Monte Carlo algorithms may return an incorrect answer; Las Vegas algorithms always return the correct answer and may have variable running time.

<a id="pdf-bf2ce5422088-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=1.00 -->
**Definition 2.15.** $ZPP$ is the class of languages decidable by a probabilistic algorithm that is always correct and has expected polynomial running time.

<a id="pdf-bf2ce5422088-p024-b002"></a>
<!-- pdf-source: page=24; block=2; confidence=1.00 -->
**Fact 2.16 (Problem 2.3).** $ZPP=RP\cap co\text{-}RP$.

<a id="pdf-bf2ce5422088-p024-b003"></a>
<!-- pdf-source: page=24; block=3; confidence=1.00 -->
**Open Problem 2.17.** Is any inclusion in $P\subseteq ZPP\subseteq RP\subseteq BPP$ proper?

<a id="pdf-bf2ce5422088-p024-b004"></a>
<!-- pdf-source: page=24; block=4; confidence=1.00 -->
**Definition 2.18.** $RNC$ is the class of languages $L$ for which a probabilistic parallel algorithm runs in polylogarithmic time on polynomially many processors and accepts members with probability at least $1/2$, while accepting nonmembers with probability $0$.

<a id="pdf-bf2ce5422088-p024-b005"></a>
<!-- pdf-source: page=24; block=5; confidence=1.00 -->
**Theorem 2.19.** Perfect Matching in bipartite graphs is in $RNC$: $PM=\{G:G\text{ is a bipartite graph with a perfect matching}\}$.

<a id="pdf-bf2ce5422088-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=1.00 -->
## 2.2.3 Tail Inequalities and Error Reduction

<a id="pdf-bf2ce5422088-p025-b002"></a>
<!-- pdf-source: page=25; block=2; confidence=1.00 -->
Independent repetitions with majority voting reduce error; quantitative tail bounds determine the required repetition count.

<a id="pdf-bf2ce5422088-p025-b003"></a>
<!-- pdf-source: page=25; block=3; confidence=1.00 -->
**Lemma 2.20 (Markov’s Inequality).** For a nonnegative real-valued random variable $X$ and any $\alpha>0$, $\Pr[X\ge\alpha]\le \mathbb{E}[X]/\alpha$.

<a id="pdf-bf2ce5422088-p025-b004"></a>
<!-- pdf-source: page=25; block=4; confidence=1.00 -->
Markov’s inequality gives only weak concentration; applying tail bounds to many independent copies yields Chernoff bounds.

<a id="pdf-bf2ce5422088-p025-b005"></a>
<!-- pdf-source: page=25; block=5; confidence=0.98 -->
**Theorem 2.21 (A Chernoff Bound).** Let $X_1,\ldots,X_t$ be independent random variables in $[0,1]$, set $X=(\sum_i X_i)/t$ and $\mu=\mathbb{E}[X]$. Then $\Pr[|X-\mu|\ge\varepsilon]\le 2\exp(-t\varepsilon^2/4)$.

<a id="pdf-bf2ce5422088-p025-b006"></a>
<!-- pdf-source: page=25; block=6; confidence=1.00 -->
The bound makes deviations exponentially unlikely in $t$; proof is assigned as Problem 2.7. It is used next for BPP error reduction.

<a id="pdf-bf2ce5422088-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=1.00 -->
## 2.3 Sampling and Approximation Problems

<a id="pdf-bf2ce5422088-p026-b002"></a>
<!-- pdf-source: page=26; block=2; confidence=1.00 -->
**Proposition 2.22.** The following are equivalent: (1) $L\in\mathrm{BPP}$; (2) for every polynomial $p$, $L$ has a probabilistic polynomial-time algorithm with two-sided error at most $2^{-p(n)}$; (3) for some polynomial $q$, $L$ has a probabilistic polynomial-time algorithm with two-sided error at most $1/2-1/q(n)$.

<a id="pdf-bf2ce5422088-p026-b003"></a>
<!-- pdf-source: page=26; block=3; confidence=1.00 -->
**Proof.** The implications $(2)\Rightarrow(1)\Rightarrow(3)$ are immediate. For $(3)\Rightarrow(2)$, take an algorithm $A$ with error at most $1/2-1/q(n)$. On input $x$ of length $n$, run $A$ independently $t=t(n)$ times and output the majority answer; choose $t$ polynomially later.

<a id="pdf-bf2ce5422088-p026-b004"></a>
<!-- pdf-source: page=26; block=4; confidence=0.99 -->
Let $X_i$ indicate that repetition $i$ outputs the correct answer and let $X=(\sum_i X_i)/t$. Majority voting succeeds when $X>1/2$. By the error bound and linearity, $\mathbb{E}[X]\ge 1/2+1/q$, with $q=q(n)$. Applying Theorem 2.21 at $\varepsilon=1/q$ gives $\Pr[X\le 1/2]\le 2e^{-t/(2q^2)}<2^{-p(n)}$ for $t(n)=2p(n)q(n)^2$ and sufficiently large $n$.

<a id="pdf-bf2ce5422088-p026-b005"></a>
<!-- pdf-source: page=26; block=5; confidence=1.00 -->
## 2.3.1 Sampling

<a id="pdf-bf2ce5422088-p026-b006"></a>
<!-- pdf-source: page=26; block=6; confidence=1.00 -->
Sampling estimates a population mean from a small random sample; the section formulates the computational problem.

<a id="pdf-bf2ce5422088-p027-b001"></a>
<!-- pdf-source: page=27; block=1; confidence=0.99 -->
**Computational Problem 2.23 (Sampling; $[+\varepsilon]$-Approx Oracle Average).** Given oracle access to $f:\{0,1\}^m\to[0,1]$, estimate $\mu(f)\stackrel{\mathrm{def}}{=}\mathbb{E}[f(U_m)]$, where $U_m$ is uniform on $\{0,1\}^m$, by outputting a value in $[\mu(f)-\varepsilon,\mu(f)+\varepsilon]$.

<a id="pdf-bf2ce5422088-p027-b002"></a>
<!-- pdf-source: page=27; block=2; confidence=0.99 -->
**Algorithm 2.24 ($[+\varepsilon]$-Approx Oracle Average).** Input: oracle access to a function $f:\{0,1\}^m\to[0,1]$ and a desired error probability $\delta\in(0,1)$. (1) Choose $x_1,\ldots,x_t\stackrel{R}{\leftarrow}\{0,1\}^m$, for an appropriate choice of $t=O(\log(1/\delta)/\varepsilon^2)$. (2) Query the oracle to obtain $f(x_1),\ldots,f(x_t)$. (3) Output $(\sum_i f(x_i))/t$.

<a id="pdf-bf2ce5422088-p027-b003"></a>
<!-- pdf-source: page=27; block=3; confidence=0.99 -->
Theorem 2.21 establishes correctness. For constant $\varepsilon,\delta$, sample count is independent of population size $2^m$; even when $\varepsilon=1/\mathrm{poly}(m)$ and $\delta=2^{-\mathrm{poly}(m)}$, runtime is polynomial in $m$. The text states a deterministic query lower bound next.

<a id="pdf-bf2ce5422088-p027-b004"></a>
<!-- pdf-source: page=27; block=4; confidence=0.99 -->
**Proposition 2.25.** Any deterministic algorithm solving $[+(1/4)]$-Approx Oracle Average must make at least $2^m/2$ queries to its oracle.

<a id="pdf-bf2ce5422088-p027-b005"></a>
<!-- pdf-source: page=27; block=5; confidence=0.99 -->
**Proof.** Suppose deterministic $A$ makes fewer than $2^{m/2}$ queries. Let $Q$ be the set of queries made when each query is answered by $0$; this specifies the adaptive query sequence because later queries may depend on earlier answers.

<a id="pdf-bf2ce5422088-p028-b001"></a>
<!-- pdf-source: page=28; block=1; confidence=1.00 -->
Section heading.

<a id="pdf-bf2ce5422088-p028-b002"></a>
<!-- pdf-source: page=28; block=2; confidence=0.99 -->
Now define two functions: $f_0(x)=0$ for all $x$, and $f_1(x)=\begin{cases}0&x\in\mathbb{Q},\\1&x\notin\mathbb{Q}.\end{cases}$ Then $A$ gives the same answer on both $f_0$ and $f_1$ (since all the oracle queries return $0$ in both cases), but $\mu(f_0)=0$ and $\mu(f_1)>1/2$, so the answer must have error greater than $1/4$ for at least one of the functions.

<a id="pdf-bf2ce5422088-p028-b003"></a>
<!-- pdf-source: page=28; block=3; confidence=1.00 -->
Section heading introducing promise problems and a circuit-input variant of approximate average.

<a id="pdf-bf2ce5422088-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=1.00 -->
To use the standard input model, represent functions concisely by Boolean circuits $C:\{0,1\}^m\to\{0,1\}$ with gates $\land,\lor,\neg$.

<a id="pdf-bf2ce5422088-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=1.00 -->
**Definition 2.26.** A promise problem $\Pi=(\Pi_Y,\Pi_N)$ consists of disjoint sets of strings designated yes and no instances. The task is to distinguish them under the promise that the input belongs to one of these sets.

<a id="pdf-bf2ce5422088-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=1.00 -->
**Definition 2.27.** $\mathrm{prBPP}$ comprises promise problems decidable by a probabilistic polynomial-time algorithm $A$ such that $x\in\Pi_Y$ implies $\Pr[A(x)\text{ accepts}]\ge 2/3$, and $x\in\Pi_N$ implies $\Pr[A(x)\text{ accepts}]\le 1/3$.

<a id="pdf-bf2ce5422088-p029-b004"></a>
<!-- pdf-source: page=29; block=4; confidence=0.99 -->
A language $L$ embeds as the promise problem $(L,L)$; consequently, derandomizing all prBPP algorithms implies the corresponding language-class derandomization.

<a id="pdf-bf2ce5422088-p029-b005"></a>
<!-- pdf-source: page=29; block=5; confidence=1.00 -->
**Proposition 2.28.** $\mathrm{prBPP}=\mathrm{prP}\implies \mathrm{BPP}=\mathrm{P}$.

<a id="pdf-bf2ce5422088-p029-b006"></a>
<!-- pdf-source: page=29; block=6; confidence=1.00 -->
Unless stated otherwise, results about language classes are understood to extend readily to their promise-class analogues; language-class notation is used for brevity.

<a id="pdf-bf2ce5422088-p030-b001"></a>
<!-- pdf-source: page=30; block=1; confidence=1.00 -->
The section defines a promise problem for approximating the average value of a Boolean circuit.

<a id="pdf-bf2ce5422088-p030-b002"></a>
<!-- pdf-source: page=30; block=2; confidence=0.96 -->
**Definition 2.29.** The $[+\varepsilon]$-Approx Circuit Average problem is $CA_\varepsilon=(CA^\varepsilon_Y,CA^\varepsilon_N)$, where $CA^\varepsilon_Y=\{(C,p):\mu(C)>p+\varepsilon\}$ and $CA^\varepsilon_N=\{(C,p):\mu(C)\le p\}$. Here $\varepsilon$ may be constant or depend on input length $n=|(C,p)|$.

<a id="pdf-bf2ce5422088-p030-b003"></a>
<!-- pdf-source: page=30; block=3; confidence=0.98 -->
**Theorem 2.30.** For every function $\varepsilon$ such that $1/\operatorname{poly}(n)\le\varepsilon(n)\le 1-1/2^{n^{o(1)}}$, $[+\varepsilon]$-Approx Circuit Average is prBPP-complete. That is, it is in prBPP and every promise problem in prBPP reduces to it.

<a id="pdf-bf2ce5422088-p030-b004"></a>
<!-- pdf-source: page=30; block=4; confidence=0.99 -->
**Proof Sketch.** Membership in prBPP follows from Algorithm 2.24 and the fact that Boolean circuits can be evaluated in polynomial time. For prBPP-hardness, consider any promise problem $\Pi\in\mathrm{prBPP}$. We have a probabilistic $t(n)$-time algorithm $A$ that decides $\Pi$ with 2-sided error at most $2^{-n}$ on inputs of length $n$, where $t(n)=\operatorname{poly}(n)$. As an upper bound, $A$ uses at most $t(n)$ random bits. Thus we can view $A$ as a deterministic algorithm on two inputs—its regular input $x\in\{0,1\}^n$ and its coin tosses $r\in\{0,1\}^{t(n)}$. We write $A(x;r)$ for $A$'s output on input $x$ and coin tosses $r$. For every $n$, there is a circuit $C(x;r)$ of size $\operatorname{poly}(t(n))=\operatorname{poly}(n)$ that simulates the computation of $A$ for any input $x\in\{0,1\}^n$, $r\in\{0,1\}^{t(n)}$, and moreover $C$ can be constructed in time $\operatorname{poly}(t(n))=\operatorname{poly}(n)$. Let $C_x(r)$ be the circuit $C$ with $x$ hardwired in. Then the map $x\mapsto(C_x,1/2^n)$ is a polynomial-time reduction from $\Pi$ to $[+\varepsilon]$-Approx Circuit Average. Indeed, if $x\in\Pi_N$, then $A$ accepts with probability at most $1/2^n$, so $\mu(C_x)\le1/2^n$. And if $x\in\Pi_Y$, then $\mu(C_x)\ge1-1/2^n>1/2^n+\varepsilon(n')$, where $n'=|(C_x,1/2^n)|=\operatorname{poly}(n)$ and we take $n$ sufficiently large.

<a id="pdf-bf2ce5422088-p031-b001"></a>
<!-- pdf-source: page=31; block=1; confidence=0.99 -->
**Corollary 2.31.** $[+\varepsilon]$-Approx Circuit Average is in prP if and only if prBPP $=$ prP.

<a id="pdf-bf2ce5422088-p031-b002"></a>
<!-- pdf-source: page=31; block=2; confidence=0.98 -->
The lower-bound argument for [+\varepsilon]-Approx Oracle Average does not directly apply to explicit circuit inputs: a query notion is unclear, and the constructed function may not have a small circuit even if the algorithm treats the circuit as an oracle.

<a id="pdf-bf2ce5422088-p031-b003"></a>
<!-- pdf-source: page=31; block=3; confidence=0.99 -->
Introduces approximate counting with relative error.

<a id="pdf-bf2ce5422088-p031-b004"></a>
<!-- pdf-source: page=31; block=4; confidence=0.96 -->
**Definition (Computational Problem 2.32).** [+\(\varepsilon\)]-Approx Circuit Average gives additive error \(\varepsilon 2^m\), which can be uninformative when the satisfying-assignment count is small. Relative approximation instead estimates \(#C\) within a factor \(1+\varepsilon\). The promise problem [×\((1+\varepsilon)\)]-Approx #CSAT has YES set \(Y=\{(C,N):\#C>(1+\varepsilon)N\}\) and NO set \(N_0=\{(C,N):\#C\le N\}\); \(\varepsilon\) may be constant or depend on input length \(n=|(C,N)|\).

<a id="pdf-bf2ce5422088-p032-b001"></a>
<!-- pdf-source: page=32; block=1; confidence=0.98 -->
The relative-approximation promise problem is NP-hard for general circuits (already when \(N=0\)); restricting to DNF formulas permits a randomized polynomial-time algorithm.

<a id="pdf-bf2ce5422088-p032-b002"></a>
<!-- pdf-source: page=32; block=2; confidence=0.99 -->
**Definition (Computational Problem 2.33).** [×\((1+\varepsilon)\)]-Approx #DNF is [×\((1+\varepsilon)\)]-Approx #CSAT restricted to DNF formulas, disjunctions of conjunctions of literals.

<a id="pdf-bf2ce5422088-p032-b003"></a>
<!-- pdf-source: page=32; block=3; confidence=0.99 -->
**Theorem 2.34.** For every \(\varepsilon(n)\ge 1/\mathrm{poly}(n)\), [×\((1+\varepsilon)\)]-Approx #DNF is in \(\mathrm{prBPP}\).

<a id="pdf-bf2ce5422088-p032-b004"></a>
<!-- pdf-source: page=32; block=4; confidence=0.98 -->
**Proof.** It suffices to estimate the satisfying-assignment count of an input DNF \(\varphi(x_1,\ldots,x_m)\) within a multiplicative \(1\pm\varepsilon\) factor. Uniformly sampling assignments and scaling the fraction satisfying \(\varphi\) by \(2^m\) can fail when satisfying assignments are rare. Instead, embed the satisfying assignments \(A\) into a sampleable set \(B\) using a subset \(A^*\subseteq B\) with \(|A^*|=|A|\), \(|A^*|\ge |B|/\mathrm{poly}(n)\), efficiently decidable membership, polynomial-time computable \(|B|\), and polynomial-time uniform sampling from \(B\).

<a id="pdf-bf2ce5422088-p032-b005"></a>
<!-- pdf-source: page=32; block=5; confidence=0.98 -->
Let \(\ell\) be the number of clauses. Set \(B=\{(i,\alpha)\in[\ell]\times\{0,1\}^m: \alpha\text{ satisfies clause }i\}\), and \(A^*=\{(i,\alpha)\in B: \alpha\text{ satisfies no clause preceding }i\}\).

<a id="pdf-bf2ce5422088-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=0.99 -->
(4) $|B|=\sum_{i=1}^{\ell}2^{m-m_i}$, where $m_i$ is the number of literals in clause $i$ (after removing contradictory clauses that contain both a variable and its negation).

<a id="pdf-bf2ce5422088-p033-b002"></a>
<!-- pdf-source: page=33; block=2; confidence=0.97 -->
**Proof step (Algorithm 2.35).** Draw \(t=O((\ell/\varepsilon)^2)\) independent uniform samples from \(B\); let \(\widehat\mu\) be the sample fraction in \(A^*\), and output \(\widehat\mu|B|\). By the Chernoff bound, with high probability \(\widehat\mu=|A^*|/|B|\pm\varepsilon/\ell\), where \(u=v\pm w\) means \(u\in[v-w,v+w]\). Therefore \(\widehat\mu|B|=|A^*|\pm\varepsilon|B|/\ell=|A|\pm\varepsilon|A|\).

<a id="pdf-bf2ce5422088-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=1.00 -->
## 2.3 Sampling and Approximation Problems

<a id="pdf-bf2ce5422088-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=1.00 -->
**Open Problem 2.36.** Find a deterministic polynomial-time algorithm that approximately counts the satisfying assignments of a DNF formula.

<a id="pdf-bf2ce5422088-p034-b003"></a>
<!-- pdf-source: page=34; block=3; confidence=0.94 -->
A later section gives a quasipolynomial-time derandomization, with running time described as $2^{\operatorname{polylog}(n)}$.

<a id="pdf-bf2ce5422088-p034-b004"></a>
<!-- pdf-source: page=34; block=4; confidence=1.00 -->
## 2.3.4 MaxCut

<a id="pdf-bf2ce5422088-p034-b005"></a>
<!-- pdf-source: page=34; block=5; confidence=0.99 -->
**Definition 2.37.** For a graph $G=(V,E)$ and $S,T\subseteq V$, define $\operatorname{cut}(S,T)=\{\{u,v\}\in E:u\in S,\ v\in T\}$ and $\operatorname{cut}(S)=\operatorname{cut}(S,V\setminus S)$.

<a id="pdf-bf2ce5422088-p034-b006"></a>
<!-- pdf-source: page=34; block=6; confidence=1.00 -->
**Computational Problem 2.38 (MaxCut, search version).** Given $G$, find a set $S\subseteq V$ maximizing $|\operatorname{cut}(S)|$.

<a id="pdf-bf2ce5422088-p034-b007"></a>
<!-- pdf-source: page=34; block=7; confidence=0.98 -->
MaxCut is NP-hard, while MIN-CUT is in P. The randomized procedure below achieves expected cut size at least $|E|/2$, hence at least half the optimum.

<a id="pdf-bf2ce5422088-p034-b008"></a>
<!-- pdf-source: page=34; block=8; confidence=1.00 -->
**Algorithm 2.39 (MaxCut approximation).** On a graph $G=(V,E)$ with no self-loops, independently put each vertex in a random set $S$ with probability $1/2$.

<a id="pdf-bf2ce5422088-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=0.99 -->
For each edge $e=(u,v)$, the endpoints land on opposite sides with probability $1/2$. Linearity of expectation gives
\[
\mathbb{E}[|\operatorname{cut}(S)|]=\sum_{e\in E}\Pr[e\text{ is cut}]=|E|/2.
\]
Thus the probabilistic method also implies every loopless graph has a cut of size at least $|E|/2$.

<a id="pdf-bf2ce5422088-p035-b002"></a>
<!-- pdf-source: page=35; block=2; confidence=0.98 -->
The procedure can be derandomized later; a more advanced randomized algorithm achieves expected size at least $0.878$ times the maximum cut and can also be derandomized.

<a id="pdf-bf2ce5422088-p035-b003"></a>
<!-- pdf-source: page=35; block=3; confidence=1.00 -->
## 2.4 Random Walks and S-T Connectivity

<a id="pdf-bf2ce5422088-p035-b004"></a>
<!-- pdf-source: page=35; block=4; confidence=1.00 -->
### 2.4.1 Graph Connectivity

<a id="pdf-bf2ce5422088-p035-b005"></a>
<!-- pdf-source: page=35; block=5; confidence=1.00 -->
**Computational Problem 2.40 (S-T Connectivity).** Given a directed graph $G$ and vertices $s,t$, determine whether there is a path from $s$ to $t$.

<a id="pdf-bf2ce5422088-p035-b006"></a>
<!-- pdf-source: page=35; block=6; confidence=0.98 -->
Breadth-first and depth-first search solve this in linear time and space. Space bounds here exclude read-only input and write-only output.

<a id="pdf-bf2ce5422088-p035-b007"></a>
<!-- pdf-source: page=35; block=7; confidence=1.00 -->
**Theorem 2.41.** S-T Connectivity has a deterministic algorithm using space $O(\log^2 n)$ and time $O(n\log n)$.

<a id="pdf-bf2ce5422088-p035-b008"></a>
<!-- pdf-source: page=35; block=8; confidence=1.00 -->
**Proof.** The recursive procedure $\operatorname{IsPath}(G,u,v,k)$ decides whether there is a path of length at most $k$ from $u$ to $v$.

<a id="pdf-bf2ce5422088-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=0.94 -->
**Algorithm 2.42 (Recursive S-T Connectivity).** $\operatorname{IsPath}(G,u,v,k)$: (1) If $k=0$, accept if $u=v$. (2) If $k=1$, accept if $u=v$ or $(u,v)$ is an edge in $G$. (3) Otherwise, loop through all vertices $w$ in $G$ and accept if both $\operatorname{IsPath}(G,u,w,\lfloor k/2\rfloor)$ and $\operatorname{IsPath}(G,w,v,\lceil k/2\rceil)$ accept for some $w$.

<a id="pdf-bf2ce5422088-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=0.99 -->
Run $\operatorname{IsPath}(G,s,t,n)$, where $n=|V|$. The recursion has $O(\log n)$ depth and stores $O(\log n)$ bits per level for a vertex, giving $O(\log^2 n)$ space. With linear work per level, the time is $O(n\log n)$.

<a id="pdf-bf2ce5422088-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=0.96 -->
The text reports no known improvement to the deterministic space bound or polynomial-time algorithm using space $n^{o(1)}$; for undirected graphs it turns to randomized space.

<a id="pdf-bf2ce5422088-p036-b004"></a>
<!-- pdf-source: page=36; block=4; confidence=1.00 -->
**Definition 2.43.** A language $L$ is in RL if a randomized algorithm $A$ always halts, uses $O(\log n)$ space on length-$n$ inputs, and satisfies:
- If $x\in L$, then $\Pr[A(x)\text{ accepts}]\ge 1/2$.
- If $x\notin L$, then $\Pr[A(x)\text{ accepts}]=0$.

<a id="pdf-bf2ce5422088-p036-b005"></a>
<!-- pdf-source: page=36; block=5; confidence=0.97 -->
The randomized space model provides coin tosses on demand, so needed random bits must be stored explicitly. Always halting implies polynomial running time because the configuration space has size $2^{O(\log n)}$. The supplied text ends mid-discussion.

<a id="pdf-bf2ce5422088-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=0.99 -->
For RL, we can define L (deterministic logspace), co-RL (one-sided error with errors only on no instances), and BPL (two-sided error).

<a id="pdf-bf2ce5422088-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=0.99 -->
**Computational Problem 2.44.** Given an undirected graph `G` and vertices `s,t`, decide whether a path connects `s` to `t`.

<a id="pdf-bf2ce5422088-p037-b003"></a>
<!-- pdf-source: page=37; block=3; confidence=0.99 -->
**Theorem 2.45.** Undirected S-T Connectivity belongs to `RL`.

<a id="pdf-bf2ce5422088-p037-b004"></a>
<!-- pdf-source: page=37; block=4; confidence=0.99 -->
**Proof sketch / Algorithm 2.46.** On input `(G,s,t)`, with `G=(V,E)` and `|V|=n`, set `v=s`; for `poly(n)` steps, accept if `v=t`, otherwise choose `v` uniformly from its neighbors. If the walk ends without visiting `t`, reject. The algorithm uses `O(log n)` space, never accepts when no path exists, and accepts with high probability when `s,t` are connected, using the polynomial hitting-time bound proved in the next section.

<a id="pdf-bf2ce5422088-p037-b005"></a>
<!-- pdf-source: page=37; block=5; confidence=0.99 -->
The text notes that this random-walk algorithm was derandomized in 2005; the derandomized method is deferred to Section 4.4.

<a id="pdf-bf2ce5422088-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=0.98 -->
The general derandomization of space-bounded algorithms remains unresolved.

<a id="pdf-bf2ce5422088-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=0.99 -->
**Open Problem 2.47.** Are `RL=L` and `BPL=L`?

<a id="pdf-bf2ce5422088-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=0.99 -->
## 2.4.2 Random Walks on Graphs

<a id="pdf-bf2ce5422088-p038-b004"></a>
<!-- pdf-source: page=38; block=4; confidence=0.98 -->
Graphs here may be directed multigraphs, allowing parallel edges and self-loops; graphs without either are called simple. A digraph is `d`-regular when every vertex has indegree and outdegree `d`. A self-loop contributes one to each degree. A digraph is undirected when edge multiplicities from `i` to `j` and from `j` to `i` agree; opposite directed edges represent one undirected edge, and a loop represents one undirected loop.

<a id="pdf-bf2ce5422088-p038-b005"></a>
<!-- pdf-source: page=38; block=5; confidence=0.99 -->
Bounding random-walk hitting time suffices for analyzing the connectivity algorithm.

<a id="pdf-bf2ce5422088-p038-b006"></a>
<!-- pdf-source: page=38; block=6; confidence=0.97 -->
**Definition 2.48.** For a digraph `G=(V,E)`, define `hit(G) = max_{i,j∈V} min{t : Pr[a length-t random walk started at i visits j] ≥ 1/2}`. The text says this differs by at most a factor of 2 from the alternative definition using maximum expected hitting time.

<a id="pdf-bf2ce5422088-p038-b007"></a>
<!-- pdf-source: page=38; block=7; confidence=0.99 -->
**Theorem 2.49.** For every connected undirected graph `G` with `n` vertices and maximum degree `d`, `hit(G) = O(d² n³ log n)`.

<a id="pdf-bf2ce5422088-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=0.96 -->
It suffices to prove Theorem 2.49 for `d`-regular graphs: adding self-loops can regularize an undirected graph and can only increase its hitting time. This argument does not extend to directed graphs, where loops cannot fix indegree/outdegree imbalance; the text points to Problem 2.10 for exponential hitting times in general digraphs.

<a id="pdf-bf2ce5422088-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=0.99 -->
For an `n`-vertex digraph `G`, its random-walk matrix is the `n×n` matrix `M` with `M_{i,j}` equal to the number of edges from `i` to `j` divided by the outdegree of `i`. For a `d`-regular graph, `M` is its adjacency matrix divided by `d`.

<a id="pdf-bf2ce5422088-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=0.97 -->
For a row-vector probability distribution `π`, the next-step distribution is `πM`, with `(πM)_j = Σ_i π_i M_{i,j}`. Starting from the point mass at vertex `i`, the distribution after `t` steps is `πM^t`. The proof aims to show that, for polynomial `t`, this distribution approaches the uniform distribution `u=(1/n,…,1/n)`, which is stationary for a regular graph (`uM=u`), and hence puts nonnegligible mass on any vertex.

<a id="pdf-bf2ce5422088-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=0.99 -->
For vectors $x,y\in\mathbb{R}^n$, we will use the standard inner product $\langle x,y\rangle=\sum_i x_i y_i$, and $\ell_2$ norm $\|x\|=\sqrt{\langle x,x\rangle}$. We write $x\perp y$ to mean that $x$ and $y$ are orthogonal, i.e., $\langle x,y\rangle=0$. We want to determine how large $k$ needs to be so that $\|\pi M^k-u\|$ is “small.” This is referred to as the mixing time of the random walk.

<a id="pdf-bf2ce5422088-p040-b001"></a>
<!-- pdf-source: page=40; block=1; confidence=0.99 -->
**Definition 2.50.** For a regular digraph \(G\) with random-walk matrix \(M\), we define
\[
\lambda(G)\stackrel{\mathrm{def}}{=}\max_{\pi}\frac{\|\pi M-u\|}{\|\pi-u\|}=\max_{\substack{x\perp u\\x\ne0}}\frac{\|xM\|}{\|x\|},
\]
where the first maximization is over all probability distributions \(\pi\in[0,1]^n\) and the second is over all vectors \(x\in\mathbb R^n\) such that \(x\perp u\). We write \(\gamma(G)\stackrel{\mathrm{def}}{=}1-\lambda(G)\).

<a id="pdf-bf2ce5422088-p040-b002"></a>
<!-- pdf-source: page=40; block=2; confidence=0.98 -->
**Lemma 2.51.** For a regular digraph \(G\) with random-walk matrix \(M\), any initial probability distribution \(\pi\), and \(t\in\mathbb N\),
\[
\|\pi M^t-u\|\le \lambda(G)^t\|\pi-u\|\le \lambda(G)^t.
\]

<a id="pdf-bf2ce5422088-p040-b003"></a>
<!-- pdf-source: page=40; block=3; confidence=0.99 -->
For the second inequality, we have:
\[
\begin{aligned}
\|\pi-u\|^2&=\|\pi\|^2+\|u\|^2-2\langle\pi,u\rangle\\
&=\sum_i\pi_i^2+1/N-2/N\sum_i\pi_i\\
&\le\sum_i\pi_i+1/N-2/N\sum_i\pi_i\\
&=1-1/N\le1.
\end{aligned}
\]

<a id="pdf-bf2ce5422088-p041-b001"></a>
<!-- pdf-source: page=41; block=1; confidence=0.90 -->
A smaller \(\lambda(G)\), equivalently larger \(\gamma(G)\), gives faster mixing. For \(t\ge \ln(n/\varepsilon)/\gamma(G)\), each entry of \(\pi M^t\) is at least \(1/n-(1-\gamma(G))^t\ge(1-\varepsilon)/n\), yielding mixing in \(O((\log n)/\gamma(G))\). The excerpt cautions that small \(\ell_2\) distance alone may not capture mixing: mass \(\varepsilon^2\) spread over \(1/\varepsilon^2\) vertices can be within \(\varepsilon\) of uniform in that norm.

<a id="pdf-bf2ce5422088-p041-b002"></a>
<!-- pdf-source: page=41; block=2; confidence=0.95 -->
**Corollary 2.52.** For every regular digraph \(G\), \(\operatorname{hit}(G)=O(n\log n/\gamma(G))\).

<a id="pdf-bf2ce5422088-p041-b003"></a>
<!-- pdf-source: page=41; block=3; confidence=0.94 -->
**Proof.** For vertices \(i,j\), a walk of length \(\ln(2n)/\gamma(G)\) from any starting vertex ends at \(j\) with probability at least \(1/(2n)\). Repeating such walks \(O(n)\) times hits \(j\) with probability at least \(1/2\), giving the stated order bound.

<a id="pdf-bf2ce5422088-p041-b004"></a>
<!-- pdf-source: page=41; block=4; confidence=0.98 -->
**Theorem 2.53.** If \(G\) is a connected, nonbipartite, \(d\)-regular undirected graph on \(n\) vertices, then \(\gamma(G)=\Omega(1/(dn)^2)\).

<a id="pdf-bf2ce5422088-p041-b005"></a>
<!-- pdf-source: page=41; block=5; confidence=0.92 -->
Theorem 2.53 and Corollary 2.52 imply Theorem 2.49: a connected undirected graph of maximum degree \(d\) can be made \((d+1)\)-regular and nonbipartite by adding self-loops. The cited bounds are not tight; Theorem 2.53 is assigned to Problem 2.9 using eigenvalues.

<a id="pdf-bf2ce5422088-p041-b006"></a>
<!-- pdf-source: page=41; block=6; confidence=0.99 -->
## 2.4.3 Eigenvalues

<a id="pdf-bf2ce5422088-p041-b007"></a>
<!-- pdf-source: page=41; block=7; confidence=0.98 -->
A nonzero \(v\in\mathbb R^n\) is an eigenvector of an \(n\times n\) matrix \(M\) with eigenvalue \(\lambda\in\mathbb R\) when \(vM=\lambda v\).

<a id="pdf-bf2ce5422088-p042-b001"></a>
<!-- pdf-source: page=42; block=1; confidence=0.99 -->
**Theorem 2.54 (Spectral Theorem for Symmetric Matrices).** If \(M\) is a symmetric \(n\times n\) real matrix with distinct eigenvalues \(\mu_1,\ldots,\mu_k\), then the eigenspaces \(W_i=\{v\in\mathbb R^n:vM=\mu_i v\}\) are orthogonal (i.e., \(v\in W_i,w\in W_j\Rightarrow v\perp w\) if \(i\ne j\)) and span \(\mathbb R^n\) (i.e., \(\mathbb R^n=W_1+\cdots+W_k\)). We refer to the dimension of \(W_i\) as the multiplicity of eigenvalue \(\mu_i\). In particular, \(\mathbb R^n\) has a basis consisting of orthogonal eigenvectors \(v_1,\ldots,v_n\) having respective eigenvalues \(\lambda_1,\ldots,\lambda_n\), where the number of times \(\mu_i\) occurs among the \(\lambda_j\)s exactly equals the multiplicity of \(\mu_i\).

<a id="pdf-bf2ce5422088-p042-b002"></a>
<!-- pdf-source: page=42; block=2; confidence=0.91 -->
For an undirected regular graph, \(M\) is symmetric and \(uM=u\), so uniform is an eigenvector with eigenvalue \(1\). Writing an orthogonal eigenbasis as \(u,v_2,\ldots,v_n\), any distribution has expansion \(\pi=u+\sum_{i=2}^n c_i v_i\), and
\[
\pi M^t=u+\sum_{i=2}^n \lambda_i^t c_i v_i.
\]
Problem 2.9 establishes \(|\lambda_i|\le1\); if all nonuniform eigenvalues have magnitude below one, the walk converges to uniform. This motivates identifying the mixing parameter with the largest nonuniform eigenvalue magnitude.

<a id="pdf-bf2ce5422088-p042-b003"></a>
<!-- pdf-source: page=42; block=3; confidence=0.93 -->
**Lemma 2.55.** For an undirected graph with random-walk matrix \(M\), order its eigenvalues so \(1=\lambda_1\ge |\lambda_2|\ge\cdots\ge|\lambda_n|\). Then \(\lambda(G)=|\lambda_2|\).

<a id="pdf-bf2ce5422088-p042-b004"></a>
<!-- pdf-source: page=42; block=4; confidence=0.93 -->
**Proof.** Take an orthogonal eigenbasis \(u=v_1,v_2,\ldots,v_n\). For \(x\perp u\), write \(x=\sum_{i=2}^n c_i v_i\). Then
\[
\|xM\|^2=\left\|\sum_{i=2}^n\lambda_i c_i v_i\right\|^2=\sum_{i=2}^n\lambda_i^2c_i^2\|v_i\|^2,
\]
so the operator norm on the subspace orthogonal to \(u\) is \(|\lambda_2|\), by the eigenvalue ordering and attainment at \(v_2\).

<a id="pdf-bf2ce5422088-p043-b001"></a>
<!-- pdf-source: page=43; block=1; confidence=0.99 -->
\[
\begin{aligned}
\|xM\|^2&=\|\lambda_2c_2v_2+\cdots+\lambda_nc_nv_n\|^2\\
&=\lambda_2^2c_2^2\|v_2\|^2+\cdots+\lambda_n^2c_n^2\|v_n\|^2\\
&\le |\lambda_2|^2\cdot(c_2^2\|v_2\|^2+\cdots+c_n^2\|v_n\|^2)\\
&=|\lambda_2|^2\cdot\|x\|^2.
\end{aligned}
\]
Equality is achieved with \(x=v_2\).

<a id="pdf-bf2ce5422088-p043-b002"></a>
<!-- pdf-source: page=43; block=2; confidence=0.96 -->
Bounding \(\lambda(G)\) reduces to bounding the eigenvalues of \(G\); \(\gamma(G)=1-\lambda(G)\) is called the spectral gap, measuring the separation in absolute value between the largest and second-largest eigenvalues.

<a id="pdf-bf2ce5422088-p043-b003"></a>
<!-- pdf-source: page=43; block=3; confidence=0.99 -->
## 2.4.4 Markov Chain Monte Carlo

<a id="pdf-bf2ce5422088-p043-b004"></a>
<!-- pdf-source: page=43; block=4; confidence=0.97 -->
MCMC samples from exponentially large spaces by random walks on suitable graphs; when these walks mix in polynomial time in input size, the chains are rapidly mixing and can yield exponential speedups over known deterministic methods.

<a id="pdf-bf2ce5422088-p043-b005"></a>
<!-- pdf-source: page=43; block=5; confidence=0.99 -->
## 2.5 Exercises

<a id="pdf-bf2ce5422088-p043-b006"></a>
<!-- pdf-source: page=43; block=6; confidence=0.97 -->
**Problem 2.1 (Schwartz–Zippel lemma).** Prove that for a nonzero polynomial \(f(x_1,\ldots,x_n)\) of degree \(d\) over a field or integral domain \(F\), and \(S\subseteq F\), independent uniform \(\alpha_i\in S\) satisfy
\[
\Pr[f(\alpha_1,\ldots,\alpha_n)=0]\le \frac{d}{|S|}.
\]

<a id="pdf-bf2ce5422088-p044-b001"></a>
<!-- pdf-source: page=44; block=1; confidence=0.99 -->
Problem 2.1 permits using that a nonzero univariate polynomial of degree \(d\) has at most \(d\) roots.

<a id="pdf-bf2ce5422088-p044-b002"></a>
<!-- pdf-source: page=44; block=2; confidence=0.99 -->
## 2.5 Exercises

<a id="pdf-bf2ce5422088-p044-b003"></a>
<!-- pdf-source: page=44; block=3; confidence=0.98 -->
**Problem 2.2.** Show that BPP and RP are unchanged if a randomized algorithm may request a uniform element of \(\{1,\ldots,m\}\) for any \(m\) whose binary representation it has computed, rather than only random bits.

<a id="pdf-bf2ce5422088-p044-b004"></a>
<!-- pdf-source: page=44; block=4; confidence=0.99 -->
**Problem 2.3.** Prove \(\mathrm{ZPP}=\mathrm{RP}\cap\mathrm{co\text{-}RP}\).

<a id="pdf-bf2ce5422088-p044-b005"></a>
<!-- pdf-source: page=44; block=5; confidence=0.97 -->
Problem 2.4 applies the Prime Number Theorem estimate that the number of primes below \(T\) is \((1\pm O(1))T/\ln T\), with the error tending to zero as \(T\to\infty\).

<a id="pdf-bf2ce5422088-p044-b006"></a>
<!-- pdf-source: page=44; block=6; confidence=0.98 -->
**Problem 2.4 (Polynomial Identity Testing for integer circuits).** (1) Show that if \(N\) is a nonzero integer and \(M\stackrel{R}{\leftarrow}\{1,\ldots,\log^2 N\}\), then
\[
\Pr[N\not\equiv0\pmod M]=\Omega(1/\log\log N).
\]

<a id="pdf-bf2ce5422088-p044-b007"></a>
<!-- pdf-source: page=44; block=7; confidence=0.99 -->
**Problem 2.4(2).** Use part (1) to prove Theorem 2.12: arithmetic circuit identity testing over \(\mathbb Z\) is in co-RP.

<a id="pdf-bf2ce5422088-p044-b008"></a>
<!-- pdf-source: page=44; block=8; confidence=0.99 -->
## Problem 2.5 (Polynomial Identity Testing via Modular Reduction)

<a id="pdf-bf2ce5422088-p044-b009"></a>
<!-- pdf-source: page=44; block=9; confidence=0.96 -->
The exercise studies modular reduction as an alternative identity-testing method for polynomials whose degree may exceed the field size, using analogous algebraic properties of polynomials and integers.

<a id="pdf-bf2ce5422088-p045-b001"></a>
<!-- pdf-source: page=45; block=1; confidence=0.98 -->
**Definition.** A polynomial over a field \(F\) is irreducible if it has no nontrivial factorization, meaning no factor other than a constant or a constant multiple of the polynomial itself.

<a id="pdf-bf2ce5422088-p045-b002"></a>
<!-- pdf-source: page=45; block=2; confidence=0.97 -->
It is known that the number of irreducible polynomials of degree at most \(d\) over a field \(\mathbb F\) is at least \(|\mathbb F|^{d+1}/2d\).

<a id="pdf-bf2ce5422088-p045-b003"></a>
<!-- pdf-source: page=45; block=3; confidence=0.99 -->
**Definition.** \(f(x)\bmod g(x)\) denotes the remainder upon division of \(f\) by \(g\).

<a id="pdf-bf2ce5422088-p045-b004"></a>
<!-- pdf-source: page=45; block=4; confidence=0.97 -->
The exercise represents a polynomial over finite \(F\) by a formula using field constants, variables, addition, multiplication, and binary-encoded exponents; field operations are assumed efficiently computable.

<a id="pdf-bf2ce5422088-p045-b005"></a>
<!-- pdf-source: page=45; block=5; confidence=0.98 -->
(1) Let \(f(x)\) be a univariate polynomial of degree \(\le D\) over a field \(\mathbb F\). Prove that there are constants \(c,c'\) such that if \(f(x)\) is nonzero (as a formal polynomial) and \(g(x)\) is a randomly selected polynomial of degree at most \(d=c\log D\), then the probability that \(f(x)\bmod g(x)\) is nonzero is at least \(1/c'\log D\). Deduce a randomized, polynomial-time identity test for univariate polynomials presented in the above form.

<a id="pdf-bf2ce5422088-p045-b006"></a>
<!-- pdf-source: page=45; block=6; confidence=0.99 -->
**Problem 2.5(2).** Give a deterministic reduction from multivariate identity testing to the univariate case, yielding a randomized polynomial-time test.

<a id="pdf-bf2ce5422088-p045-b007"></a>
<!-- pdf-source: page=45; block=7; confidence=0.99 -->
## Problem 2.6 (Primality Testing)

<a id="pdf-bf2ce5422088-p045-b008"></a>
<!-- pdf-source: page=45; block=8; confidence=0.98 -->
**Problem 2.6(1).** Show that for every positive integer \(n\), \((x+1)^n\equiv x^n+1\pmod n\) holds if and only if \(n\) is prime.

<a id="pdf-bf2ce5422088-p046-b001"></a>
<!-- pdf-source: page=46; block=1; confidence=1.00 -->
## 2.5 Exercises

<a id="pdf-bf2ce5422088-p046-b002"></a>
<!-- pdf-source: page=46; block=2; confidence=1.00 -->
Use Part 1 and Problem 2.5 to give a co-RP algorithm for primality testing; account for the fact that arithmetic modulo $n$ forms a field only if $n$ is prime.

<a id="pdf-bf2ce5422088-p046-b003"></a>
<!-- pdf-source: page=46; block=3; confidence=1.00 -->
## Problem 2.7 (Chernoff Bound)

<a id="pdf-bf2ce5422088-p046-b004"></a>
<!-- pdf-source: page=46; block=4; confidence=1.00 -->
Let $X_1,\ldots,X_t$ be independent random variables valued in $[0,1]$, and set $X=\sum_{i=1}^t X_i$.

<a id="pdf-bf2ce5422088-p046-b005"></a>
<!-- pdf-source: page=46; block=5; confidence=0.99 -->
(1) Prove $\mathbb E[e^{rX}]\le e^{r\mathbb E[X]+r^2t}$ for every $r\in[0,1/2]$, using $1+x\le e^x\le1+x+x^2$ on that interval. (2) Deduce the two tail bounds $\Pr[X\ge\mathbb E[X]+\varepsilon t]\le e^{-\varepsilon^2t/4}$ and $\Pr[X\le\mathbb E[X]-\varepsilon t]\le e^{-\varepsilon^2t/4}$. (3) Identify where independence is used.

<a id="pdf-bf2ce5422088-p046-b006"></a>
<!-- pdf-source: page=46; block=6; confidence=1.00 -->
## Problem 2.8 (Necessity of Randomness for Identity Testing*)

<a id="pdf-bf2ce5422088-p046-b007"></a>
<!-- pdf-source: page=46; block=7; confidence=0.99 -->
For the oracle problem of testing whether a degree-$d$ polynomial $f:\mathbb F^m\to\mathbb F$ is zero, show that every deterministic algorithm for $m=d=n$ needs at least $2^n$ oracle queries; contrast this with the one-query randomized test when $|\mathbb F|\ge2^n$. Decide whether this proves $\mathrm P\ne\mathrm{RP}$ and explain.

<a id="pdf-bf2ce5422088-p046-b008"></a>
<!-- pdf-source: page=46; block=8; confidence=1.00 -->
## Problem 2.9 (Spectral Graph Theory)

<a id="pdf-bf2ce5422088-p046-b009"></a>
<!-- pdf-source: page=46; block=9; confidence=1.00 -->
Let $M$ be the random-walk matrix of a $d$-regular undirected graph $G=(V,E)$ with $n$ vertices; loops and multiple edges are allowed. The uniform distribution is an eigenvector of $M$ with eigenvalue $1$.

<a id="pdf-bf2ce5422088-p047-b001"></a>
<!-- pdf-source: page=47; block=1; confidence=1.00 -->
Prove: (1) every eigenvalue of $M$ has absolute value at most $1$; (2) $G$ is disconnected iff eigenvalue $1$ has multiplicity at least $2$; (3) if $G$ is connected, then it is bipartite iff $-1$ is an eigenvalue of $M$.

<a id="pdf-bf2ce5422088-p047-b002"></a>
<!-- pdf-source: page=47; block=2; confidence=0.99 -->
(4) \(G\) connected \(\Rightarrow\) all eigenvalues of \(M\) other than \(\lambda_1\) are at most \(1-1/\operatorname{poly}(n,d)\). To do this, it may help to first show that the second largest eigenvalue of \(M\) (not necessarily in absolute value) equals
\[
\max_x\langle x,Mx\rangle=1-\frac1d\min_x\sum_{(i,j)\in E}(x_i-x_j)^2,
\]
where the maximum/minimum is taken over all vectors \(x\) of length \(1\) such that \(\sum_i x_i=0\), and \(\langle x,y\rangle=\sum_i x_i y_i\) is the standard inner product. For intuition, consider restricting the above maximum/minimum to \(x\in\{+\alpha,-\beta\}^n\) for \(\alpha,\beta>0\).

<a id="pdf-bf2ce5422088-p047-b003"></a>
<!-- pdf-source: page=47; block=3; confidence=0.95 -->
(5) If $G$ is connected and nonbipartite, prove every eigenvalue other than $1$ has absolute value at most $1-1/\operatorname{poly}(n,d)$, hence $\gamma(G)\ge1/\operatorname{poly}(n,d)$. (6*) Establish the tight estimate $1-\Omega(1/(dDn))$ in Part 4, where $D$ is the graph diameter, and deduce $\gamma(G)=\Omega(1/(d^2n^2))$ for connected nonbipartite $G$.

<a id="pdf-bf2ce5422088-p047-b004"></a>
<!-- pdf-source: page=47; block=4; confidence=1.00 -->
## Problem 2.10 (Hitting Time and Eigenvalues for Directed Graphs)

<a id="pdf-bf2ce5422088-p047-b005"></a>
<!-- pdf-source: page=47; block=5; confidence=0.98 -->
(1) Show that for every \(n\), there exists a digraph \(G\) with \(n\) vertices, outdegree \(2\), and \(\operatorname{hit}(G)=2^{\Omega(n)}\). (2) Let \(G\) be a regular digraph with random-walk matrix \(M\). Show that \(\lambda(G)=\sqrt{\lambda(G')}\), where \(G'\) is the undirected graph whose random-walk matrix is \(MM^T\).

<a id="pdf-bf2ce5422088-p047-b006"></a>
<!-- pdf-source: page=47; block=6; confidence=1.00 -->
**Definition.** A digraph is Eulerian if it is connected and each vertex has equal indegree and outdegree. Replacing every edge of a connected undirected graph by both directed orientations gives an example.

<a id="pdf-bf2ce5422088-p048-b001"></a>
<!-- pdf-source: page=48; block=1; confidence=1.00 -->
For an $n$-vertex Eulerian digraph of maximum degree $d$, prove $\operatorname{hit}(G)=\operatorname{poly}(n,d)$.

<a id="pdf-bf2ce5422088-p048-b002"></a>
<!-- pdf-source: page=48; block=2; confidence=1.00 -->
## Problem 2.11 (Consequences of Derandomizing prBPP)

<a id="pdf-bf2ce5422088-p048-b003"></a>
<!-- pdf-source: page=48; block=3; confidence=0.99 -->
Given $f:\{0,1\}^*\to\mathbb N$ and $\varepsilon:\mathbb N\to\mathbb R_{\ge0}$, suppose a probabilistic polynomial-time algorithm $A$ satisfies, for every $x$, $\Pr[A(x)\le f(x)\le(1+\varepsilon(|x|))A(x)]\ge2/3$. Show that $\mathrm{prBPP}=\mathrm{prP}$ yields a deterministic polynomial-time algorithm $B$ satisfying the same inequalities on every input. The hint is to use a related computational problem formulation.

<a id="pdf-bf2ce5422088-p048-b004"></a>
<!-- pdf-source: page=48; block=4; confidence=1.00 -->
**Definition.** An NP search problem is given by a polynomial-time verifier $V$ and a polynomial $p$; on input $x\in\{0,1\}^n$, the task is to find $y\in\{0,1\}^{p(n)}$ with $V(x,y)=1$.

<a id="pdf-bf2ce5422088-p048-b005"></a>
<!-- pdf-source: page=48; block=5; confidence=0.99 -->
Assume a probabilistic polynomial-time algorithm $A$ outputs a valid witness $y\in\{0,1\}^{p(n)}$ for every input $x\in\{0,1\}^n$ with probability at least $2/3$. Prove that $\mathrm{prBPP}=\mathrm{prP}$ implies a deterministic polynomial-time algorithm always outputting a valid witness. Hint: use a promise problem on pairs $(x,r)$, where $r$ is a prefix of $A$'s random bits.

<a id="pdf-bf2ce5422088-p048-b006"></a>
<!-- pdf-source: page=48; block=6; confidence=0.98 -->
The text begins introducing MA as a relaxation of NP in which the verifier $V$ is probabilistic; the remainder of the exercise is not present on the supplied page.

<a id="pdf-bf2ce5422088-p049-b001"></a>
<!-- pdf-source: page=49; block=1; confidence=0.97 -->
For a promise problem $Π=(Π_Y,Π_N)$ where the verifier accepts yes instances with probability at least $2/3$ and no instances with probability at most $1/3$, assume a randomized polynomial-time algorithm outputs a witness $y\in\{0,1\}^{p(n)}$ with $(x,y)\in Π_Y$ with probability at least $2/3$. Show that $\mathrm{prBPP}=\mathrm{prP}$ implies a deterministic polynomial-time algorithm always outputs a string $y$ with $(x,y)\notin Π_N$. For languages, this is equivalent to finding a yes witness; for general promise problems it is weaker.

<a id="pdf-bf2ce5422088-p049-b002"></a>
<!-- pdf-source: page=49; block=2; confidence=0.99 -->
(4) Using Part 3, the Prime Number Theorem (see Problem 2.4), and the fact that **Primality Testing** is in **BPP** (Problem 2.6) to show that if \(\mathrm{prBPP}=\mathrm{prP}\), then there is a deterministic polynomial-time algorithm that given a number \(N\), outputs a prime in the interval \([N,2N)\) for all sufficiently large \(N\).

<a id="pdf-bf2ce5422088-p049-b003"></a>
<!-- pdf-source: page=49; block=3; confidence=1.00 -->
## 2.6 Chapter Notes and References

<a id="pdf-bf2ce5422088-p049-b004"></a>
<!-- pdf-source: page=49; block=4; confidence=0.94 -->
The notes cite standard randomized-algorithms texts and highlight early factoring and primality algorithms, independent discoveries of randomized polynomial identity testing, and later derandomization results for restricted arithmetic formulas. They identify sources for Problems 2.4 and 2.8.

<a id="pdf-bf2ce5422088-p050-b001"></a>
<!-- pdf-source: page=50; block=1; confidence=0.98 -->
The notes point to a survey of arithmetic circuits, credit randomized perfect-matching algorithms to Lovász and later work, and cite sequential and parallel determinant algorithms. They attribute the polynomial-identity and primality algorithms in Problems 2.5–2.6 to Agrawal–Biswas and note that Agrawal–Kayal–Saxena derandomized primality testing to obtain a polynomial-time algorithm.

<a id="pdf-bf2ce5422088-p050-b002"></a>
<!-- pdf-source: page=50; block=2; confidence=0.99 -->
The randomized complexity classes **RP**, **BPP**, **ZPP**, and **PP** were formally defined by Gill, who conjectured that **BPP** \(\ne\) **P** (in fact **ZPP** \(\ne\) **P**).

<a id="pdf-bf2ce5422088-p050-b003"></a>
<!-- pdf-source: page=50; block=3; confidence=0.98 -->
The computational view of sampling is surveyed in cited work; sampling illustrates randomized algorithms whose running time is sublinear in input size, a feature now found across many problems.

<a id="pdf-bf2ce5422088-p050-b004"></a>
<!-- pdf-source: page=50; block=4; confidence=0.98 -->
Promise problems are attributed to Even, Selman, and Yacobi; a survey discusses their role in complexity theory. Problem 2.11, concerning consequences of $\mathrm{prBPP}=\mathrm{prP}$, is attributed to a cited source.

<a id="pdf-bf2ce5422088-p051-b001"></a>
<!-- pdf-source: page=51; block=1; confidence=0.94 -->
The randomized algorithm for `[(1 + ε)]`-Approx #DNF is due to Karp and Luby [236], who initiated the study of randomized algorithms for approximate counting problems. A 1/2-approximation algorithm for MaxCut was first given in [342]; that algorithm can be viewed as a natural derandomization of Algorithm 2.39. (See Algorithm 3.17.) The 0.878-approximation algorithm was given by Goemans and Williamson [154].

<a id="pdf-bf2ce5422088-p051-b002"></a>
<!-- pdf-source: page=51; block=2; confidence=0.98 -->
Savitch’s $\log^2 n$-space algorithm for directed $s$-$t$ connectivity, together with its completeness for $\mathrm{NL}$, gives $\mathrm{NL}\subseteq\mathrm{DSPACE}(\log^2 n)$, where $\mathrm{DSPACE}(\log^c n)$ denotes deterministic space $\log^c n$. Its general form is $\mathrm{NSPACE}(s(n))\subseteq\mathrm{DSPACE}(s(n)^2)$. The notes credit the randomized undirected-connectivity algorithm to Aleliunas et al. and its derandomization to Reingold.

<a id="pdf-bf2ce5422088-p051-b003"></a>
<!-- pdf-source: page=51; block=3; confidence=0.98 -->
For background on random walks, mixing, and Markov chain Monte Carlo, the notes refer to standard texts; use of the method to count perfect matchings is credited to cited work.

<a id="pdf-bf2ce5422088-p051-b004"></a>
<!-- pdf-source: page=51; block=4; confidence=0.98 -->
The bound in Theorem 2.49 is not sharp in general; for simple regular graphs it can be improved to $\Theta(n^2)$.

<a id="pdf-bf2ce5422088-p051-b005"></a>
<!-- pdf-source: page=51; block=5; confidence=0.98 -->
Although the exposition emphasizes undirected graphs, many results extend to regular or Eulerian directed graphs; Problem 2.10, Part 2, is attributed to a cited source.

<a id="pdf-bf2ce5422088-p051-b006"></a>
<!-- pdf-source: page=51; block=6; confidence=0.90 -->
The Spectral Theorem (Theorem 2.54) is standard linear algebra. A cited strengthening of Problem 2.9 gives $\gamma(G)=\Omega(1/(dD n))$, implying the tight lower bound $\gamma(G)=\Omega(1/n^2)$ for simple graphs when $D=O(n/d)$. The notes direct readers to a survey for broader spectral graph theory.

<a id="pdf-bf2ce5422088-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=1.00 -->
## 2.6 Chapter Notes and References

<a id="pdf-bf2ce5422088-p052-b002"></a>
<!-- pdf-source: page=52; block=2; confidence=0.99 -->
Randomized verification gives the classes MA and AM (both contained in IP); Graph Nonisomorphism is in AM but is not known to be in NP. Derandomizing such systems could yield short NP proofs of nonisomorphism. Randomized verification of encoded NP proofs also leads to PCPs and hardness-of-approximation applications.

<a id="pdf-bf2ce5422088-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=1.00 -->
# 3 Basic Derandomization Techniques

<a id="pdf-bf2ce5422088-p053-b002"></a>
<!-- pdf-source: page=53; block=2; confidence=0.99 -->
Examples of randomized algorithms include polynomial identity testing in co-RP, approximate #DNF counting in prBPP, perfect matching in RNC, undirected S-T connectivity in RL, and probabilistic polynomial-time MaxCut approximation. The chapter studies removing randomness, including whether BPP = P, RL = L, and RNC = NC; the introductory techniques may be infeasible or apply only in specialized settings.

<a id="pdf-bf2ce5422088-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.99 -->
These basic methods prepare for later study of pseudorandom objects as more sophisticated derandomization tools.

<a id="pdf-bf2ce5422088-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=1.00 -->
## 3.1 Enumeration

<a id="pdf-bf2ce5422088-p054-b003"></a>
<!-- pdf-source: page=54; block=3; confidence=0.98 -->
A measure of randomization's savings is the smallest deterministic time upper bound for BPP. The time hierarchy theorem separates the listed classes; more generally, for efficiently computable time bound $t$, it gives $\mathrm{DTIME}(O(t(n)/\log t(n))) \subsetneq \mathrm{DTIME}(t(n))$.

<a id="pdf-bf2ce5422088-p054-b004"></a>
<!-- pdf-source: page=54; block=4; confidence=0.99 -->
**Definition 3.1 (Deterministic Time Classes).**
\[
\begin{aligned}
\mathrm{DTIME}(t(n)) &= \{L : L\text{ can be decided deterministically in time }O(t(n))\}\\
\mathrm{P} &= \bigcup_c \mathrm{DTIME}(n^c) \qquad (\text{“polynomial time”})\\
\widetilde{\mathrm{P}} &= \bigcup_c \mathrm{DTIME}(2^{(\log n)^c}) \qquad (\text{“quasipolynomial time”})\\
\mathrm{SUBEXP} &= \bigcap_{\varepsilon} \mathrm{DTIME}(2^{n^\varepsilon}) \qquad (\text{“subexponential time”})\\
\mathrm{EXP} &= \bigcup_c \mathrm{DTIME}(2^{n^c}) \qquad (\text{“exponential time”})
\end{aligned}
\]

<a id="pdf-bf2ce5422088-p054-b005"></a>
<!-- pdf-source: page=54; block=5; confidence=0.99 -->
The stated hierarchy is $\mathrm{P}\subsetneq\widetilde{\mathrm{P}}\subsetneq\mathrm{SUBEXP}\subsetneq\mathrm{EXP}$. Separating classes defined by different resources, such as deterministic and nondeterministic time, is harder. Enumeration simulates any randomized algorithm deterministically with exponential slowdown.

<a id="pdf-bf2ce5422088-p054-b006"></a>
<!-- pdf-source: page=54; block=6; confidence=1.00 -->
**Proposition 3.2.** $\mathrm{BPP}\subset\mathrm{EXP}$.

<a id="pdf-bf2ce5422088-p054-b007"></a>
<!-- pdf-source: page=54; block=7; confidence=0.99 -->
The source notes that DTIME is sometimes abbreviated TIME. In other contexts, exponential time may mean $\mathrm{DTIME}(2^{O(n)})$ and subexponential time $\mathrm{DTIME}(2^{o(n)})$; the source uses E for the former in Section 7.

<a id="pdf-bf2ce5422088-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.99 -->
**Proof.** If $L$ is in **BPP**, then there is a probabilistic polynomial-time algorithm $A$ for $L$ running in time $t(n)$ for some polynomial $t$. As in the proof of Theorem 2.30, we write $A(x;r)$ for $A$’s output on input $x\in\{0,1\}^n$ and coin tosses $r\in\{0,1\}^{m(n)}$, where we may assume $m(n)\le t(n)$ without loss of generality. Then:
\[
\Pr[A(x;r)\text{ accepts}]=\frac{1}{2^{m(n)}}\sum_{r\in\{0,1\}^{m(n)}} A(x;r).
\]
We can compute the right-hand side of the above expression in deterministic time $2^{m(n)}\cdot t(n)$.

<a id="pdf-bf2ce5422088-p055-b002"></a>
<!-- pdf-source: page=55; block=2; confidence=0.97 -->
Exhaustive enumeration applies generally to BPP but costs exponential time; it is efficient when the random-bit count is small.

<a id="pdf-bf2ce5422088-p055-b003"></a>
<!-- pdf-source: page=55; block=3; confidence=0.99 -->
**Proposition 3.3.** If a randomized algorithm for $L$ runs in time $t(n)$ and uses $m(n)$ random bits, then $L\in\mathrm{DTIME}(t(n)2^{m(n)})$. In particular, polynomial time and $O(\log n)$ random bits imply $L\in\mathrm P$.

<a id="pdf-bf2ce5422088-p055-b004"></a>
<!-- pdf-source: page=55; block=4; confidence=0.95 -->
Reducing the random bits of every BPP algorithm to $O(\log n)$ would imply $\mathrm{BPP}=\mathrm P$; the text notes that Proposition 3.2 gives the strongest known unconditional deterministic time upper bound here.

<a id="pdf-bf2ce5422088-p055-b005"></a>
<!-- pdf-source: page=55; block=5; confidence=0.93 -->
**Open Problem 3.4.** Is BPP closer to P or EXP? Does $\mathrm{BPP}\subseteq\widetilde{\mathrm P}$ or $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$?

<a id="pdf-bf2ce5422088-p055-b006"></a>
<!-- pdf-source: page=55; block=6; confidence=0.99 -->
## 3.2 Nonconstructive/Nonuniform Derandomization

Introduces efficient derandomization that relies on nonconstructive advice depending on input length.

<a id="pdf-bf2ce5422088-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.99 -->
**Proposition 3.5.** Suppose randomized algorithm $A(x;r)$ has error probability less than $2^{-n}$ on each input $x$ of length $n$. For every $n$, there is a fixed random string $r_n$ such that $A(x;r_n)$ is correct for every $x\in\{0,1\}^n$.

<a id="pdf-bf2ce5422088-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.95 -->
**Proof.** Choose $R_n$ uniformly from the algorithm's random strings for length-$n$ inputs. By a union bound over the $2^n$ inputs, the probability that any input is answered incorrectly is at most $2^n\cdot 2^{-n}=1$ (strictly less than $1$ by the error hypothesis). Thus some fixed choice $r_n$ makes every answer correct.

<a id="pdf-bf2ce5422088-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.96 -->
Once fixed, $r_n$ permits polynomial-time evaluation, but the existence proof does not efficiently find it. Repetition can reduce the error of standard randomized classes below $2^{-n}$, so the proposition applies to them.

<a id="pdf-bf2ce5422088-p056-b004"></a>
<!-- pdf-source: page=56; block=4; confidence=0.99 -->
**Example 3.6 (Perfect Matching).** We apply the proposition to Algorithm 2.7. Let $G=(V,E)$ be a bipartite graph with $m$ vertices on each side, and let $A^G(x_{1,1},\ldots,x_{m,m})$ be the matrix that has entries $A^G_{i,j}=x_{i,j}$ if $(i,j)\in E$, and $A^G_{i,j}=0$ if $(i,j)\notin E$. Recall that the polynomial $\det(A^G(x))$ is nonzero if and only if $G$ has a perfect matching. Let $S_m=\{0,1,2,\ldots,m^2 2^{m^2}\}$. We argued that, by the Schwartz–Zippel Lemma, if we choose $\alpha\stackrel{R}{\leftarrow} S_m^{m^2}$ at random and evaluate $\det(A^G(\alpha))$, we can determine whether $\det(A^G(x))$ is zero with error probability at most $m/|S_m|$, which is smaller than $2^{-m^2}$.

<a id="pdf-bf2ce5422088-p056-b005"></a>
<!-- pdf-source: page=56; block=5; confidence=0.98 -->
The example continues on page 57, applying Proposition 3.5 to select a single evaluation point that works for every graph of the given size.

<a id="pdf-bf2ce5422088-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.99 -->
Since a bipartite graph with $m$ vertices per side is specified by a string of length $n=m^2$, by Proposition 3.5 we know that for every $m$, there exists an $\alpha_m\in S_m^{m^2}$ such that $\det(A^G(\alpha_m))\ne 0$ if and only if $G$ has a perfect matching, for every bipartite graph $G$ with $m$ vertices on each side.

<a id="pdf-bf2ce5422088-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.82 -->
**Open Problem 3.7.** Can such an $\alpha_m\in\{0,\ldots,m^2 2^{m^2}\}^{m^2}$ be constructed deterministically and efficiently? A polylogarithmic-time parallel construction with polynomially many processors would place Perfect Matching in deterministic NC; a subexponential-time construction would also be of interest.

<a id="pdf-bf2ce5422088-p057-b003"></a>
<!-- pdf-source: page=57; block=3; confidence=0.99 -->
**Example 3.8 (Universal Traversal Sequences).** Let $G$ be a connected $d$-regular undirected multigraph on $n$ vertices. From Theorem 2.49, we know that a random walk of $\mathrm{poly}(n,d)$ steps from any start vertex will visit any other vertex with high probability. By increasing the length of the walk by a polynomial factor, we can ensure that every vertex is visited with probability greater than $1-2^{-nd\log n}$. By the same reasoning as in the previous example, we conclude that for every pair $(n,d)$, there exists a universal traversal sequence $w\in\{1,2,\ldots,d\}^{\mathrm{poly}(n,d)}$ such that for every $n$-vertex, $d$-regular, connected $G$ and every vertex $s$ in $G$, if we start from $s$ and follow $w$ then we will visit the entire graph.

<a id="pdf-bf2ce5422088-p057-b004"></a>
<!-- pdf-source: page=57; block=4; confidence=0.98 -->
**Open Problem 3.9.** Can a universal traversal sequence be constructed explicitly, for example in polynomial time or logarithmic space? The text points to later progress in Section 4.4.

<a id="pdf-bf2ce5422088-p057-b005"></a>
<!-- pdf-source: page=57; block=5; confidence=0.98 -->
The text recasts the nonconstructive advice obtained from Proposition 3.5 in nonuniform complexity terminology.

<a id="pdf-bf2ce5422088-p057-b006"></a>
<!-- pdf-source: page=57; block=6; confidence=0.99 -->
**Definition 3.10.** Let $C$ be a class of languages, and $a:\mathbb{N}\to\mathbb{N}$ be a function. Then $C/a$ is the class of languages defined as follows: $L\in C/a

<a id="pdf-bf2ce5422088-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=1.00 -->
## 3.2 Nonconstructive/Nonuniform Derandomization

<a id="pdf-bf2ce5422088-p058-b002"></a>
<!-- pdf-source: page=58; block=2; confidence=0.99 -->
if there exists $L'\in C$, and $\alpha_1,\alpha_2,\ldots\in\{0,1\}^*$ with $|\alpha_n|\le a(n)$, such that $x\in L\Longleftrightarrow (x,\alpha_{|x|})\in L'$. The $\alpha$s are called the advice strings. $\mathrm{P/poly}$ is the class $\bigcup_c \mathrm{P}/n^c$, i.e., polynomial time with polynomial advice.

<a id="pdf-bf2ce5422088-p058-b003"></a>
<!-- pdf-source: page=58; block=3; confidence=1.00 -->
**Fact 3.11.** \(L\in\mathrm{P/poly}\) iff there are Boolean circuits \(C_n:\{0,1\}^n\to\{0,1\}\) deciding \(L\cap\{0,1\}^n\), with size \(|C_n|\le p(n)\) for some polynomial \(p\).

<a id="pdf-bf2ce5422088-p058-b004"></a>
<!-- pdf-source: page=58; block=4; confidence=0.99 -->
We refer to $\mathrm{P/poly}$ as a “nonuniform” model of computation because it allows for different, unrelated “programs” for each input length (e.g., the circuits $C_n$, or the advice $\alpha_n$), in contrast to classes like $\mathrm{P}$, **BPP**, and **NP**, that require a single “program” of constant size specifying how the computation should behave for inputs of arbitrary length. Although $\mathrm{P/poly}$ contains some undecidable problems, people generally believe that $\mathrm{NP}\not\subseteq\mathrm{P/poly}$. Indeed, trying to prove lower bounds on circuit size is one of the main approaches to proving $\mathrm{P}\ne\mathrm{NP}$, since circuits seem much more concrete and combinatorial than Turing machines. However, this too has turned out to be quite difficult; the best circuit lower bound known for computing an explicit function is roughly $5n$.

<a id="pdf-bf2ce5422088-p058-b005"></a>
<!-- pdf-source: page=58; block=5; confidence=1.00 -->
**Corollary 3.12.** \(\mathrm{BPP}\subseteq\mathrm{P/poly}\), following from Proposition 3.5.

<a id="pdf-bf2ce5422088-p058-b006"></a>
<!-- pdf-source: page=58; block=6; confidence=0.98 -->
The section announces a broader principle that nonuniform computation can be more powerful than randomness.

<a id="pdf-bf2ce5422088-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=1.00 -->
## 3.3 Nondeterminism

<a id="pdf-bf2ce5422088-p059-b002"></a>
<!-- pdf-source: page=59; block=2; confidence=0.98 -->
The section compares nondeterminism with randomness: for one-sided error, a successful random tape can serve as a witness; for two-sided error, verifying a correct tape is not evidently feasible.

<a id="pdf-bf2ce5422088-p059-b003"></a>
<!-- pdf-source: page=59; block=3; confidence=1.00 -->
**Proposition 3.13.** \(\mathrm{RP}\subseteq\mathrm{NP}\).

<a id="pdf-bf2ce5422088-p059-b004"></a>
<!-- pdf-source: page=59; block=4; confidence=1.00 -->
**Proof.** For \(L\in\mathrm{RP}\), a polynomial-time verifier accepts \(x\in L\) given a coin-toss sequence \(r\) for which the randomized algorithm accepts: \(A(x;r)=\mathrm{accept}\).

<a id="pdf-bf2ce5422088-p059-b005"></a>
<!-- pdf-source: page=59; block=5; confidence=0.99 -->
For BPP, a guessed random tape that yields a correct answer need not be efficiently verifiable. The text observes that current knowledge is consistent with \(\mathrm{BPP}=\mathrm{NEXP}\), then gives a conditional containment result.

<a id="pdf-bf2ce5422088-p059-b006"></a>
<!-- pdf-source: page=59; block=6; confidence=1.00 -->
**Theorem 3.14.** If \(\mathrm{P}=\mathrm{NP}\), then \(\mathrm{P}=\mathrm{BPP}\).

<a id="pdf-bf2ce5422088-p059-b007"></a>
<!-- pdf-source: page=59; block=7; confidence=0.99 -->
**Proof.** For each \(L\in\mathrm{BPP}\), express membership as \(x\in L\iff\exists y\,\forall z\,P(x,y,z)\) for a polynomial-time predicate \(P\), with \(|y|,|z|\) polynomial in \(|x|\) (3.1). If \(\mathrm{P}=\mathrm{NP}\), the universal condition is decidable in polynomial time because its complement is in NP and hence in P. Thus \(L\in\mathrm{NP}=\mathrm{P}\). The proof then begins constructing (3.1) from a randomized algorithm.

<a id="pdf-bf2ce5422088-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.99 -->
It is smaller than $2^{-n}$ and that it uses $m=\mathrm{poly}(n)$ coin tosses. Let $A_x\subseteq\{0,1\}^m$ be the set of coin tosses $r$ for which $A(x;r)=1$. We will show that if $x$ is in $L$, there exist $m$ “shifts” (or “translations”) of $A_x$ that cover all points in $\{0,1\}^m$. (Notice that this is an $\exists\forall$ statement.) Intuitively, this should be possible because $A_x$ contains all but an exponentially small fraction of $\{0,1\}^m$. On the other hand, if $x\notin L$, then no $m$ shifts of $A_x$ can cover all of $\{0,1\}^m$. Intuitively, this is because $A_x$ is an exponentially small fraction of $\{0,1\}^m$. Formally, by a “shift of $A_x$” we mean a set of the form $A_x\oplus s=\{r\oplus s:r\in A_x\}$ for some $s\in\{0,1\}^m$; note that $|A_x\oplus s|=|A_x|$. We will show
\[
\begin{aligned}
x\in L &\Rightarrow \exists s_1,s_2,\ldots,s_m\in\{0,1\}^m\ \forall r\in\{0,1\}^m\quad r\in\bigcup_{i=1}^m(A_x\oplus s_i)\\
&\Longleftrightarrow \exists s_1,s_2,\ldots,s_m\in\{0,1\}^m\ \forall r\in\{0,1\}^m\quad \bigvee_{i=1}^m(A(x;r\oplus s_i)=1),\\
x\notin L &\Rightarrow \forall s_1,s_2,\ldots,s_m\in\{0,1\}^m\ \exists r\in\{0,1\}^m\quad r\notin\bigcup_{i=1}^m(A_x\oplus s_i)\\
&\Longleftrightarrow \forall s_1,s_2,\ldots,s_m\in\{0,1\}^m\ \exists r\in\{0,1\}^m\quad \neg\bigvee_{i=1}^m(A(x;r\oplus s_i)=1).
\end{aligned}
\]

<a id="pdf-bf2ce5422088-p060-b002"></a>
<!-- pdf-source: page=60; block=2; confidence=0.99 -->
$x\notin L$. Let $s_1,\ldots,s_m$ be arbitrary, and choose $R\stackrel{R}{\leftarrow}\{0,1\}^m$ at random. Now $A_x$ and hence each $A_x\oplus s_i$ contains less than a $2^{-n}$ fraction of $\{0,1\}^m$. So, by a union bound,
\[
\Pr\left[R\in\bigcup_i(A_x\oplus s_i)\right]\le\sum_i\Pr[R\in A_x\oplus s_i]<m\cdot 2^{-n}<1,
\]
for sufficiently large $n$. In particular, there exists an $r\in\{0,1\}^m$ such that $r\notin\bigcup_i(A_x\oplus s_i)$.

<a id="pdf-bf2ce5422088-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.99 -->
$x\in L$. Choose $S_1,S_2,\ldots,S_m\stackrel{R}{\leftarrow}\{0,1\}^m$. Then, for every fixed $r$, we have:
\[
\begin{aligned}
\Pr\left[r\notin\bigcup_i(A_x\oplus S_i)\right] &= \prod_i\Pr[r\notin A_x\oplus S_i]\\
&=\prod_i\Pr[S_i\notin A_x\oplus r]\\
&< (2^{-n})^m,
\end{aligned}
\]
since $A_x$ and hence $A_x\oplus r$ contains more than a $1-2^{-n}$ fraction of $\{0,1\}^m$. By a union bound, we have:
\[
\Pr\left[\exists r\quad r\notin\bigcup_i(A_x\oplus S_i)\right]<2^m\cdot(2^{-n})^m\le 1.
\]
Thus, there exist $s_1,\ldots,s_m$ such that $\bigcup_i(A_x\oplus s_i)$ contains all points $r$ in $\{0,1\}^m$.

<a id="pdf-bf2ce5422088-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.97 -->
The preceding argument places BPP in the second level of PH; the $k$th level corresponds to analogous expressions with $k$ quantifiers.

<a id="pdf-bf2ce5422088-p061-b003"></a>
<!-- pdf-source: page=61; block=3; confidence=1.00 -->
## 3.4 The Method of Conditional Expectations

<a id="pdf-bf2ce5422088-p061-b004"></a>
<!-- pdf-source: page=61; block=4; confidence=0.99 -->
Enumeration, nonuniformity, and nondeterminism apply broadly to BPP but need not yield efficient deterministic algorithms. Conditional expectations and the following technique can be efficient in some cases, though they are less general.

<a id="pdf-bf2ce5422088-p061-b005"></a>
<!-- pdf-source: page=61; block=5; confidence=1.00 -->
### 3.4.1 The General Approach

<a id="pdf-bf2ce5422088-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.99 -->
Represent the $m$ random bits as a binary tree of coin-toss paths. Since most paths are good, seek one by choosing each next bit so that the fraction of good continuations does not decrease.

<a id="pdf-bf2ce5422088-p062-b002"></a>
<!-- pdf-source: page=62; block=2; confidence=0.99 -->
**Definition.** For a randomized algorithm $A$, input $x$, and $1\le i\le m$, define
\[
P(r_1,\ldots,r_i)=\Pr[A(x;R_1,\ldots,R_m)\text{ is correct}\mid R_1=r_1,\ldots,R_i=r_i],
\]
where the $R_j$ are independent uniform bits. Equivalently,
\[
P(r_1,\ldots,r_i)=\mathbb E_{R_{i+1}}[P(r_1,\ldots,r_i,R_{i+1})].
\]

<a id="pdf-bf2ce5422088-p062-b003"></a>
<!-- pdf-source: page=62; block=3; confidence=0.99 -->
By averaging, there exists an $r_{i+1}\in\{0,1\}$ such that $P(r_1,r_2,\ldots,r_i,r_{i+1})\ge P(r_1,r_2,\ldots,r_i)$. So at node $(r_1,r_2,\ldots,r_i)$, we simply pick $r_{i+1}$ that maximizes $P(r_1,r_2,\ldots,r_i,r_{i+1})$. At the end we have $r_1,r_2,\ldots,r_m$, and $$P(r_1,r_2,\ldots,r_m)\ge P(r_1,r_2,\ldots,r_{m-1})\ge\cdots\ge P(r_1)\ge P(A)\ge 2/3,$$

<a id="pdf-bf2ce5422088-p062-b004"></a>
<!-- pdf-source: page=62; block=4; confidence=0.96 -->
Figure 3.1 illustrates conditional good-path probabilities; a leaf marked “o” is a good path, with the example showing $P(0,1)=7/8$.

<a id="pdf-bf2ce5422088-p063-b001"></a>
<!-- pdf-source: page=63; block=1; confidence=0.95 -->
For a complete sequence of coin tosses, $P(r_1,\ldots,r_m)=1$, since that fixed path is either good or not; the preceding lower bound of $2/3$ therefore ensures it is good.

<a id="pdf-bf2ce5422088-p063-b002"></a>
<!-- pdf-source: page=63; block=2; confidence=0.98 -->
The method requires deterministic computation of each conditional expectation, which may be infeasible. It can apply to particular search tasks and quality measures, yielding, for example, a greedy algorithm.

<a id="pdf-bf2ce5422088-p063-b003"></a>
<!-- pdf-source: page=63; block=3; confidence=1.00 -->
### 3.4.2 Derandomized MAXCUT Approximation

<a id="pdf-bf2ce5422088-p063-b004"></a>
<!-- pdf-source: page=63; block=4; confidence=0.99 -->
**Definition (Computational Problem 3.15; rephrasing Problem 2.38).** Given $G=(V,E)$, find a partition $S,T$ of $V$ with $S\cup T=V$ and $S\cap T=\varnothing$ maximizing $|\operatorname{cut}(S,T)|$, where $\operatorname{cut}(S,T)=\{\{u,v\}\in E:u\in S,\ v\in T\}$.

<a id="pdf-bf2ce5422088-p063-b005"></a>
<!-- pdf-source: page=63; block=5; confidence=0.98 -->
Assigning vertices independently and uniformly to the two sides gives expected cut size at least $|E|/2$, excluding self-loops, which cannot be cut.

<a id="pdf-bf2ce5422088-p063-b006"></a>
<!-- pdf-source: page=63; block=6; confidence=0.99 -->
**Algorithm 3.16.** On a loop-free graph $G=([N],E)$, flip $N$ coins $r_1,\ldots,r_N$; put vertex $i$ in $S$ when $r_i=0$ and in $T$ when $r_i=1$, then output $(S,T)$.

<a id="pdf-bf2ce5422088-p063-b007"></a>
<!-- pdf-source: page=63; block=7; confidence=0.99 -->
**Definition.** For fixed first $i$ coin outcomes, let
\[
e(r_1,\ldots,r_i)=\mathbb E_{R_1,\ldots,R_N}\bigl[|\operatorname{cut}(S,T)|\mid R_1=r_1,\ldots,R_i=r_i\bigr],
\]
the expected cut size conditioned on those choices.

<a id="pdf-bf2ce5422088-p064-b001"></a>
<!-- pdf-source: page=64; block=1; confidence=1.00 -->
## 3.4 The Method of Conditional Expectations

<a id="pdf-bf2ce5422088-p064-b002"></a>
<!-- pdf-source: page=64; block=2; confidence=0.96 -->
For a graph with no self-loops, let $S_i=\{j\le i:r_j=0\}$, $T_i=\{j\le i:r_j=1\}$, and $U_i=\{i+1,\ldots,N\}$. After fixing $r_1,\ldots,r_i$, the expected cut size is
\[
e(r_1,\ldots,r_i)=|\operatorname{cut}(S_i,T_i)|+\tfrac12|\operatorname{cut}(U_i,[N])|. \tag{3.2}
\]
Here $\operatorname{cut}(U_i,[N])$ consists of edges with at least one endpoint in $U_i$. To choose the next bit, maximize the conditional expectation. The undecided-edge term is independent of that choice, and
\[
e(r_1,\ldots,r_i,0)-e(r_1,\ldots,r_i,1)=|\operatorname{cut}(\{i+1\},T_i)|-|\operatorname{cut}(\{i+1\},S_i)|.
\]

<a id="pdf-bf2ce5422088-p064-b003"></a>
<!-- pdf-source: page=64; block=3; confidence=0.98 -->
**Algorithm 3.17.** Initialize $S=T=\varnothing$. For $i=0,\ldots,N-1$, put vertex $i+1$ in $S$ if $|\operatorname{cut}(\{i+1\},T)|>|\operatorname{cut}(\{i+1\},S)|$; otherwise put it in $T$. The algorithm always returns a cut of size at least $|E|/2$.

<a id="pdf-bf2ce5422088-p065-b001"></a>
<!-- pdf-source: page=65; block=1; confidence=1.00 -->
## 3.5 Pairwise Independence

<a id="pdf-bf2ce5422088-p065-b002"></a>
<!-- pdf-source: page=65; block=2; confidence=1.00 -->
### 3.5.1 An Example

<a id="pdf-bf2ce5422088-p065-b003"></a>
<!-- pdf-source: page=65; block=3; confidence=0.97 -->
The random MaxCut analysis gives $\mathbb{E}[|\operatorname{cut}(S)|]=\sum_{(i,j)\in E}\Pr[R_i\ne R_j]=|E|/2$. This remains valid when the bits are pairwise independent and unbiased, so it suffices to construct such bits using fewer than $N$ random bits.

<a id="pdf-bf2ce5422088-p065-b004"></a>
<!-- pdf-source: page=65; block=4; confidence=0.99 -->
**Construction 3.18.** Given independent unbiased bits $B_1,\ldots,B_k$, define $R_S=\bigoplus_{i\in S}B_i$ for every nonempty $S\subseteq[k]$.

<a id="pdf-bf2ce5422088-p065-b005"></a>
<!-- pdf-source: page=65; block=5; confidence=0.99 -->
**Proposition 3.19.** The $2^k-1$ variables $R_S$ from Construction 3.18 are pairwise independent unbiased bits.

<a id="pdf-bf2ce5422088-p065-b006"></a>
<!-- pdf-source: page=65; block=6; confidence=0.94 -->
**Proof.** Each $R_S$ is unbiased. For distinct nonempty $S,T\subseteq[k]$,
\[
R_S=R_{S\cap T}\oplus R_{S\setminus T},\qquad R_T=R_{S\cap T}\oplus R_{T\setminus S}.
\]

<a id="pdf-bf2ce5422088-p066-b001"></a>
<!-- pdf-source: page=66; block=1; confidence=1.00 -->
## 3.5 Pairwise Independence

<a id="pdf-bf2ce5422088-p066-b002"></a>
<!-- pdf-source: page=66; block=2; confidence=0.97 -->
The bits $R_{S\cap T},R_{S\setminus T},R_{T\setminus S}$ depend on disjoint subsets of the independent $B_i$ and hence are independent; at least two of those subsets are nonempty. Consequently $(R_S,R_T)$ is uniform on $\{0,1\}^2$, proving pairwise independence.

<a id="pdf-bf2ce5422088-p066-b003"></a>
<!-- pdf-source: page=66; block=3; confidence=0.93 -->
Taking $k=\lceil\log_2(N+1)\rceil$ provides enough pairwise independent bits for the MaxCut algorithm from $k$ random bits. Enumerating all $2^k$ seeds yields a deterministic polynomial-time algorithm; it uses logarithmic workspace and is parallelizable, though slower than Algorithm 3.17. Almost pairwise independence can speed it up with a slightly worse approximation factor (Problem 3.4).

<a id="pdf-bf2ce5422088-p066-b004"></a>
<!-- pdf-source: page=66; block=4; confidence=0.96 -->
**Algorithm 3.20.** For each seed $(b_1,\ldots,b_k)$ with $k=\lceil\log_2(N+1)\rceil$, run randomized MaxCut using coins $r_S=\bigoplus_{i\in S}b_i$ for nonempty $S\subseteq[k]$, then return the largest cut found.

<a id="pdf-bf2ce5422088-p066-b005"></a>
<!-- pdf-source: page=66; block=5; confidence=1.00 -->
### 3.5.2 Pairwise Independent Hash Functions

<a id="pdf-bf2ce5422088-p066-b006"></a>
<!-- pdf-source: page=66; block=6; confidence=0.95 -->
Some applications require $N=2^n$ pairwise independent variables uniform in $\{0,1\}^m=[M]$. Generating each output bit separately uses about $nm=(\log M)(\log N)$ initial random bits, which is not logarithmic in $N$ when $M$ grows. The section introduces definitions for a more efficient construction; lowercase letters conventionally denote base-2 logarithms of corresponding uppercase letters.

<a id="pdf-bf2ce5422088-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.99 -->
A sequence of random values in \([M]^N\) can be represented as a random function \(f:[N]\to[M]\); the function view is useful for discussing computational complexity.

<a id="pdf-bf2ce5422088-p067-b002"></a>
<!-- pdf-source: page=67; block=2; confidence=0.99 -->
**Definition 3.21.** A family (multiset) \(H=\{h:[N]\to[M]\}\) is pairwise independent if, for uniformly random \(H\in H\), (1) each \(H(x)\) is uniform on \([M]\), and (2) for distinct \(x_1,x_2\in[N]\), \(H(x_1)\) and \(H(x_2)\) are independent.

<a id="pdf-bf2ce5422088-p067-b003"></a>
<!-- pdf-source: page=67; block=3; confidence=0.97 -->
Equivalently, for distinct \(x_1,x_2\in[N]\) and all \(y_1,y_2\in[M]\), \(\Pr_{H\leftarrow H}[H(x_1)=y_1\land H(x_2)=y_2]=1/M^2\). The probability is over the choice of function from the family.

<a id="pdf-bf2ce5422088-p067-b004"></a>
<!-- pdf-source: page=67; block=4; confidence=0.99 -->
**Definition 3.22.** A family \(H=\{h:[N]\to[M]\}\) is explicit if, given descriptions of \(h\) and \(x\in[N]\), one can compute \(h(x)\) in time polynomial in \(\log N,\log M\).

<a id="pdf-bf2ce5422088-p067-b005"></a>
<!-- pdf-source: page=67; block=5; confidence=0.97 -->
Pairwise independent families are also called strongly 2-universal. The weaker 2-universal condition only requires \(\Pr[H(x_1)=H(x_2)]\le 1/M\) for distinct inputs; this suffices for the deterministic MaxCut algorithm and permits including \(S=\varnothing\) in Construction 3.18.

<a id="pdf-bf2ce5422088-p067-b006"></a>
<!-- pdf-source: page=67; block=6; confidence=0.99 -->
The text announces another construction of a pairwise independent family.

<a id="pdf-bf2ce5422088-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.99 -->
## 3.5 Pairwise Independence

<a id="pdf-bf2ce5422088-p068-b002"></a>
<!-- pdf-source: page=68; block=2; confidence=0.99 -->
**Construction 3.23.** For a finite field \(F\), take \(H=\{h_{a,b}:F\to F\}_{a,b\in F}\), where \(h_{a,b}(x)=ax+b\).

<a id="pdf-bf2ce5422088-p068-b003"></a>
<!-- pdf-source: page=68; block=3; confidence=0.99 -->
**Proposition 3.24.** The family in Construction 3.23 is pairwise independent.

<a id="pdf-bf2ce5422088-p068-b004"></a>
<!-- pdf-source: page=68; block=4; confidence=0.98 -->
**Proof.** For distinct \(x_1,x_2\) and any \(y_1,y_2\), exactly one affine line contains \((x_1,y_1)\) and \((x_2,y_2)\): it has slope \(a=(y_1-y_2)/(x_1-x_2)\) and intercept \(b=y_1-ax_1\). Thus exactly one of the \(|F|^2\) choices of \((a,b)\) gives both prescribed outputs, so the probability is \(1/|F|^2\).

<a id="pdf-bf2ce5422088-p068-b005"></a>
<!-- pdf-source: page=68; block=5; confidence=0.94 -->
Selecting \(a,b\) uses \(2\log|F|\) random bits, versus \(|F|\log|F|\) bits for a truly random function and \((\log|F|)^2\) bits for the repeated construction of Proposition 3.19.

<a id="pdf-bf2ce5422088-p068-b006"></a>
<!-- pdf-source: page=68; block=6; confidence=0.99 -->
Evaluating these functions requires an efficient representation of \(F\), prompting a review of finite-field construction and arithmetic.

<a id="pdf-bf2ce5422088-p068-b007"></a>
<!-- pdf-source: page=68; block=7; confidence=0.96 -->
**Remark 3.25.** Every prime power \(q=p^k\) has a field \(F_q\), unique up to isomorphism, with characteristic \(p\). An irreducible polynomial of degree \(k\) over \(F_p=\mathbb Z_p\) gives a representation of length \(O(\log q)\) supporting addition, multiplication, and division in time polynomial in \(\log q\). The text begins comparing deterministic and probabilistic construction costs; the sentence continues on the next page.

<a id="pdf-bf2ce5422088-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.95 -->
Finding a prime \(p\) of desired bitlength \(\ell\) takes randomized time \(\operatorname{poly}(\ell)=\operatorname{poly}(\log p)\), or deterministic time \(\operatorname{poly}(2^\ell)=\operatorname{poly}(p)\). Given \(p,k\), a description of \(F_{p^k}\) can be found randomly in \(\operatorname{poly}(\log p,k)=\operatorname{poly}(\log q)\) time or deterministically in \(\operatorname{poly}(p,k)\) time. Since the deterministic methods are exponential in the bitlength of \(p\), choosing \(p=2\) permits deterministic construction in \(\operatorname{poly}(k)=\operatorname{poly}(\log q)\) time.

<a id="pdf-bf2ce5422088-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.99 -->
Using fields of size \(2^n\) gives explicit pairwise independent maps from \(\{0,1\}^n\) to itself. For \(n<m\), restrict a map from \(H_{m,m}\) by setting \(h'(x)=h(x\mathbin\Vert 0^{m-n})\). For \(m<n\), truncate a map from \(H_{n,n}\): \(h'(x)=h(x)|_m\), its first \(m\) bits.

<a id="pdf-bf2ce5422088-p069-b003"></a>
<!-- pdf-source: page=69; block=3; confidence=0.97 -->
These reductions use \(2\max\{n,m\}\) random bits. This is optimal when \(m\ge n\); when \(m<n\), the cost can be reduced to \(n+m\) bits using \((ax)|_m+b\) with \(b\in\{0,1\}^m\), in place of \((ax+b)|_m\).

<a id="pdf-bf2ce5422088-p069-b004"></a>
<!-- pdf-source: page=69; block=4; confidence=0.99 -->
**Theorem 3.26.** For every \(n,m\in\mathbb N\), there is an explicit pairwise independent family \(H_{n,m}=\{h:\{0,1\}^n\to\{0,1\}^m\}\) from which a uniformly random function can be selected using \(\max\{m,n\}+m\) random bits.

<a id="pdf-bf2ce5422088-p069-b005"></a>
<!-- pdf-source: page=69; block=5; confidence=0.99 -->
Problem 3.5 establishes that this randomness bound is essentially optimal.

<a id="pdf-bf2ce5422088-p069-b006"></a>
<!-- pdf-source: page=69; block=6; confidence=0.99 -->
## 3.5.3 Hash Tables

<a id="pdf-bf2ce5422088-p069-b007"></a>
<!-- pdf-source: page=69; block=7; confidence=0.99 -->
Pairwise independent functions were motivated by storing a set \(S\subseteq[N]\) and efficiently answering membership queries, or retrieving data associated with a key in \(S\).

<a id="pdf-bf2ce5422088-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=1.00 -->
## 3.5 Pairwise Independence

<a id="pdf-bf2ce5422088-p070-b002"></a>
<!-- pdf-source: page=70; block=2; confidence=0.98 -->
For a random function $H$ from $[N]$ to $[M]$, for any set $S$ of size at most $K$, the probability that there are any collisions is $$\Pr[\exists x\ne y\in S\text{ s.t. }H(x)=H(y)]\le\sum_{x\ne y\in S}\Pr[H(x)=H(y)]\le\binom{K}{2}\cdot\frac1M<\varepsilon$$ for $M=K^2/\varepsilon$. Notice that the above analysis does not require $H$ to be a completely random function: it suffices that $H$ be pairwise independent (or even 2-universal). Thus using Theorem 3.26, we can generate and store $H$ using $O(\log N)$ random bits. The storage required for the table $T$ is $O(M\log N)=O(K^2\log N)$ bits, which is much smaller than $N$ when $K\le N^{o(1)}$. Note that to uniquely represent a set of size $K$, we need space at least $\log\binom NK=\Omega(K\log N)$ (when $K\le N^{0.99}$). In fact, there is a data structure achieving a matching space upper bound of $O(K\log N)$, which works by taking $M=O(K)$ in the above construction and using additional hash functions to separate the (few) collisions that will occur. Often, when people analyze applications of hashing in computer science, they model the hash function as a truly random function. However, the domain of the hash function is often exponentially large, and thus it is infeasible to even write down a truly random hash function. Thus, it would be preferable to show that some explicit family of hash functions works for the application with similar performance. In many cases (such as the one above), it can be shown that pairwise independence (or $k$-wise independence, as discussed below) suffices.

<a id="pdf-bf2ce5422088-p071-b001"></a>
<!-- pdf-source: page=71; block=1; confidence=1.00 -->
## 3.5.4 Randomness-Efficient Error Reduction and Sampling

<a id="pdf-bf2ce5422088-p071-b002"></a>
<!-- pdf-source: page=71; block=2; confidence=0.95 -->
To reduce a constant-error BPP algorithm's error to $2^{-k}$, independent repetitions require $O(k)$ trials and $O(km)$ random bits when one run uses $m$ bits. The section instead uses pairwise-independent repetitions and Chebyshev's inequality, with $\operatorname{Var}[X]=\mathbb E[(X-\mu)^2]=\mathbb E[X^2]-\mu^2$.

<a id="pdf-bf2ce5422088-p071-b003"></a>
<!-- pdf-source: page=71; block=3; confidence=1.00 -->
**Lemma 3.27 (Chebyshev’s Inequality).** If $X$ has expectation $\mu$, then for $\varepsilon>0$, $$\Pr[|X-\mu|\ge\varepsilon]\le \frac{\operatorname{Var}[X]}{\varepsilon^2}.$$

<a id="pdf-bf2ce5422088-p071-b004"></a>
<!-- pdf-source: page=71; block=4; confidence=1.00 -->
**Proof.** Apply Markov's inequality (Lemma 2.20) to $Y=(X-\mu)^2$: $$\Pr[|X-\mu|\ge\varepsilon]=\Pr[(X-\mu)^2\ge\varepsilon^2]\le\frac{\mathbb E[(X-\mu)^2]}{\varepsilon^2}=\frac{\operatorname{Var}[X]}{\varepsilon^2}.$$

<a id="pdf-bf2ce5422088-p071-b005"></a>
<!-- pdf-source: page=71; block=5; confidence=1.00 -->
**Proposition 3.28 (Pairwise Independent Tail Inequality).** For pairwise independent $X_1,\ldots,X_t\in[0,1]$, define $X=\frac1t\sum_i X_i$ and $\mu=\mathbb E[X]$. Then $$\Pr[|X-\mu|\ge\varepsilon]\le\frac{1}{t\varepsilon^2}.$$

<a id="pdf-bf2ce5422088-p072-b001"></a>
<!-- pdf-source: page=72; block=1; confidence=0.99 -->
**Proof.** Let $\mu_i=\mathbb E[X_i]$. Then $$\begin{aligned}\operatorname{Var}[X]&=\mathbb E[(X-\mu)^2]\\&=\frac1{t^2}\cdot\mathbb E\left[\left(\sum_i(X_i-\mu_i)\right)^2\right]\\&=\frac1{t^2}\cdot\sum_{i,j}\mathbb E[(X_i-\mu_i)(X_j-\mu_j)]\\&=\frac1{t^2}\cdot\sum_i\mathbb E[(X_i-\mu_i)^2]\quad\text{(by pairwise independence)}\\&=\frac1{t^2}\cdot\sum_i\operatorname{Var}[X_i]\\&\le\frac1t.\end{aligned}$$ Now apply Chebyshev's Inequality.

<a id="pdf-bf2ce5422088-p072-b002"></a>
<!-- pdf-source: page=72; block=2; confidence=0.96 -->
**Error Reduction.** Since the tail bound decreases as $1/t$, $t=O(2^k)$ pairwise-independent runs reduce a BPP error from $1/3$ to $2^{-k}$. Choose $h:\{0,1\}^{k+O(1)}\to\{0,1\}^m$ from a pairwise-independent family and run the algorithm using seeds $h(x)$ for each $x$. The random-bit cost is $m+\max\{m,k+O(1)\}=O(m+k)$. The comparison table gives independent repetitions: $O(k)$ runs and $O(km)$ bits; pairwise-independent repetitions: $O(2^k)$ runs and $O(m+k)$ bits.

<a id="pdf-bf2ce5422088-p073-b001"></a>
<!-- pdf-source: page=73; block=1; confidence=0.99 -->
With repetition parameter k = O(log n), a constant-error BPP algorithm using m random bits can be amplified to error 1/poly(n) using O(m + log n) = O(m) random bits; Problem 4.6 is cited for an amplification method with no randomness overhead.

<a id="pdf-bf2ce5422088-p073-b002"></a>
<!-- pdf-source: page=73; block=2; confidence=0.99 -->
| | Number of Samples | Number of Random Bits |
|---|---:|---:|
| Truly Random Sample | $O((1/\varepsilon^2)\cdot\log(1/\delta))$ | $O(m\cdot(1/\varepsilon^2)\cdot\log(1/\delta))$ |
| Pairwise Independent Repetitions | $O((1/\varepsilon^2)\cdot(1/\delta))$ | $O(m+\log(1/\varepsilon)+\log(1/\delta))$ |

<a id="pdf-bf2ce5422088-p073-b003"></a>
<!-- pdf-source: page=73; block=3; confidence=0.99 -->
Both sampling procedures choose all oracle queries nonadaptively from their random coins and return the average of queried values; the general sampling problem imposes no such output restriction.

<a id="pdf-bf2ce5422088-p074-b001"></a>
<!-- pdf-source: page=74; block=1; confidence=1.00 -->
Section heading: 3.5 Pairwise Independence.

<a id="pdf-bf2ce5422088-p074-b002"></a>
<!-- pdf-source: page=74; block=2; confidence=0.98 -->
**Definition 3.29.** A sampler for domain size M maps a uniform seed x∈[N] to samples z₁,…,z_t∈[M]. It is a (δ,ε) averaging sampler if every f:[M]→[0,1] satisfies Pr[(1/t)∑ᵢf(zᵢ)>μ(f)+ε]≤δ (3.3), where the samples are generated by Samp(U[N]). If this condition is required only for Boolean-valued f, it is a boolean averaging sampler. The sampler is explicit if Samp(x)ᵢ is computable in time poly(log N,log t) from x∈[N] and i∈[t].

<a id="pdf-bf2ce5422088-p074-b003"></a>
<!-- pdf-source: page=74; block=3; confidence=0.99 -->
Applying (3.3) to 1−f gives the opposite-tail bound; thus the definition implies the usual absolute-error guarantee with failure probability at most 2δ. The one-sided formulation is chosen to simplify a later connection to list-decodable codes.

<a id="pdf-bf2ce5422088-p074-b004"></a>
<!-- pdf-source: page=74; block=4; confidence=0.99 -->
**Theorem 3.30 (Pairwise Independent Sampler).** For every m∈ℕ and δ,ε∈[0,1], there is an explicit (δ,ε) averaging sampler Samp:{0,1}ⁿ→({0,1}ᵐ)ᵗ using n=O(m+log(1/ε)+log(1/δ)) random bits and t=O(1/(ε²δ)) samples.

<a id="pdf-bf2ce5422088-p074-b005"></a>
<!-- pdf-source: page=74; block=5; confidence=0.97 -->
Averaging samplers are related to other pseudorandom objects, especially randomness extractors, and their restricted form is useful in some applications.

<a id="pdf-bf2ce5422088-p075-b001"></a>
<!-- pdf-source: page=75; block=1; confidence=1.00 -->
Section heading: 3.5.5 k-wise Independence.

<a id="pdf-bf2ce5422088-p075-b002"></a>
<!-- pdf-source: page=75; block=2; confidence=0.99 -->
Pairwise-independent functions and their construction extend naturally to k-wise independence.

<a id="pdf-bf2ce5422088-p075-b003"></a>
<!-- pdf-source: page=75; block=3; confidence=0.99 -->
**Definition 3.31 (k-wise independent hash functions).** For N,M,k∈ℕ with k≤N, a family H of functions [N]→[M] is k-wise independent if, for every k distinct inputs x₁,…,x_k∈[N], the values H(x₁),…,H(x_k) are independent and uniform in [M] when H is chosen uniformly from the family.

<a id="pdf-bf2ce5422088-p075-b004"></a>
<!-- pdf-source: page=75; block=4; confidence=0.99 -->
**Construction 3.32 (k-wise independence from polynomials).** Over a finite field F, take all functions h_{a₀,…,a_{k−1}}:F→F defined by h(x)=a₀+a₁x+⋯+a_{k−1}x^{k−1}, with coefficients a₀,…,a_{k−1}∈F.

<a id="pdf-bf2ce5422088-p075-b005"></a>
<!-- pdf-source: page=75; block=5; confidence=1.00 -->
**Proposition 3.33.** The family in Construction 3.32 is k-wise independent.

<a id="pdf-bf2ce5422088-p075-b006"></a>
<!-- pdf-source: page=75; block=6; confidence=0.99 -->
**Proof.** As in Proposition 3.24, it suffices to show that for distinct x₁,…,x_k∈F and arbitrary y₁,…,y_k∈F there is exactly one polynomial h of degree at most k−1 satisfying h(xᵢ)=yᵢ for every i. Existence follows from Lagrange interpolation: h(x)=∑_{i=1}^k yᵢ∏_{j≠i}(x−xⱼ)/(xᵢ−xⱼ). For uniqueness, if h and g both fit the values, h−g has degree at most k−1 and at least k roots, so it is the zero polynomial.

<a id="pdf-bf2ce5422088-p075-b007"></a>
<!-- pdf-source: page=75; block=7; confidence=1.00 -->
**Corollary 3.34.** For every $n,m,k\in\mathbb N$, there is a family of $k$-wise independent functions $\mathcal H=\{h:\{0,1\}^n\to\{0,1\}^m\}$ such that choosing

<a id="pdf-bf2ce5422088-p076-b001"></a>
<!-- pdf-source: page=76; block=1; confidence=1.00 -->
## 3.6 Exercises

<a id="pdf-bf2ce5422088-p076-b002"></a>
<!-- pdf-source: page=76; block=2; confidence=0.93 -->
The text notes that sampling and evaluating functions from a k-wise independent family have stated bit and time costs, and that k-wise independence supports derandomization and sharper tail bounds; it points to Problem 3.8.

<a id="pdf-bf2ce5422088-p076-b003"></a>
<!-- pdf-source: page=76; block=3; confidence=1.00 -->
Formally, a collection of sets $S_1,S_2,\ldots,S_m\subseteq[d]$ is called an $(\ell,a)$-design (for integers $a\le\ell\le d$) if (i) for all $i$, $|S_i|=\ell$; and (ii) for all $i\ne j$, $|S_i\cap S_j|<a$.

<a id="pdf-bf2ce5422088-p076-b004"></a>
<!-- pdf-source: page=76; block=4; confidence=0.99 -->
**Problem 3.1.** Prove that $\mathrm{prRP}=\mathrm{prP}$ implies $\mathrm{prBPP}=\mathrm{prP}$, and hence $\mathrm{BPP}=\mathrm{P}$. The hint refers to the proof that $\mathrm{NP}=\mathrm{P}$ implies $\mathrm{BPP}=\mathrm{P}$.

<a id="pdf-bf2ce5422088-p076-b005"></a>
<!-- pdf-source: page=76; block=5; confidence=0.96 -->
(1) Prove that if $m\le\binom{\binom d a}{\binom\ell a}^{2}$, then there exists an $(\ell,a)$-design $S_1,\ldots,S_m\subseteq[d]$. Hint: Use the Probabilistic Method. Specifically, show that if the sets are chosen randomly, then for every $S_1,\ldots,S_{i-1}$, $$\mathbb E_{S_i}[\#\{j<i:|S_i\cap S_j|\ge a\}]<1.$$

<a id="pdf-bf2ce5422088-p077-b001"></a>
<!-- pdf-source: page=77; block=1; confidence=1.00 -->
## 3.6 Exercises

<a id="pdf-bf2ce5422088-p077-b002"></a>
<!-- pdf-source: page=77; block=2; confidence=1.00 -->
(2) Conclude that for every constant $\gamma>0$ and every $\ell,m\in\mathbb N$, there exists an $(\ell,a)$-design $S_1,\ldots,S_m\subseteq[d]$ with $d=O(\ell^2/a)$ and $a=\gamma\cdot\log m$. In particular, setting $m=2^\ell$, we fit exponentially many sets of size $\ell$ in a universe of size $d=O(\ell)$ while keeping the intersections an arbitrarily small fraction of the set size.

<a id="pdf-bf2ce5422088-p077-b003"></a>
<!-- pdf-source: page=77; block=3; confidence=0.99 -->
**Problem 3.2(3).** Use conditional expectations to construct designs as in Parts 1 and 2 deterministically in time $\operatorname{poly}(m,d)$.

<a id="pdf-bf2ce5422088-p077-b004"></a>
<!-- pdf-source: page=77; block=4; confidence=0.99 -->
**Problem 3.3(1).** For $A\in\{0,1\}^{n\times m}$ and $b\in\{0,1\}^n$, define $h_{A,b}(x)=(Ax+b)\bmod 2$ for $x\in\{0,1\}^m$, with reduction componentwise. Show $H_{m,n}=\{h_{A,b}\}$ is pairwise independent, and compare its random-function bit cost with Construction 3.23.

<a id="pdf-bf2ce5422088-p077-b005"></a>
<!-- pdf-source: page=77; block=5; confidence=0.99 -->
**Definition.** A matrix is Toeplitz if $A_{i+1,j+1}=A_{i,j}$ for all valid indices.

<a id="pdf-bf2ce5422088-p077-b006"></a>
<!-- pdf-source: page=77; block=6; confidence=0.99 -->
**Problem 3.3(2).** Show that restricting the matrix-vector family in Part 1 to Toeplitz matrices still gives pairwise independence, and determine the random-bit cost.

<a id="pdf-bf2ce5422088-p077-b007"></a>
<!-- pdf-source: page=77; block=7; confidence=0.98 -->
**Definition.** A family $H$ of functions $[N]\to[M]$ is $\varepsilon$-almost pairwise independent if for every distinct $x_1,x_2\in[N]$ and all $y_1,y_2\in[M]$, $\Pr_{R\leftarrow H}[R(x_1)=y_1\land R(x_2)=y_2]\leq(1+\varepsilon)/M^2$. A footnote gives another convention using statistical distance from two independent uniform outputs, equivalent up to an $M^2$ factor in the error parameter.

<a id="pdf-bf2ce5422088-p078-b001"></a>
<!-- pdf-source: page=78; block=1; confidence=1.00 -->
## 3.6 Exercises

<a id="pdf-bf2ce5422088-p078-b002"></a>
<!-- pdf-source: page=78; block=2; confidence=0.97 -->
**Problem 3.4(1).** Show that there is an $\varepsilon$-almost pairwise independent family from $\{0,1\}^n$ to $\{0,1\}^m$ samplable with $O(m+\log n+\log(1/\varepsilon))$ random bits, compared with $O(m+n)$ for exact pairwise independence. The hint uses a finite field $\mathbb F$, domain $\mathbb F^{d+1}$, $h=g\circ f_a$ with $g$ from a pairwise independent family, and $f_a(x_0,\ldots,x_d)=x_0+x_1a+\cdots+x_da^d$.

<a id="pdf-bf2ce5422088-p078-b003"></a>
<!-- pdf-source: page=78; block=3; confidence=0.99 -->
**Problem 3.4(2).** Give a deterministic algorithm that, for an $N$-vertex, $M$-edge graph without self-loops, finds a cut of size at least $(1/2-o(1))M$ in time $M\,\operatorname{polylog}(N)$ and space $O(\log M)$, improving on Algorithm 3.20's $M\,\operatorname{poly}(N)$ time.

<a id="pdf-bf2ce5422088-p078-b004"></a>
<!-- pdf-source: page=78; block=4; confidence=0.99 -->
**Problem 3.5.** For a pairwise independent family $H=\{h:[N]\to[M]\}$, prove: (1) if $N\ge2$, then $|H|\ge M^2$; (2) if $M=2$, then $|H|\ge N+1$, using mutually orthogonal vectors $v_x\in\{\pm1\}^{|H|}$; (3) in general, $|H|\ge N(M-1)+1$, using $M-1$ linearly independent vectors $v_{x,y}\in\mathbb R^{|H|}$ for each $x$, with vectors for distinct inputs orthogonal; (4) for $N=2^n,M=2^m$, a random function from $H$ requires at least $\max\{n,m\}+m$ random bits.

<a id="pdf-bf2ce5422088-p078-b005"></a>
<!-- pdf-source: page=78; block=5; confidence=1.00 -->
**Problem 3.6 (Frequency Moments of Data Streams).** Given one pass through a huge “stream” of data items $(a_1,a_2,\ldots,a_k)$, where each

<a id="pdf-bf2ce5422088-p079-b001"></a>
<!-- pdf-source: page=79; block=1; confidence=0.97 -->
For a stream of items, let $m_a=\#\{i:a_i=a\}$ and $f_2=\sum_a m_a^2$. Choose $t$ random 4-wise independent maps $H_j:\{0,1\}^n\to\{+1,-1\}$ and initialize $X_j=0$. For each incoming item $a_i$, add $H_j(a_i)$ to each $X_j$; output $Y=\frac1t\sum_{j=1}^t X_j^2$. The stated storage is $O(tn+t\log k)$, compared with storing the stream or a histogram.

<a id="pdf-bf2ce5422088-p079-b002"></a>
<!-- pdf-source: page=79; block=2; confidence=0.99 -->
**Problem (title not visible).** For every fixed stream $(a_1,\ldots,a_k)$ and each $j$, show that $\mathbb E[X_j^2]=f_2$, where the expectation is over the choice of $H_j$. Show that $\operatorname{Var}[X_j^2]\le 2f_2^2$. Conclude that for a sufficiently large constant $t$, independent of $n$ and $k$, the output $Y$ is within $1\%$ of $f_2$ with probability at least $0.99$. Show how to decrease the error probability to $\delta$ while increasing the space by a factor of $\log(1/\delta)$.

<a id="pdf-bf2ce5422088-p079-b003"></a>
<!-- pdf-source: page=79; block=3; confidence=0.99 -->
**Problem 3.7.** (1) If $X\in[0,1]$ and $\mu=\mathbb E[X]$, prove $\operatorname{Var}[X]\le\mu(1-\mu)$. (2) If $X$ is the average of $t$ pairwise independent $[0,1]$-valued random variables with mean $\mu$, prove $\Pr[|X-\mu|\ge\varepsilon]\le\mu(1-\mu)/(t\varepsilon^2)$. In particular, for $t=O(1/\mu)$, show $\Pr[0.99\mu\le X\le1.01\mu]\ge0.99$.

<a id="pdf-bf2ce5422088-p080-b001"></a>
<!-- pdf-source: page=80; block=1; confidence=0.97 -->
**Problem 3.8 ($k$-wise Independent Tail Inequality).** Let $X$ be the average of $t$ $k$-wise independent random variables for an even integer $k$, and let $\mu=\mathbb E[X]$. Prove that
\[
\Pr[|X-\mu|\ge\varepsilon]\le\left(\frac{k^2}{4t\varepsilon^2}\right)^{k/2}.
\]
(Hint: show that all terms in the expansion of $\mathbb E[(X-\mu)^k]=\mathbb E[(\sum_i(X_i-\mu_i))^k]$ that involve more than $k/2$ variables $X_i$ are zero.) Note that for fixed $k$, this probability decays like $O(1/(t\varepsilon^2))^{k/2}$, improving the $1/(t\varepsilon^2)$ bound in pairwise independence when $k>2$.

<a id="pdf-bf2ce5422088-p080-b002"></a>
<!-- pdf-source: page=80; block=2; confidence=0.99 -->
**Definition (Problem 3.9).** A map $\mathrm{Samp}:[N]\to[M]^t$ is a $(\delta,\varepsilon)$ hitting sampler if every $T\subseteq[M]$ of density greater than $\varepsilon$ satisfies $\Pr_{R\leftarrow\mathrm{Samp}(U_{[N]})}[(z_1,\ldots,z_t):\exists i,\ z_i\in T]\ge1-\delta$.

<a id="pdf-bf2ce5422088-p080-b003"></a>
<!-- pdf-source: page=80; block=3; confidence=0.99 -->
**Problem 3.9.** (1) Prove every $(\delta,\varepsilon)$ averaging sampler is a $(\delta,\varepsilon)$ hitting sampler. (2) Show that for hitting samplers alone, the sample count in Theorem 3.30 can be reduced to $O(1/(\varepsilon\delta))$; the hint is to use Problem 3.7. (3) Identify the subset of BPP algorithms for which hitting samplers support randomness-efficient error reduction.

<a id="pdf-bf2ce5422088-p080-b004"></a>
<!-- pdf-source: page=80; block=4; confidence=1.00 -->
Chapter notes and references.

<a id="pdf-bf2ce5422088-p080-b005"></a>
<!-- pdf-source: page=80; block=5; confidence=0.96 -->
The notes attribute the Time Hierarchy Theorem to Hartmanis and Stearns; circuit upper bounds for RP to Adleman and for BPP to Gill; and the equivalence between polynomial-size circuits and P/poly to Pippenger. Advice-class definitions and uniform/nonuniform lower-bound connections are attributed to Karp and Lipton; a $5n-O(n)$ circuit-size lower bound for an explicit P function is cited to Iwama et al. Universal traversal sequences and the associated open construction problem are attributed to Aleliunas et al.; a conjectured deterministic NC algorithm for Perfect Matching is also cited.

<a id="pdf-bf2ce5422088-p081-b001"></a>
<!-- pdf-source: page=81; block=1; confidence=0.96 -->
(Fact 3.11.) The general definition of complexity classes with advice (Definition 3.10) is due to Karp and Lipton [235], who explored the relationship between nonuniform lower bounds and uniform lower bounds. A $5n-O(n)$ circuit-size lower bound for an explicit function (in P) was given by Iwama et al. [218, 254].

The existence of universal traversal sequences (Example 3.8) was proven by Aleliunas et al. [13], who suggested finding an explicit construction (Open Problem 3.9) as an approach to derandomizing the logspace algorithm for Undirected S-T Connectivity. For the state of the art on these problems, see Section 4.4. A conjectured deterministic NC algorithm for Perfect Matching (derandomizing Algorithm 2.7 in a different way than Open Problem 3.7) is given in [4].

Theorem 3.14 is due to Sipser [364], who proved that BPP is in the fourth level of the polynomial-time hierarchy; this was improved to the second level by Gács. Our proof of Theorem 3.14 is due to Lautemann [256]. Problem 3.1 is due to Buhrman and Fortnow [85]. For more on nondeterministic computation and nonuniform complexity, see textbooks on computational complexity, such as [32, 161, 366].

The Method of Conditional Probabilities was formalized and popularized as an algorithmic tool in the work of Spencer [370] and Raghavan [316]. Its use in Algorithm 3.17 for approximating Max-Cut is implicit in [279]. For more on this method, see the textbooks [25, 291].

A more detailed treatment of pairwise independence (along with a variety of other topics in pseudorandomness and derandomization) can be found in the survey by Luby and Wigderson [281]. The use of limited independence in computer science originates with the seminal papers of Carter and Wegman [93, 417], which introduced the notions of universal, strongly universal (i.e., $k$-wise independent), and almost strongly universal (i.e., almost $k$-wise independent) families of hash functions. The pairwise independent and $k$-wise independent sample spaces of Constructions 3.18, 3.23, and 3.32 date back to the work of Lancaster [255] and Joffe [222, 223] in the probability literature, and were rediscovered several times in the computer science literature. The construction of pairwise independent hash functions from Part 1 of Problem 3.3 is due to Carter and Wegman [93] and Part 2 is implicit

<a id="pdf-bf2ce5422088-p082-b001"></a>
<!-- pdf-source: page=82; block=1; confidence=1.00 -->
## 3.7 Chapter Notes and References

<a id="pdf-bf2ce5422088-p082-b002"></a>
<!-- pdf-source: page=82; block=2; confidence=0.99 -->
The notes attribute constructions and applications involving pairwise independence, samplers, derandomization, tail bounds, designs, and data-stream frequency moments to the cited prior works.

<a id="pdf-bf2ce5422088-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=1.00 -->
# 4 Expander Graphs

<a id="pdf-bf2ce5422088-p083-b002"></a>
<!-- pdf-source: page=83; block=2; confidence=1.00 -->
The chapter introduces expanders as sparse, well-connected pseudorandom graphs.

<a id="pdf-bf2ce5422088-p083-b003"></a>
<!-- pdf-source: page=83; block=3; confidence=1.00 -->
## 4.1 Measures of Expansion

<a id="pdf-bf2ce5422088-p083-b004"></a>
<!-- pdf-source: page=83; block=4; confidence=0.99 -->
Consider an infinite graph family $G_i$ with vertex counts $N_i$ growing and degrees $D_i$ growing slowly relative to $N_i$. The exposition generally suppresses the index and often states definitions for directed multigraphs, while focusing later on undirected multigraphs.

<a id="pdf-bf2ce5422088-p084-b001"></a>
<!-- pdf-source: page=84; block=1; confidence=1.00 -->
## 4.1 Measures of Expansion

<a id="pdf-bf2ce5422088-p084-b002"></a>
<!-- pdf-source: page=84; block=2; confidence=1.00 -->
### 4.1.1 Vertex Expansion

<a id="pdf-bf2ce5422088-p084-b003"></a>
<!-- pdf-source: page=84; block=3; confidence=0.99 -->
**Definition 4.1.** A digraph $G$ is a $(K,A)$ vertex expander if every vertex set $S$ with $|S|\le K$ has neighborhood $N(S)=\{u\mid \exists v\in S\text{ such that }(u,v)\in E\}$ satisfying $|N(S)|\ge A|S|$.

<a id="pdf-bf2ce5422088-p084-b004"></a>
<!-- pdf-source: page=84; block=4; confidence=0.99 -->
The ideal parameters are $D=O(1)$, $K=\Omega(N)$, and $A$ as close to $D$ as possible. Other measures use the boundary $\partial S=N(S)\setminus S$, the number of edges leaving $S$, a small second random-walk eigenvalue $\lambda(G)$, or edge mixing between sets. These measures are closely related and can be equivalent for some parameter ranges.

<a id="pdf-bf2ce5422088-p084-b005"></a>
<!-- pdf-source: page=84; block=5; confidence=0.99 -->
**Theorem 4.2.** For every constant $D\ge 3$, there is a constant $\alpha>0$ such that for every $N$, a random $D$-regular undirected graph on $N$ vertices is an $(\alpha N,D-1.01)$ vertex expander with probability at least $1/2$.

<a id="pdf-bf2ce5422088-p084-b006"></a>
<!-- pdf-source: page=84; block=6; confidence=0.99 -->
Note that the degree bound of 3 is the smallest possible, as every graph of degree 2 is a poor expander (being a union of cycles and chains).

<a id="pdf-bf2ce5422088-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.97 -->
Expansion above $D-1$ is generally impossible for most parameter settings; the text next proves a simpler result for bipartite expanders.

<a id="pdf-bf2ce5422088-p085-b002"></a>
<!-- pdf-source: page=85; block=2; confidence=0.99 -->
**Definition 4.3.** A bipartite multigraph $G$ is a $(K,A)$ vertex expander if every left-vertex set $S$ with $|S|\le K$ satisfies $|N(S)|\ge A|S|$.

<a id="pdf-bf2ce5422088-p085-b003"></a>
<!-- pdf-source: page=85; block=3; confidence=0.99 -->
$\mathrm{Bip}_{N,D}$ denotes bipartite multigraphs with $N$ vertices on each side, in which each left vertex has $D$ numbered neighbors (right degrees may vary).

<a id="pdf-bf2ce5422088-p085-b004"></a>
<!-- pdf-source: page=85; block=4; confidence=0.99 -->
**Theorem 4.4.** For every constant $D$, some constant $\alpha>0$ has the property that for every $N$, a uniformly random graph from $\mathrm{Bip}_{N,D}$ is an $(\alpha N,D-2)$ vertex expander with probability at least $1/2$.

<a id="pdf-bf2ce5422088-p085-b005"></a>
<!-- pdf-source: page=85; block=5; confidence=0.99 -->
**Proof.** Uniform sampling from $\mathrm{Bip}_{N,D}$ amounts to choosing each left vertex's $D$ right neighbors independently and uniformly. For $K\le\alpha N$, let $p_K$ be the probability that some left set of size $K$ has neighborhood size below $(D-2)K$. For fixed $S$, its $KD$ neighbor choices are samples with replacement from $[N]$. In their sequential listing, call a choice a repeat if it has appeared earlier. Each choice is a repeat with conditional probability at most $(i-1)/N\le KD/N$. If $|N(S)|\le(D-2)K$, there are at least $2K$ repeats, so the union bound gives $\Pr[|N(S)|\le(D-2)K]\le {KD\choose 2K}(KD/N)^{2K}$.

<a id="pdf-bf2ce5422088-p085-b006"></a>
<!-- pdf-source: page=85; block=6; confidence=0.99 -->
Thus, we find that
\[
p_K\le {N\choose K}{KD\choose 2K}\left(\frac{KD}{N}\right)^{2K}
\le \left(\frac{Ne}{K}\right)^K\left(\frac{KDe}{2K}\right)^{2K}\left(\frac{KD}{N}\right)^{2K}
=\left(\frac{e^3D^4K}{4N}\right)^K.
\]

<a id="pdf-bf2ce5422088-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=0.99 -->
Taking $\alpha=1/(e^3D^4)$ makes $p_K\le4^{-K}$ whenever $K\le\alpha N$. Therefore $\Pr[G\text{ is not an }(\alpha N,D-2)\text{ expander}]\le\sum_{K=1}^{\lfloor\alpha N\rfloor}4^{-K}<1/2$, proving Theorem 4.4.

<a id="pdf-bf2ce5422088-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=0.98 -->
Variants include using unions of $D$ random perfect matchings for two-sided regularity (with a modified repeat bound), optimizing the expansion factor for fixed $\alpha<1$ and $D>2$, and broader tradeoffs and extensions to unbalanced or nonbipartite graphs.

<a id="pdf-bf2ce5422088-p086-b003"></a>
<!-- pdf-source: page=86; block=3; confidence=0.96 -->
A stated tradeoff says that a random $D$-regular bipartite multigraph with $N$ vertices per side is an $(\alpha N,A)$ vertex expander with high probability for sufficiently large $N$ if $D>\frac{H(\alpha)+H(\alpha A)}{H(\alpha)-\alpha A H(1/A)}$, where $H(p)=p\log(1/p)+(1-p)\log(1/(1-p))$.

<a id="pdf-bf2ce5422088-p086-b004"></a>
<!-- pdf-source: page=86; block=4; confidence=0.98 -->
Expanders serve applications including fault-tolerant networks, parallel sorting, derandomization, complexity lower bounds, error-correcting codes, optimization relaxations, metric embeddings, routing, and data structures; many applications require deterministic efficient constructions.

<a id="pdf-bf2ce5422088-p087-b001"></a>
<!-- pdf-source: page=87; block=1; confidence=0.97 -->
Explicit expanders are viewed as pseudorandom objects: fixed graphs that retain many properties of random graphs. Spectral expansion measures connectivity through the convergence rate of random walks.

<a id="pdf-bf2ce5422088-p087-b002"></a>
<!-- pdf-source: page=87; block=2; confidence=0.93 -->
Recall that for an $N$-vertex regular directed graph $G$ with random-walk matrix $M$, we define
\[
\lambda(G)\stackrel{\mathrm{def}}{=}\max_{\pi}\frac{\|\pi M-u\|}{\|\pi-u\|}=\max_{x\perp u}\frac{\|xM\|}{\|x\|},
\]
where $u=(1/N,\ldots,1/N)\in\mathbb R^N$ is the uniform distribution on $[N]$, the first maximum is over all probability distributions $\pi\in[0,1]^N$, and the second maximum is over all vectors $x\in\mathbb R^N$ orthogonal to $u$. We write $\gamma(G)\stackrel{\mathrm{def}}{=}1-\lambda(G)$ to denote the spectral gap of $G$.

<a id="pdf-bf2ce5422088-p087-b003"></a>
<!-- pdf-source: page=87; block=3; confidence=0.99 -->
**Definition 4.5.** For $\gamma\in[0,1]$, a regular digraph $G$ has spectral expansion $\gamma$ if $\gamma(G)\ge\gamma$, equivalently $\lambda(G)\le1-\gamma$. Larger gap (or smaller $\lambda$) means stronger expansion.

<a id="pdf-bf2ce5422088-p087-b004"></a>
<!-- pdf-source: page=87; block=4; confidence=0.98 -->
The text notes a terminology convention: some sources call $\lambda$ spectral expansion, while this treatment uses $\gamma$ so that larger values indicate better expansion.

<a id="pdf-bf2ce5422088-p088-b001"></a>
<!-- pdf-source: page=88; block=1; confidence=0.99 -->
Section heading introducing comparisons between spectral and vertex expansion.

<a id="pdf-bf2ce5422088-p088-b002"></a>
<!-- pdf-source: page=88; block=2; confidence=0.99 -->
For common parameters, the two expansion measures are equivalent; first the text derives vertex expansion from spectral expansion.

<a id="pdf-bf2ce5422088-p088-b003"></a>
<!-- pdf-source: page=88; block=3; confidence=0.99 -->
**Theorem 4.6 (spectral expansion $\Rightarrow$ vertex expansion).** If $G$ is a regular digraph with spectral expansion $\gamma=1-\lambda$ for some $\lambda\in[0,1]$, then, for every $\alpha\in[0,1]$, $G$ is an $(\alpha N,1/((1-\alpha)\lambda^2+\alpha))$ vertex expander. In particular, $G$ is an $(N/2,1+\gamma)$ expander.

<a id="pdf-bf2ce5422088-p088-b004"></a>
<!-- pdf-source: page=88; block=4; confidence=0.99 -->
The proof uses collision probability and support size for distributions.

<a id="pdf-bf2ce5422088-p088-b005"></a>
<!-- pdf-source: page=88; block=5; confidence=0.99 -->
**Definition 4.7.** For a probability distribution $\pi$, its collision probability is $\operatorname{CP}(\pi)=\sum_x\pi_x^2$, the probability that two independent samples agree. Its support is $\operatorname{Supp}(\pi)=\{x:\pi_x>0\}$.

<a id="pdf-bf2ce5422088-p088-b006"></a>
<!-- pdf-source: page=88; block=6; confidence=0.98 -->
**Lemma 4.8.** For every probability distribution $\pi$ on $[N]$: (1) $\operatorname{CP}(\pi)=\|\pi\|_2^2=\|\pi-u\|_2^2+1/N$, where $u$ is uniform on $[N]$; (2) $\operatorname{CP}(\pi)\ge 1/|\operatorname{Supp}(\pi)|$, with equality exactly when $\pi$ is uniform on its support.

<a id="pdf-bf2ce5422088-p088-b007"></a>
<!-- pdf-source: page=88; block=7; confidence=0.99 -->
**Proof.** The collision probability equals $\sum_x\pi_x^2=\|\pi\|_2^2$. Since $\pi=u+(\pi-u)$ and $\pi-u$ is orthogonal to $u$, the squared norm is $1/N+\|\pi-u\|_2^2$. For the support bound, Cauchy–Schwarz gives $1=(\sum_{x\in\operatorname{Supp}(\pi)}\pi_x)^2\le |\operatorname{Supp}(\pi)|\sum_x\pi_x^2$; equality holds exactly for the uniform distribution on the support.

<a id="pdf-bf2ce5422088-p088-b008"></a>
<!-- pdf-source: page=88; block=8; confidence=0.96 -->
**Proof of Theorem 4.6 (continued on page 89).** Spectral expansion $\gamma=1-\lambda$ is equivalent to $\lambda(G)\le\lambda$. The argument continues on page 89 using the definition of $\lambda(G)$ and Lemma 4.8(1).

<a id="pdf-bf2ce5422088-p089-b001"></a>
<!-- pdf-source: page=89; block=1; confidence=0.98 -->
For every probability distribution $\pi$, we have
\[
\operatorname{CP}(\pi M)-\frac1N\le\lambda^2\left(\operatorname{CP}(\pi)-\frac1N\right).
\]
Letting $S$ be any subset of the vertices of size at most $\alpha N$ and $\pi$ the uniform distribution on $S$, we have $\operatorname{CP}(\pi)=1/|S|$ and $\operatorname{CP}(\pi M)\ge 1/|\operatorname{Supp}(\pi M)|=1/|N(S)|$. Thus,
\[
\frac1{|N(S)|}-\frac1N\le\lambda^2\left(\frac1{|S|}-\frac1N\right).
\]
Solving for $|N(S)|$ and using $N\ge |S|/\alpha$, we obtain $|N(S)|\ge |S|/(\lambda^2(1-\alpha)+\alpha)$, as desired.

<a id="pdf-bf2ce5422088-p089-b002"></a>
<!-- pdf-source: page=89; block=2; confidence=0.99 -->
The converse direction is harder and is stated without proof.

<a id="pdf-bf2ce5422088-p089-b003"></a>
<!-- pdf-source: page=89; block=3; confidence=0.99 -->
**Theorem 4.9 (vertex expansion ⇒ spectral expansion).** For every $\delta>0$ and $D>0$, some $\gamma>0$ exists such that every $D$-regular $(N/2,1+\delta)$ vertex expander has spectral expansion $\gamma$. One may take $\gamma=\Omega((\delta/D)^2)$.

<a id="pdf-bf2ce5422088-p089-b004"></a>
<!-- pdf-source: page=89; block=4; confidence=0.99 -->
The size threshold $N/2$ is needed because graphs formed from two disconnected good expanders can expand sets of size below half while lacking spectral expansion. The dependence on $D$ is also necessary: adding edges can preserve vertex expansion while worsening spectral expansion.

<a id="pdf-bf2ce5422088-p089-b005"></a>
<!-- pdf-source: page=89; block=5; confidence=0.99 -->
**Corollary 4.10.** For an infinite family of $D$-regular multigraphs with constant $D\in\mathbb N$, the following are equivalent: (i) some constant $\delta>0$ makes every graph an $(N/2,1+\delta)$ vertex expander; (ii) some constant $\gamma>0$ gives every graph spectral expansion $\gamma$.

<a id="pdf-bf2ce5422088-p090-b001"></a>
<!-- pdf-source: page=90; block=1; confidence=0.99 -->
Informally, an expander family is often a constant-degree regular graph family satisfying either equivalent expansion condition above.

<a id="pdf-bf2ce5422088-p090-b002"></a>
<!-- pdf-source: page=90; block=2; confidence=0.99 -->
The optimal value for the spectral expansion is also well-understood. First note that, by taking $\alpha\to 0$ in Theorem 4.6, a graph with spectral expansion $1-\lambda$ has vertex expansion $A\approx 1/\lambda^2$ for small sets. Thus, a lower bound on $\lambda$ is $1/\sqrt D-o(1)$. In fact, this lower bound can be improved, as shown in the following theorem (and proven in Problem 4.4):

<a id="pdf-bf2ce5422088-p090-b003"></a>
<!-- pdf-source: page=90; block=3; confidence=0.99 -->
**Theorem 4.11.** For every constant $D\in\mathbb N$, any $D$-regular, $N$-vertex multigraph $G$ satisfies $\lambda(G)\ge 2\sqrt{D-1}/D-O(1)$, where the $O(1)$ term vanishes as $N\to\infty$ (and $D$ is held constant).

<a id="pdf-bf2ce5422088-p090-b004"></a>
<!-- pdf-source: page=90; block=4; confidence=0.99 -->
Surprisingly, there exist explicit constructions giving $\lambda(G)<2\sqrt{D-1}/D$. Graphs meeting this bound are called Ramanujan graphs. Random graphs almost match this bound, as well:

<a id="pdf-bf2ce5422088-p090-b005"></a>
<!-- pdf-source: page=90; block=5; confidence=0.99 -->
**Theorem 4.12.** For any constant $D\in\mathbb N$, a random $D$-regular $N$-vertex graph satisfies $\lambda(G)\le 2\sqrt{D-1}/D+O(1)$ with probability $1-O(1)$, where both $O(1)$ terms vanish as $N\to\infty$ (and $D$ is held constant).

<a id="pdf-bf2ce5422088-p090-b006"></a>
<!-- pdf-source: page=90; block=6; confidence=0.92 -->
For Ramanujan graphs, Theorem 4.6 gives vertex expansion factor approximately $D/4$ for small sets; this is not tight, and the discussion continues beyond the supplied excerpt.

<a id="pdf-bf2ce5422088-p091-b001"></a>
<!-- pdf-source: page=91; block=1; confidence=0.98 -->
Ramanujan graphs can have vertex expansion only about $D/2-O(1)$ for constant-density sets, whereas the probabilistic construction in Theorem 4.2 achieves $D-O(1)$. Thus spectral expansion does not yield optimal vertex expansion; conversely, Theorem 4.9’s spectral bound worsens with degree. The two notions are broadly related, but parameter tradeoffs matter for some applications.

<a id="pdf-bf2ce5422088-p091-b002"></a>
<!-- pdf-source: page=91; block=2; confidence=1.00 -->
## 4.1.3 Other Measures of Expansion

<a id="pdf-bf2ce5422088-p091-b003"></a>
<!-- pdf-source: page=91; block=3; confidence=0.99 -->
**Definition 4.13.** For a $D$-regular digraph $G$, edge expansion means that for every vertex set $S$ with $|S|\le K$,
\[
e(S,S)\ge \varepsilon |S|D,
\]
where $e(S,T)=|\{(u,v)\in S\times T:\{u,v\}\in E\}|$ counts oriented pairs, so edges internal to $S\cap T$ are counted in both orientations. Equivalently, at least an $\varepsilon$ fraction of the edges leaving $S$ go outside it. Some conventions omit the factor $D$. For the random walk, $e(S,S)/(|S|D)$ is the one-step exit probability conditioned on starting in $S$.

<a id="pdf-bf2ce5422088-p091-b004"></a>
<!-- pdf-source: page=91; block=4; confidence=0.99 -->
The text begins comparing edge and spectral expansion for $K=N/2$; the comparison continues on the next page.

<a id="pdf-bf2ce5422088-p092-b001"></a>
<!-- pdf-source: page=92; block=1; confidence=0.99 -->
**Theorem 4.14.** Let $G$ be a $D$-regular digraph on $N$ vertices.

1. If $G$ has spectral expansion $\gamma$, then it is an $(N/2,\gamma/2)$ edge expander.
2. If $G$ is an $(N/2,\varepsilon)$ edge expander and at least an $\alpha$ fraction of the edges leaving every vertex are self-loops, for $\alpha\in[0,1]$, then $G$ has spectral expansion $\alpha\varepsilon^2/2$.

<a id="pdf-bf2ce5422088-p092-b002"></a>
<!-- pdf-source: page=92; block=2; confidence=0.99 -->
The self-loop condition rules out bipartite or more generally periodic behavior, which can allow positive edge expansion despite zero spectral expansion. With a constant self-loop fraction, edge and spectral expansion are equivalent up to constants, even at unbounded degree. The text relates edge expansion to rapid mixing and notes that the generalized notion for Markov chains is conductance. Part 1 follows from the Expander Mixing Lemma; the proof of Part 2 is omitted.

<a id="pdf-bf2ce5422088-p092-b003"></a>
<!-- pdf-source: page=92; block=3; confidence=0.99 -->
The text generalizes edge expansion to edges between arbitrary sets $S,T$: in a random-like graph, the fraction of edges from $S$ to $T$ should be close to the product of their vertex densities.

<a id="pdf-bf2ce5422088-p092-b004"></a>
<!-- pdf-source: page=92; block=4; confidence=0.99 -->
**Lemma 4.15 (Expander Mixing Lemma).** Let $G$ be a $D$-regular digraph on $N$ vertices with spectral expansion $1-\lambda$. For vertex sets $S,T$ with densities $\alpha=|S|/N$ and $\beta=|T|/N$, the statement continues on page 93.

<a id="pdf-bf2ce5422088-p093-b001"></a>
<!-- pdf-source: page=93; block=1; confidence=0.97 -->
For all vertex sets $S,T$ as above,
\[
\left|\frac{e(S,T)}{ND}-\alpha\beta\right|
\le \lambda\sqrt{\alpha(1-\alpha)\beta(1-\beta)}
\le \lambda\sqrt{\alpha\beta}
\le \lambda.
\]
Here $ND$ is the total number of oriented edges.

<a id="pdf-bf2ce5422088-p093-b002"></a>
<!-- pdf-source: page=93; block=2; confidence=0.98 -->
Observe that the denominator $N\cdot D$ counts all edges of the graph (as ordered pairs). The lemma states that the difference between the fraction of edges from $S$ to $T$ and the expected value if we were to choose $G$ randomly is “small,” roughly $\lambda$ times the square root of this fraction. Finally, note that Part 1 of Theorem 4.14 follows from the Expander Mixing Lemma by setting $T=S^c$, so $\beta=1-\alpha$ and $e(S,T)/ND\ge (1-\lambda)\cdot\alpha\cdot(1-\alpha)\ge\gamma\alpha/2$. When a digraph $G=(V,E)$ has the property that $|e(S,T)/|E|-\alpha\beta|=O(1)$ for all sets $S,T$ (with densities $\alpha,\beta$), the graph is called quasirandom. Thus, the Expander Mixing Lemma implies that a regular digraph with $\lambda(G)=O(1)$ is quasirandom. Quasirandomness has been studied extensively for dense graphs, in which case it has numerous equivalent formulations. Here we are most interested in sparse graphs, especially constant-degree graphs (for which $\lambda(G)=O(1)$ is impossible).

<a id="pdf-bf2ce5422088-p093-b003"></a>
<!-- pdf-source: page=93; block=3; confidence=0.99 -->
**Proof.** Let $\chi_S$ be the characteristic (row) vector of $S$ and $\chi_T$ the characteristic vector of $T$. Let $A$ be the adjacency matrix of $G$, and $M=A/D$ be the random-walk matrix for $G$. Note that $e(S,T)=\chi_S A\chi_T^t=\chi_S(DM)\chi_T^t$, where the superscript $t$ denotes the transpose.

We can express $\chi_S$ as the sum of two components, one parallel to the uniform distribution $u$, and the other a vector $\chi_S^\perp$, where $\chi_S^\perp\perp u$. The coefficient of $u$ is $\langle\chi_S,u\rangle/\langle u,u\rangle=\sum_i(\chi_S)_i=|S|=\alpha N$. Then $\chi_S=(\alpha N)u+\chi_S^\perp$ and similarly $\chi_T=(\beta N)u+\chi_T^\perp$.

<a id="pdf-bf2ce5422088-p094-b001"></a>
<!-- pdf-source: page=94; block=1; confidence=0.99 -->
Formally, we have
\[
\frac{e(S,T)}{N\cdot D}=\frac1N((\alpha N)u+\chi_S^\perp)M((\beta N)u+\chi_T^\perp)^t
\]
\[
=\frac1N(\alpha\beta N^2)uMu^t+\frac1N(\alpha N)uM(\chi_T^\perp)^t
+\frac1N(\beta N)\chi_S^\perp Mu^t+\frac1N\chi_S^\perp M(\chi_T^\perp)^t.
\]
Since $uM=u$ and $Mu^t=u^t$, and both $\chi_S^\perp$ and $\chi_T^\perp$ are orthogonal to $u$, the above expression simplifies to
\[
\frac{e(S,T)}{N\cdot D}=\frac{(\alpha\beta N)uu^t}{N}+\frac{\chi_S^\perp M(\chi_T^\perp)^t}{N}=\alpha\beta+\frac{(\chi_S^\perp M)(\chi_T^\perp)^t}{N}.
\]
Thus,
\[
\left|\frac{e(S,T)}{N\cdot D}-\alpha\beta\right|=\left|\frac{(\chi_S^\perp M)(\chi_T^\perp)^t}{N}\right|
\le\frac1N\|\chi_S^\perp M\|\,\|\chi_T^\perp\|
\le\frac1N\lambda\|\chi_S^\perp\|\,\|\chi_T^\perp\|.
\]
To complete the proof, we note that $\alpha N=\|\chi_S\|^2=\|(\alpha N)u\|^2+\|\chi_S^\perp\|^2=\alpha^2N+\|\chi_S^\perp\|^2$, so $\|\chi_S^\perp\|=\sqrt{\alpha(1-\alpha)N}$ and similarly $\|\chi_T^\perp\|=\sqrt{\beta(1-\beta)N}$.

<a id="pdf-bf2ce5422088-p094-b002"></a>
<!-- pdf-source: page=94; block=2; confidence=0.99 -->
**Theorem 4.16 (Converse to Expander Mixing Lemma).** Let $G$ be a $D$-regular, $N$-vertex undirected graph. Suppose that for all pairs of disjoint vertex sets $S,T$, we have $|e(S,T)/(N\cdot D)-\mu(S)\mu(T)|\le\theta\sqrt{\mu(S)\mu(T)}$ for some $\theta\in[0,1]$, where $\mu(R)=|R|/N$ for any set $R$ of vertices. Then $\lambda(G)=O(\theta\log(1/\theta))$.

<a id="pdf-bf2ce5422088-p095-b001"></a>
<!-- pdf-source: page=95; block=1; confidence=0.96 -->
The two bounds relate \(\lambda\) and \(\theta\) within a logarithmic factor, making the comparison especially useful when expansion is strong (\(\lambda\) small, or \(\gamma\) near 1).

<a id="pdf-bf2ce5422088-p095-b002"></a>
<!-- pdf-source: page=95; block=2; confidence=1.00 -->
## 4.2 Random Walks on Expanders

<a id="pdf-bf2ce5422088-p095-b003"></a>
<!-- pdf-source: page=95; block=3; confidence=0.95 -->
When \(\lambda(G)<1\), a length-\(t\) walk from any vertex is within \(\ell_2\)-distance \(\lambda^t\) of uniform; for constant-degree graphs, \(O(\log N)\) steps use \(O(\log N)\) random bits and yield a nearly uniform vertex. The walk sequence also has useful pseudorandom behavior. For reducing a randomized algorithm's error to \(2^{-k}\), expander walks achieve \(m+O(k)\) random bits and an \(O(k)\) time overhead, versus the costs of independent repetition or pairwise independence.

<a id="pdf-bf2ce5422088-p096-b001"></a>
<!-- pdf-source: page=96; block=1; confidence=0.95 -->
For \(k=O(m)\), the randomness cost \(m+O(k)\) is \((1+O(1))m\). The construction uses an expander on \(\{0,1\}^m\): choose a uniform initial vertex, then take \(t-1\) random steps, using each visited vertex as the algorithm's random-bit setting.

<a id="pdf-bf2ce5422088-p096-b002"></a>
<!-- pdf-source: page=96; block=2; confidence=0.96 -->
For an RP algorithm, accept if any walk execution accepts. On a Yes input, the rejecting coin settings form a set \(B\) of density at most \(1/2\); it suffices to bound the probability that all visited vertices lie in \(B\). For two steps, the expander mixing lemma bounds this probability by \(\mu(B)^2+\lambda\mu(B)\), close to the independent-sample value when \(\lambda\) is small relative to \(\mu(B)\).

<a id="pdf-bf2ce5422088-p096-b003"></a>
<!-- pdf-source: page=96; block=3; confidence=0.99 -->
**Theorem 4.17 (Hitting Property of Expander Walks).** If \(G\) is a regular digraph with spectral expansion \(1-\lambda\), then for any \(B\subseteq V(G)\) of density \(\mu\), a walk \((V_1,\ldots,V_t)\) of \(t-1\) steps from a uniformly random starting vertex satisfies
\[
\Pr[V_i\in B\text{ for all }i=1,\ldots,t]\leq (\mu+\lambda(1-\mu))^t.
\]

<a id="pdf-bf2ce5422088-p097-b001"></a>
<!-- pdf-source: page=97; block=1; confidence=0.98 -->
When the expansion and spectral error parameters are constants below 1, the probability that the walk remains in the set for all steps is exponentially small in the walk length, completing the RP error-reduction analysis.

<a id="pdf-bf2ce5422088-p097-b002"></a>
<!-- pdf-source: page=97; block=2; confidence=0.99 -->
The discussion compares two ways to analyze quantities expressed using the walk matrix: decompose the input vector into uniform and orthogonal parts, or decompose the matrix itself.

<a id="pdf-bf2ce5422088-p097-b003"></a>
<!-- pdf-source: page=97; block=3; confidence=0.93 -->
Write a vector as \(v=v_{\parallel}+v_{\perp}\), where \(v_{\parallel}=\langle v,u\rangle u/\langle u,u\rangle\) is its uniform-direction component and \(v_{\perp}\perp u\). Then \(vM=v_{\parallel}M+v_{\perp}M\), with \(v_{\parallel}M=v_{\parallel}\) and \(\|v_{\perp}M\|\leq\lambda\|v_{\perp}\|\). This method was used for the Expander Mixing Lemma (Lemma 4.15).

<a id="pdf-bf2ce5422088-p097-b004"></a>
<!-- pdf-source: page=97; block=4; confidence=0.99 -->
**Matrix Decomposition.** This corresponds to a different decomposition of the output vector $vM$ that can be expressed in a way that is independent of the decomposition of the input vector $v$. Specifically, if $G$ has spectral expansion $\gamma=1-\lambda$, then
\[
vM=v^{\parallel}+v^\perp M=\gamma\cdot v^{\parallel}+(\lambda\cdot v^{\parallel}+v^\perp M)
\]
\[
=v(\gamma J+\lambda E),
\]
where $J$ is the matrix in which every entry is $1/N$ and the error matrix $E$ satisfies $\|vE\|\le\|v\|$.

<a id="pdf-bf2ce5422088-p098-b001"></a>
<!-- pdf-source: page=98; block=1; confidence=0.99 -->
Indeed, if we used it to prove the Expander Mixing Lemma (without decomposing $\chi_S$ and $\chi_T$), we would get a slightly worse error term of $\lambda\sqrt{\mu(S)\mu(T)}+\lambda\mu(S)\mu(T)$.

<a id="pdf-bf2ce5422088-p098-b002"></a>
<!-- pdf-source: page=98; block=2; confidence=0.99 -->
**Definition 4.18.** The (spectral) norm of an $N\times N$ real matrix $M$ is defined to be
\[
\|M\|=\max_{x\in\mathbb R^N}\frac{\|xM\|}{\|x\|}.
\]
(If $M$ is symmetric, then $\|M\|$ equals the largest absolute value of any eigenvalue of $M$.)

<a id="pdf-bf2ce5422088-p098-b003"></a>
<!-- pdf-source: page=98; block=3; confidence=0.99 -->
**Lemma 4.19.** For a regular digraph \(G\) on \(N\) vertices with random-walk matrix \(M\), spectral expansion \(\gamma=1-\lambda\) holds iff \(M=\gamma J+\lambda E\), where \(J\) is the \(N\times N\) all-entries-\(1/N\) matrix and \(\|E\|\leq1\).

<a id="pdf-bf2ce5422088-p098-b004"></a>
<!-- pdf-source: page=98; block=4; confidence=0.93 -->
**Proof.** If \(G\) has expansion \(\gamma\), set \(E=(M-\gamma J)/\lambda\). Since \(uM=u\) and \(uJ=u\), we have \(uE=u\). For \(v\perp u\), regularity gives \(vM\perp u\), and \(vJ=0\); hence \(vE=vM/\lambda\) and \(\|vE\|\leq\|v\|\). Together with the uniform-direction action, this gives \(\|E\|\leq1\).

<a id="pdf-bf2ce5422088-p099-b001"></a>
<!-- pdf-source: page=99; block=1; confidence=0.99 -->
Conversely, if \(M=\gamma J+\lambda E\) and \(\|E\|\leq1\), then for every \(v\perp u\), \(vJ=0\), so \(\|vM\|=\|\lambda vE\|\leq\lambda\|v\|\). Thus \(G\) has spectral expansion \(\gamma\).

<a id="pdf-bf2ce5422088-p099-b002"></a>
<!-- pdf-source: page=99; block=2; confidence=0.96 -->
The decomposition suggests viewing each step as a complete-graph step with weight \(\gamma\) plus a bounded-error contribution with weight \(\lambda\). The error matrix need not be stochastic; Theorem 4.17 gives the corresponding bound \(\gamma\mu+\lambda=\mu+\lambda(1-\mu)\) on the probability of remaining in \(B\) at each step.

<a id="pdf-bf2ce5422088-p099-b003"></a>
<!-- pdf-source: page=99; block=3; confidence=0.98 -->
**Proof of Theorem 4.17.** Let \(P\) be diagonal with \(P_{i,i}=1\) for \(i\in B\) and \(0\) otherwise. For a distribution \(\pi\), its probability mass on \(B\) is \(\|\pi P\|_1\), where \(\|x\|_1=\sum_i|x_i|\). The initial distribution is uniform, represented by \(u\).

<a id="pdf-bf2ce5422088-p099-b004"></a>
<!-- pdf-source: page=99; block=4; confidence=0.99 -->
**Claim 4.20.** The probability that the random walk stays entirely within \(B\) is \(\|uP(MP)^{t-1}\|_1\).

<a id="pdf-bf2ce5422088-p099-b005"></a>
<!-- pdf-source: page=99; block=5; confidence=0.99 -->
**Proof of Claim:** By induction on $\ell$, we show that $(uP(MP)^\ell)_i$ is the probability that the first $\ell+1$ vertices of the random walk are in $B$ and the $(\ell+1)$st vertex is $i$. The base case is $\ell=0$. If $i\in B$, $(uP)_i=1/N$; if $i\notin B$, $(uP)_i=0$. Now assume the hypothesis holds up to some $\ell$. Then $(uP(MP)^\ell M)_i$ is the probability that the first $\ell+1$ vertices of the random walk are in $B$ and the $(\ell+2)$nd vertex is $i$. Multiplying by $P$, we zero out all components for nodes not in $B$ and leave the others unchanged. Thus, we obtain the probability that the first $\ell+2$ vertices are in $B$ and the $(\ell+2)$nd vertex is $i$.

<a id="pdf-bf2ce5422088-p100-b001"></a>
<!-- pdf-source: page=100; block=1; confidence=0.98 -->
To bound the probability of staying in a set using spectral expansion, the text switches to the Euclidean norm and reduces the estimate to bounding \(\|PMP\|\), using \(P^2=P\) and \(uP(MP)^{t-1}=uP(PMP)^{t-1}\).

<a id="pdf-bf2ce5422088-p100-b002"></a>
<!-- pdf-source: page=100; block=2; confidence=0.99 -->
**Claim 4.21.** \(\|PMP\|\le \mu+\lambda(1-\mu)\).

<a id="pdf-bf2ce5422088-p100-b003"></a>
<!-- pdf-source: page=100; block=3; confidence=0.94 -->
**Proof.** By the matrix decomposition in Lemma 4.19, \(M=\gamma J+\lambda E\), so \(\|PMP\|\le \gamma\|PJP\|+\lambda\|PEP\|\le\gamma\|PJP\|+\lambda\). For any vector \(x\), let \(y=xP\). Since \(PJP\) maps through the uniform direction, \(xPJP=yJP=(\sum_i y_i/N)uP\). As \(\|y\|\le\|x\|\), \(y\) has at most \(\mu N\) nonzero entries, and \(\|uP\|=\sqrt{\mu/N}\), Cauchy–Schwarz gives \(\|xPJP\|\le\mu\|x\|\). Hence \(\|PJP\|\le\mu\), and \(\|PMP\|\le\gamma\mu+\lambda=\mu+\lambda(1-\mu)\).

<a id="pdf-bf2ce5422088-p100-b004"></a>
<!-- pdf-source: page=100; block=4; confidence=0.99 -->
Using Claims 4.20 and 4.21, the probability of never leaving $B$ in a $(t-1)$-step random walk is
\[
\|uP(MP)^{t-1}\|_1\le\sqrt{\mu N}\cdot\|uP(MP)^{t-1}\|
\le\sqrt{\mu N}\cdot\|uP\|\cdot\|PMP\|^{t-1}.
\]

<a id="pdf-bf2ce5422088-p101-b001"></a>
<!-- pdf-source: page=101; block=1; confidence=0.87 -->
The preceding estimate yields \(\|uP(MP)^{t-1}\|_1\le(\mu+\lambda(1-\mu))^t\).

<a id="pdf-bf2ce5422088-p101-b002"></a>
<!-- pdf-source: page=101; block=2; confidence=0.99 -->
The hitting bounds address RP algorithms; the text next gives an expander-walk concentration bound for BPP algorithms.

<a id="pdf-bf2ce5422088-p101-b003"></a>
<!-- pdf-source: page=101; block=3; confidence=0.94 -->
**Theorem 4.22 (Chernoff Bound for Expander Walks).** Let \(G\) be a regular digraph on \(N\) vertices with spectral expansion \(1-\lambda\), and let \(f:[N]\to[0,1]\). For a random walk \(V_1,\ldots,V_t\) started uniformly, for every \(\varepsilon>0\),
\[
\Pr\!\left[\left|\frac1t\sum_{i=1}^t f(V_i)-\mu(f)\right|\ge\lambda+\varepsilon\right]\le 2e^{-\Omega(\varepsilon^2t)}.
\]

<a id="pdf-bf2ce5422088-p101-b004"></a>
<!-- pdf-source: page=101; block=4; confidence=0.98 -->
The additive error includes \(\lambda=1-\gamma\), so this estimate is useful when \(\lambda\) is small; powering the expander reduces \(\lambda\), while a stronger bound removes it from the error at the cost of an \(\Omega(\gamma\varepsilon^2t)\) exponent. The displayed theorem suffices when a small constant error is acceptable.

<a id="pdf-bf2ce5422088-p101-b005"></a>
<!-- pdf-source: page=101; block=5; confidence=0.96 -->
**Proof.** Set \(X_i=f(V_i)\) and \(X=\sum_i X_i\). As in the usual Chernoff argument, bound the moment generating function \(\mathbb E[e^{rX}]\) and apply Markov's inequality for a suitable \(r\). Since the \(e^{rX_i}\) are dependent, the expectation does not factor. The proof instead represents it using a diagonal matrix \(P\) whose \((i,i)\)-entry is \(e^{rf(i)}\).

<a id="pdf-bf2ce5422088-p102-b001"></a>
<!-- pdf-source: page=102; block=1; confidence=0.99 -->
Then, similarly to Claim 4.20 in the proof of the hitting proof above, we observe that
\[
\mathbb E[e^{rX}]=|uP(MP)^{t-1}|_1=|u(MP)^t|_1\le\sqrt N\cdot\|u\|\cdot\|MP\|^t=\|MP\|^t.
\]
To see this, we simply note that each cross-term in the matrix product $uP(MP)^{t-1}$ corresponds to exactly one expander walk $v_1,\ldots,v_t$, with a coefficient equal to the probability of this walk times $\prod_i e^{rf(v_i)}$.

<a id="pdf-bf2ce5422088-p102-b002"></a>
<!-- pdf-source: page=102; block=2; confidence=0.99 -->
By the Matrix Decomposition Lemma (Lemma 4.19), we can bound
\[
\|MP\|\le(1-\lambda)\cdot\|JP\|+\lambda\cdot\|EP\|.
\]
Since $J$ simply projects onto the uniform direction, we have
\[
\|JP\|^2=\frac{\|uP\|^2}{\|u\|^2}
=\frac{\sum_v(e^{r\cdot f(v)}/N)^2}{\sum_v(1/N)^2}
=\frac1N\sum_v e^{2r f(v)}
=\frac1N\sum_v(1+2r f(v)+O(r^2))
=1+2r\mu+O(r^2),
\]
for $r\le1$, and thus $\|JP\|=\sqrt{1+2r\mu+O(r^2)}=1+r\mu+O(r^2)$. For the error term, we have $\|EP\|\le\|P\|\le e^r=1+r+O(r^2)$. Thus,
\[
\|MP\|\le(1-\lambda)\cdot(1+r\mu+O(r^2))+\lambda\cdot(1+r+O(r^2))\le1+(\mu+\lambda)r+O(r^2),
\]
and we have
\[
\mathbb E[e^{rX}]\le(1+(\mu+\lambda)r+O(r^2))^t\le e^{(\mu+\lambda)rt+O(r^2t)}.
\]

<a id="pdf-bf2ce5422088-p103-b001"></a>
<!-- pdf-source: page=103; block=1; confidence=0.98 -->
By Markov’s inequality, for sufficiently large constant c and r=ε/c, Pr[X ≥ (μ+λ+ε)t] ≤ e^(−εrt+O(r²t)) = e^(−Ω(ε²t)). Applying the same argument to 1−f gives Pr[X ≤ (μ−λ−ε)t] = e^(−Ω(ε²t)); together these establish the theorem.

<a id="pdf-bf2ce5422088-p103-b002"></a>
<!-- pdf-source: page=103; block=2; confidence=0.99 -->
For reducing the error of a BPP algorithm from 1/3 to 2^{−k}, we can apply Theorem 4.22 with λ = ε = 1/12, so that a walk of length t = O(k) suffices. If the original BPP algorithm used m random bits and the expander is of constant degree (which is possible with λ = 1/12), then the number of random bits needed is only m + O(k). Comparing with previous methods for error reduction, we have:

|  | Number of Repetitions | Number of Random Bits |
|---|---:|---:|
| Independent Repetitions | O(k) | O(km) |
| Pairwise Independent Repetitions | O(2^k) | O(k + m) |
| Expander Walks | O(k) | m + O(k) |

<a id="pdf-bf2ce5422088-p103-b003"></a>
<!-- pdf-source: page=103; block=3; confidence=0.99 -->
For sampling, where we are given an oracle to a function f : {0,1}^m → [0,1] and we want to approximate μ(f) to within an additive error of ε, we can apply Theorem 4.22 with error ε/2 and λ = ε/2. The needed expander can be obtained by taking an O(log(1/ε))th power of a constant-degree expander, yielding the following bounds:

|  | Number of Samples | Number of Random Bits |
|---|---:|---:|
| Truly Random Sample | O((1/ε²) · log(1/δ)) | O(m · (1/ε²) · log(1/δ)) |
| Pairwise Independent Samples | O((1/ε²) · (1/δ)) | O(m + log(1/ε) + log(1/δ)) |
| Expander Walks | O((1/ε²) · log(1/δ)) | m + O(log(1/δ) · (log(1/ε)/ε²)) |

<a id="pdf-bf2ce5422088-p104-b001"></a>
<!-- pdf-source: page=104; block=1; confidence=0.96 -->
The expander-walk bit bound includes log(1/ε) from powering a constant-degree expander, with O(log(1/ε)) random bits per step. Expander walks improve dependence on failure probability δ in sample count relative to pairwise independence, but worsen dependence on approximation error ε in random-bit count; Problem 4.5 combines the two approaches.

<a id="pdf-bf2ce5422088-p104-b002"></a>
<!-- pdf-source: page=104; block=2; confidence=0.99 -->
**Theorem 4.23 (Expander-Walk Sampler).** For every m∈N and δ,ε∈[0,1], there is a (δ,ε)-averaging sampler Samp:{0,1}^n→({0,1}^m)^t using n=m+O(log(1/δ)·log(1/ε)/ε²) random bits and t=O(ε^(−2)log(1/δ)) samples.

<a id="pdf-bf2ce5422088-p104-b003"></a>
<!-- pdf-source: page=104; block=3; confidence=0.97 -->
The sampler combining expander walks and pairwise independence from Problem 4.5 is not an averaging sampler; obtaining an explicit averaging sampler with comparable parameters remains open.

<a id="pdf-bf2ce5422088-p104-b004"></a>
<!-- pdf-source: page=104; block=4; confidence=0.99 -->
**Open Problem 4.24.** Give an explicit construction of a (δ, ε) averaging sampler Samp : {0,1}^n → ({0,1}^m)^t that uses n = O(m + log(δ) + log(1/ε)) random bits and t = O((1/ε²) · log(1/δ)) samples.

<a id="pdf-bf2ce5422088-p104-b005"></a>
<!-- pdf-source: page=104; block=5; confidence=0.97 -->
The expander-walk applications described so far are not efficient: they assume an exponentially large expander on 2^m vertices, where m is the algorithm’s random-bit count. Randomly generating such a graph is too costly, and even deterministically generating and writing it down requires exponential size. The next section develops succinct explicit expanders and efficient walks on them.

<a id="pdf-bf2ce5422088-p105-b001"></a>
<!-- pdf-source: page=105; block=1; confidence=1.00 -->
## 4.3 Explicit Constructions

<a id="pdf-bf2ce5422088-p105-b002"></a>
<!-- pdf-source: page=105; block=2; confidence=0.97 -->
Random expanders may suffice for some applications, but explicit constructions are needed for several reasons: a rare failure to be an expander may be unacceptable (and checking combinatorial expansion is NP-hard for most measures, though spectral expansion is polynomial-time computable); random selection defeats applications intended to reduce randomness; and some applications require exponentially large graphs that cannot be written down. Explicit constructions also reflect understanding of these combinatorial objects.

<a id="pdf-bf2ce5422088-p106-b001"></a>
<!-- pdf-source: page=106; block=1; confidence=1.00 -->
## 4.3 Explicit Constructions

<a id="pdf-bf2ce5422088-p106-b002"></a>
<!-- pdf-source: page=106; block=2; confidence=0.99 -->
**Mildly explicit:** construct a complete representation of an $N$-node graph in time $\operatorname{poly}(N)$. **Fully explicit:** given $u\in[N]$ and $i\in[D]$, compute the $i$th neighbor of $u$ in time $\operatorname{poly}(\log N)$.

<a id="pdf-bf2ce5422088-p106-b003"></a>
<!-- pdf-source: page=106; block=3; confidence=0.98 -->
The stated goal is an infinite family of fully explicit $D$-regular graphs with spectral expansion at least a constant $\gamma>0$, where $D,\gamma$ do not depend on the family index. The vertex counts should also be sufficiently dense to provide sizes near a desired value.

<a id="pdf-bf2ce5422088-p106-b004"></a>
<!-- pdf-source: page=106; block=4; confidence=1.00 -->
## 4.3.1 Algebraic Constructions

<a id="pdf-bf2ce5422088-p106-b005"></a>
<!-- pdf-source: page=106; block=5; confidence=0.99 -->
**Construction 4.25.** Take $V=\mathbb Z_M\times\mathbb Z_M$. From each $(x,y)$, draw directed edges to $(x,y)$, $(x+1,y)$, $(x,y+1)$, $(x,x+y)$, and $(-y,x)$, with arithmetic modulo $M$.

<a id="pdf-bf2ce5422088-p107-b001"></a>
<!-- pdf-source: page=107; block=1; confidence=0.99 -->
This is a fully explicit 5-regular digraph on $N=M^2$ vertices with spectral expansion $\gamma=\Omega(1)$. Adding reverse copies makes it undirected. Its expansion was proved using group representation theory; related variants have Fourier-analytic proofs.

<a id="pdf-bf2ce5422088-p107-b002"></a>
<!-- pdf-source: page=107; block=2; confidence=0.99 -->
**Construction 4.26.** Let $V=\mathbb Z_p$. Each $x$ is connected to $x+1$, $x-1$, and $x^{-1}$ modulo $p$, with $0^{-1}=0$.

<a id="pdf-bf2ce5422088-p107-b003"></a>
<!-- pdf-source: page=107; block=3; confidence=0.97 -->
The construction is mildly explicit; deterministic polynomial-time construction requires finding an $n$-bit prime. Its expansion proof uses the Selberg $3/16$ theorem.

<a id="pdf-bf2ce5422088-p107-b004"></a>
<!-- pdf-source: page=107; block=4; confidence=0.98 -->
**Construction 4.27 (Ramanujan graphs).** G = (V, E) is a graph with vertex set V = F_q ∪ {∞}, the finite field of prime order q s.t. q ≡ 1 mod 4 plus one extra node representing infinity. The edges in this graph connect each node z with all z′ of the form:

z′ = ((a₀ + i a₁)z + (a₂ + i a₃)) / ((−a₂ + i a₃)z + (a₀ − i a₁))

for a₀, a₁, a₂, a₃ ∈ Z such that a₀² + a₁² + a₂² + a₃² = p, a₀ is odd and positive, and a₁, a₂, a₃ are even, for some fixed prime p ≠ q such that p ≡ 1 mod 4, q is a square modulo p, and i ∈ F_q such that i² = −1 mod q.

<a id="pdf-bf2ce5422088-p107-b005"></a>
<!-- pdf-source: page=107; block=5; confidence=0.99 -->
The degree of the graph is the number of solutions to the equation a₀² + a₁² + a₂² + a₃² = p, which turns out to be D = p + 1, and it has λ(G) ≤ 2√(D − 1)/D, so it is an optimal spectral expander. (See Theorems 4.11 and 4.12, and note that this bound is even better than we know for random graphs, which have an additive O(1) term in the

<a id="pdf-bf2ce5422088-p108-b001"></a>
<!-- pdf-source: page=108; block=1; confidence=0.83 -->
The source names these graphs for the number-theoretic input to their expansion proof, and extends the term to any infinite family with optimal expansion $\gamma\ge1-2\sqrt{D-1}/D$.

<a id="pdf-bf2ce5422088-p108-b002"></a>
<!-- pdf-source: page=108; block=2; confidence=1.00 -->
## 4.3.2 Graph Operations

<a id="pdf-bf2ce5422088-p108-b003"></a>
<!-- pdf-source: page=108; block=3; confidence=0.98 -->
The next construction starts from a constant-size expander and repeatedly applies graph operations to increase size while controlling degree and second eigenvalue. The text notes a later use in derandomizing undirected $S$-$T$ connectivity.

<a id="pdf-bf2ce5422088-p108-b004"></a>
<!-- pdf-source: page=108; block=4; confidence=0.99 -->
**Definition 4.28.** An $(N,D,\gamma)$-graph is a $D$-regular digraph on $N$ vertices with spectral expansion $\gamma$.

<a id="pdf-bf2ce5422088-p108-b005"></a>
<!-- pdf-source: page=108; block=5; confidence=1.00 -->
## 4.3.2.1 Squaring

<a id="pdf-bf2ce5422088-p108-b006"></a>
<!-- pdf-source: page=108; block=6; confidence=0.99 -->
**Definition 4.29.** For a $D$-regular digraph $G=(V,E)$, define $G^2=(V,E')$ to be $D^2$-regular on the same vertices, where the $(i,j)$-neighbor of $x$ is the $j$th neighbor of the $i$th neighbor of $x$. A random step in $G^2$ is equivalent to two random steps in $G$.

<a id="pdf-bf2ce5422088-p109-b001"></a>
<!-- pdf-source: page=109; block=1; confidence=0.99 -->
**Lemma 4.30.** If $G$ is an $(N,D,1-\lambda)$-graph, then $G^2$ is an $(N,D^2,1-\lambda^2)$-graph. Squaring preserves node count, squares the degree, and improves expansion from $\gamma=1-\lambda$ to $1-\lambda^2=2\gamma-\gamma^2$.

<a id="pdf-bf2ce5422088-p109-b002"></a>
<!-- pdf-source: page=109; block=2; confidence=0.99 -->
**Proof.** The claims about $N$ and $D$ follow from the definition of graph squaring. If $M$ is the random-walk matrix of $G$, then $M^2$ is that of $G^2$. For $x\perp u$, $\|xM^2\|\le\lambda\|xM\|\le\lambda^2\|x\|$.

<a id="pdf-bf2ce5422088-p109-b003"></a>
<!-- pdf-source: page=109; block=3; confidence=0.99 -->
Tensoring increases graph size while also increasing degree.

<a id="pdf-bf2ce5422088-p109-b004"></a>
<!-- pdf-source: page=109; block=4; confidence=0.99 -->
**Definition 4.31 (Tensor product of graphs).** For $D_1$-regular $G_1=(V_1,E_1)$ and $D_2$-regular $G_2=(V_2,E_2)$, define $G_1\otimes G_2$ on $V_1\times V_2$ with degree $D_1D_2$. The neighbor indexed by $(i_1,i_2)$ of $(x_1,x_2)$ is $(y_1,y_2)$, where $y_b$ is the $i_b$th neighbor of $x_b$ in $G_b$. A random step moves independently in each component.

<a id="pdf-bf2ce5422088-p109-b005"></a>
<!-- pdf-source: page=109; block=5; confidence=1.00 -->
**Definition 4.32 (Tensor Products of Vectors and Matrices).** Let x ∈ ℝ^{N₁}, y ∈ ℝ^{N₂}, then their tensor product is the vector z = x ⊗ y ∈ ℝ^{N₁N₂} where z_{ij} = x_i y_j.

<a id="pdf-bf2ce5422088-p110-b001"></a>
<!-- pdf-source: page=110; block=1; confidence=0.99 -->
For $A=(a_{ii'})\in\mathbb R^{N_1\times N_1}$ and $B=(b_{jj'})\in\mathbb R^{N_2\times N_2}$, their tensor product is $A\otimes B=(c_{ij,i'j'})\in\mathbb R^{N_1N_2\times N_1N_2}$, with $c_{ij,i'j'}=a_{ii'}b_{jj'}$.

<a id="pdf-bf2ce5422088-p110-b002"></a>
<!-- pdf-source: page=110; block=2; confidence=0.98 -->
Tensor-graph steps are independent walks on the factors; tensor products of probability distributions describe independent component distributions. The identity $(x\otimes y)(A\otimes B)=(xA)\otimes(yB)$ holds, and $A\otimes B$ is uniquely characterized by it. Decomposable tensors span the full product space, though not every vector is decomposable. For the factor walk matrices, $M_1\otimes M_2=(I_{N_1}\otimes M_2)(M_1\otimes I_{N_2})=(M_1\otimes I_{N_2})(I_{N_1}\otimes M_2)$, so either component walk may be performed first.

<a id="pdf-bf2ce5422088-p110-b003"></a>
<!-- pdf-source: page=110; block=3; confidence=0.99 -->
**Lemma 4.33.** If $G_b$ is an $(N_b,D_b,\gamma_b)$-graph for $b=1,2$, then $G_1\otimes G_2$ is an $(N_1N_2,D_1D_2,\min\{\gamma_1,\gamma_2\})$-graph. For equal factors, node count increases, degree increases, and spectral expansion is unchanged.

<a id="pdf-bf2ce5422088-p111-b001"></a>
<!-- pdf-source: page=111; block=1; confidence=1.00 -->
**Proof.** As usual, we write γ₁ = 1 − λ₁, γ₂ = 1 − λ₂; then our goal is to show that G₁ ⊗ G₂ has spectral expansion 1 − max{λ₁, λ₂}. The intuition is as follows. We can think of the vertices of G₁ ⊗ G₂ as being partitioned into N₁ “clouds,” each consisting of N₂ vertices, where cloud v₁ contains all vertices of the form (v₁, ·). Thus, any probability distribution (V₁, V₂) on the vertices (v₁, v₂) of G₁ ⊗ G₂ can be thought of as picking a cloud v₁ according to the marginal distribution V₁ and then picking the vertex v₂ within the cloud v₁ according to the conditional distribution V₂|_{V₁=v₁}. If the overall distribution on pairs is far from uniform, then either (1) the marginal distribution V₁ on the clouds must be far from uniform, or (2) the conditional distributions V₂|_{V₁=v₁} within the clouds must be far from uniform. When we take a random step, the expansion of G₁ will bring us closer to uniform in Case 1 and the expansion of G₂ will bring us closer to uniform in Case 2. … Given any vector x ∈ ℝ^{N₁N₂} that is orthogonal to u_{N₁N₂}, we can decompose x as x = x^{∥} + x^{⊥}, where x^{∥} is a multiple of u_{N₂} on each cloud of size N₂ and x^{⊥} is orthogonal to u_{N₂} on each cloud. Note that x^{∥} = y ⊗ u_{N₂}, where y ∈ ℝ^{N₁} is orthogonal to u_{N₁} (because x^{∥} = x − x^{⊥} is orthogonal to u_{N₁N₂}).

<a id="pdf-bf2ce5422088-p111-b002"></a>
<!-- pdf-source: page=111; block=2; confidence=0.99 -->
For the cloud-constant component, $x_{\parallel}(M_1\otimes M_2)=(y\otimes u_{N_2})(M_1\otimes M_2)=(yM_1)\otimes u_{N_2}$.

<a id="pdf-bf2ce5422088-p112-b001"></a>
<!-- pdf-source: page=112; block=1; confidence=0.96 -->
For a decomposition \(x=x_{\parallel}+x_{\perp}\), the two components after applying \(M\) have norms at most \(\lambda_1\|x_{\parallel}\|\) and \(\lambda_2\|x_{\perp}\|\), respectively. They remain orthogonal, so \(\|xM\|^2\leq\max\{\lambda_1,\lambda_2\}^2(\|x_{\parallel}\|^2+\|x_{\perp}\|^2)=\max\{\lambda_1,\lambda_2\}^2\|x\|^2\).

<a id="pdf-bf2ce5422088-p112-b002"></a>
<!-- pdf-source: page=112; block=2; confidence=0.99 -->
Introduces the zig–zag product as an operation that reduces degree while retaining expansion; together with squaring and tensoring, it yields arbitrarily large expanders with constant degree and expansion.

<a id="pdf-bf2ce5422088-p113-b001"></a>
<!-- pdf-source: page=113; block=1; confidence=0.98 -->
**Definition 4.34.** For a \(D_1\)-regular digraph \(G\) on \(N_1\) vertices and a \(D_2\)-regular digraph \(H\) on \(D_1\) vertices, \(G\zigzag H\) has vertices \((u,i)\in[N_1]\times[D_1]\). Its \((a,b)\)-neighbor from \((u,i)\), for \(a,b\in[D_2]\), is found by: (1) taking the \(a\)-neighbor \(i'\) of \(i\) in \(H\); (2) following the \(i'\)-th outgoing edge \(e=(u,v)\) of \(u\) in \(G\), and letting \(j'\) be the index of that edge among edges entering \(v\); (3) taking the \(b\)-neighbor \(j\) of \(j'\) in \(H\). The construction depends on the numbering of outgoing and incoming edges of \(G\), so it is naturally an operation on labelled graphs.

<a id="pdf-bf2ce5422088-p114-b001"></a>
<!-- pdf-source: page=114; block=1; confidence=1.00 -->
**Theorem 4.35.** If G is a (N₁, D₁, γ₁)-graph, and H is a (D₁, D₂, γ₂)-graph then G ⊗̸ H is a (N₁D₁, D₂², γ = γ₁ · γ₂²)-graph. In particular, if γ₁ = 1 − λ₁ and γ₂ = 1 − λ₂, then γ = 1 − λ for λ ≤ λ₁ + 2λ₂.

<a id="pdf-bf2ce5422088-p114-b002"></a>
<!-- pdf-source: page=114; block=2; confidence=0.95 -->
The account separates distributions on vertex clouds into two cases: conditional distributions within clouds are nonuniform, so the first \(H\)-step improves them; or they are uniform, while the cloud marginal is nonuniform, so the \(G\)-step improves that marginal. The \(G\)-step is a permutation and does not itself move the joint distribution closer to uniform.

<a id="pdf-bf2ce5422088-p115-b001"></a>
<!-- pdf-source: page=115; block=1; confidence=0.97 -->
The vector decomposition separates a vector orthogonal to uniform into parts uniform within each cloud and parts orthogonal within each cloud; it yields sharper spectral bounds, though the parts need not stay orthogonal through zig–zag steps. Alternatively, view the inner expander as a perturbation of the complete graph: when it is complete, zig–zag equals tensor product. Matrix decomposition gives a simpler, slightly weaker analysis.

<a id="pdf-bf2ce5422088-p115-b002"></a>
<!-- pdf-source: page=115; block=2; confidence=0.97 -->
**Proof.** Let \(A,B,M\) be the random-walk matrices of \(G_1,G_2,G_1\zigzag G_2\). For the zig–zag steps, set \(\widetilde B=I_{N_1}\otimes B\), and let \(\widehat A\) be the permutation matrix of the \(G_1\)-step. Then \(M=\widetilde B\widehat A\widetilde B\). By Lemma 4.19, write \(B=\gamma_2J+(1-\gamma_2)E\), where \(J\) has every entry \(1/D_1\) and \(\|E\|\le 1\).

<a id="pdf-bf2ce5422088-p116-b001"></a>
<!-- pdf-source: page=116; block=1; confidence=0.99 -->
This gives M = (γ₂ J̃ + (1 − γ₂) Ẽ) Â (γ₂ J̃ + (1 − γ₂) Ẽ) = γ₂² J̃ Â J̃ + (1 − γ₂²)F, where we take (1 − γ₂²)F to be the sum of the three terms involving Ẽ; noting that their norms sum to at most (1 − γ₂²), we see that F has norm at most 1. Now, the key observation is that J̃ Â J̃ = A ⊗ J. Thus, M = γ₂² · A ⊗ J + (1 − γ₂²)F, and thus λ(M) ≤ γ₂² · λ(A ⊗ J) + (1 − γ₂²) ≤ γ₂² · (1 − γ₁) + (1 − γ₂²) = 1 − γ₁γ₂², as desired.

<a id="pdf-bf2ce5422088-p116-b002"></a>
<!-- pdf-source: page=116; block=2; confidence=0.99 -->
This section constructs expander families using graph operations.

<a id="pdf-bf2ce5422088-p116-b003"></a>
<!-- pdf-source: page=116; block=3; confidence=0.99 -->
An initial family uses only graph squaring and the zig–zag product.

<a id="pdf-bf2ce5422088-p116-b004"></a>
<!-- pdf-source: page=116; block=4; confidence=0.98 -->
**Construction 4.36.** Given a \((D^4,D,7/8)\)-graph \(H\), define \(G_1=H^2\) and \(G_{t+1}=G_t^2\zigzag H\).

<a id="pdf-bf2ce5422088-p116-b005"></a>
<!-- pdf-source: page=116; block=5; confidence=0.99 -->
**Proposition 4.37.** For every \(t\), \(G_t\) is a \((D^{4t},D^2,1/2)\)-graph.

<a id="pdf-bf2ce5422088-p116-b006"></a>
<!-- pdf-source: page=116; block=6; confidence=0.98 -->
**Proof.** Proceed by induction on \(t\). In the base case, \(G_1=H^2\) is a \((D^4,D^2,1-\lambda_0^2)\)-graph by Lemma 4.30, and \(\lambda_0^2\le1/2\).

<a id="pdf-bf2ce5422088-p117-b001"></a>
<!-- pdf-source: page=117; block=1; confidence=0.98 -->
The product \(G_t^2\zigzag H\) is defined because \(\deg(G_t^2)=\deg(G_t)^2=(D^2)^2=\#\mathrm{nodes}(H)\). Its degree is \(D^2\), its number of nodes is \(N_tD^4=D^{4(t+1)}\), and its spectral parameter satisfies \(\lambda(G_{t+1})\le\lambda(G_t)^2+2\lambda(H)\le(1/2)^2+2(1/8)=1/2\).

<a id="pdf-bf2ce5422088-p117-b002"></a>
<!-- pdf-source: page=117; block=2; confidence=0.96 -->
Let \(\mathrm{time}(G_t)\) denote the time to evaluate its edge-rotation map. One evaluation for \(G_t\) uses two for \(G_{t-1}\), plus polynomial time in \(\log N_t\) for string manipulation. Hence \(\mathrm{time}(G_t)=2\mathrm{time}(G_{t-1})+\mathrm{poly}(\log N_t)=2^t\mathrm{poly}(\log N_t)=N_t^{\Theta(1)}\), since \(N_t=D^{4t}\). Thus this family is mildly explicit.

<a id="pdf-bf2ce5422088-p117-b003"></a>
<!-- pdf-source: page=117; block=3; confidence=0.99 -->
Tensoring is introduced so graph sizes grow faster while neighbor computation remains efficient.

<a id="pdf-bf2ce5422088-p117-b004"></a>
<!-- pdf-source: page=117; block=4; confidence=0.98 -->
**Construction 4.38.** For a \((D^8,D,7/8)\)-graph \(H\), define \(G_1=H^2\) and \(G_{t+1}=(G_t\otimes G_t)^2\zigzag H\).

<a id="pdf-bf2ce5422088-p117-b005"></a>
<!-- pdf-source: page=117; block=5; confidence=0.99 -->
In this family of graphs, the number of nodes grows doubly exponentially N_t ≈ c^{2^t}, while the computation time grows only exponentially as before. Namely, time(G_t) = 4^t · poly(log N_t) = poly(log N_t).

<a id="pdf-bf2ce5422088-p118-b001"></a>
<!-- pdf-source: page=118; block=1; confidence=1.00 -->
## 4.3 Explicit Constructions

<a id="pdf-bf2ce5422088-p118-b002"></a>
<!-- pdf-source: page=118; block=2; confidence=0.99 -->
Now \(N_t=D^{8t}\), so given a number \(N\), we can find a graph \(G_t\) in the family whose size is at most \(D^8\cdot N=O(N)\).

<a id="pdf-bf2ce5422088-p118-b003"></a>
<!-- pdf-source: page=118; block=3; confidence=0.98 -->
**Theorem 4.39.** There is a constant \(D\in\mathbb N\) such that for every \(t\in\mathbb N\), a fully explicit expander graph \(G_t\) exists with degree \(D\), spectral expansion \(1/2\), and \(N_t=D^{4t}\) nodes.

<a id="pdf-bf2ce5422088-p118-b004"></a>
<!-- pdf-source: page=118; block=4; confidence=1.00 -->
The result yields explicit expander-walk error reduction and averaging sampling.

<a id="pdf-bf2ce5422088-p118-b005"></a>
<!-- pdf-source: page=118; block=5; confidence=0.99 -->
**Corollary 4.40.** If language \(L\) has a BPP algorithm with error at most \(1/3\) using \(m(n)\) random bits on inputs of length \(n\), then for every polynomial \(k(n)\), it has a BPP algorithm with error at most \(2^{-k(n)}\) using \(m(n)+O(k(n))\) random bits.

<a id="pdf-bf2ce5422088-p118-b006"></a>
<!-- pdf-source: page=118; block=6; confidence=0.99 -->
**Corollary 4.41.** There is an explicit averaging sampler with the parameters of Theorem 4.23.

<a id="pdf-bf2ce5422088-p118-b007"></a>
<!-- pdf-source: page=118; block=7; confidence=1.00 -->
## 4.3.4 Open Problems

<a id="pdf-bf2ce5422088-p118-b008"></a>
<!-- pdf-source: page=118; block=8; confidence=0.96 -->
Spectral expanders from Theorem 4.39 are also vertex and edge expanders (Theorem 4.6, Corollary 4.10, and Theorem 4.14), but these equivalences do not preserve optimality across expansion measures. Optimal spectral expanders (Ramanujan graphs) are known, though their constructions use deep number theory; the discussion continues on page 119.

<a id="pdf-bf2ce5422088-p119-b001"></a>
<!-- pdf-source: page=119; block=1; confidence=0.96 -->
The source characterizes the absence of a more elementary construction as reflecting a limitation in understanding expanders.

<a id="pdf-bf2ce5422088-p119-b002"></a>
<!-- pdf-source: page=119; block=2; confidence=0.99 -->
**Open Problem 4.42.** Give an explicit “combinatorial” construction of constant-degree expander graphs \(G\) with \(\lambda(G)\le 2\sqrt{D-1}/D\) (or even \(\lambda(G)=O(1/\sqrt D)\)), where \(D\) is the degree.

<a id="pdf-bf2ce5422088-p119-b003"></a>
<!-- pdf-source: page=119; block=3; confidence=0.97 -->
Bipartite or directed expanders with constant left- or out-degree \(D\) and expansion \((1-\varepsilon)D\) are known for arbitrarily small constant \(\varepsilon\) (Section 6). Reaching optimal expansion \(D-O(1)\) (Theorem 4.4), or high expansion for undirected vertex expanders, remains open.

<a id="pdf-bf2ce5422088-p119-b004"></a>
<!-- pdf-source: page=119; block=4; confidence=0.97 -->
**Open Problem 4.43.** For arbitrarily large constant \(D\), explicitly construct balanced bipartite \((\Omega(N),D-c)\) vertex expanders, with \(N\) vertices on each side and left degree \(D\), where \(c\) is a universal constant independent of \(D\).

<a id="pdf-bf2ce5422088-p119-b005"></a>
<!-- pdf-source: page=119; block=5; confidence=0.97 -->
**Open Problem 4.44.** For arbitrarily small constant \(\varepsilon>0\), explicitly construct undirected \((\Omega(N),(1-\varepsilon)D)\) vertex expanders with \(N\) vertices and constant degree \(D\) depending only on \(\varepsilon\).

<a id="pdf-bf2ce5422088-p119-b006"></a>
<!-- pdf-source: page=119; block=6; confidence=0.99 -->
Although Problem 4.43 concerns balanced bipartite graphs, the imbalanced case is also important; related references include Problems 4.10 and 5.5 and Open Problems 5.36 and 6.35.

<a id="pdf-bf2ce5422088-p119-b007"></a>
<!-- pdf-source: page=119; block=7; confidence=1.00 -->
## 4.4 Undirected S-T Connectivity in Deterministic Logspace

<a id="pdf-bf2ce5422088-p119-b008"></a>
<!-- pdf-source: page=119; block=8; confidence=0.99 -->
Given an undirected graph \(G\) and vertices \(s,t\), decide whether an \(s\)-to-\(t\) path exists. It is solvable in randomized logspace (RL); the section develops a deterministic logspace (L) solution using expanders.

<a id="pdf-bf2ce5422088-p120-b001"></a>
<!-- pdf-source: page=120; block=1; confidence=1.00 -->
## 4.4 Undirected S-T Connectivity in Deterministic Logspace

<a id="pdf-bf2ce5422088-p120-b002"></a>
<!-- pdf-source: page=120; block=2; confidence=0.95 -->
On constant-degree expander components, connectivity can be tested in logspace by enumerating paths of length \(O(\log N)\), since such graphs have logarithmic diameter. Expander-building operations can transform an input graph to improve expansion by squaring while retaining degree through zig–zag and avoiding tensoring to keep size polynomial.

<a id="pdf-bf2ce5422088-p120-b003"></a>
<!-- pdf-source: page=120; block=3; confidence=0.99 -->
**Algorithm 4.45 (Undirected S-T Connectivity in L).** Input: An undirected graph \(G\) with \(N\) edges and vertices \(s,t\).

(1) Let \(H\) be a fixed \((D^4,D,3/4)\) graph for some constant \(D\).

(2) Reduce \((G,s,t)\) to \((G_0,s_0,t_0)\), where \(G_0\) is a \(D^2\)-regular graph in which every connected component is nonbipartite and \(s_0\) and \(t_0\) are connected in \(G_0\) iff \(s\) and \(t\) are connected in \(G\).

(3) For \(k=1,\ldots,\ell=O(\log N)\), define:

(a) Let \(G_k=G_{k-1}^2\mathbin{\textcircled{z}}H\).

(b) Let \(s_k\) and \(t_k\) be any two vertices in the “clouds” of \(G_k\) corresponding to \(s_{k-1}\) and \(t_{k-1}\), respectively.

<a id="pdf-bf2ce5422088-p121-b001"></a>
<!-- pdf-source: page=121; block=1; confidence=0.99 -->
Test all paths of length $O(\log N)$ in $G'$ starting at $s'$; accept if any visits $t'$.

<a id="pdf-bf2ce5422088-p121-b002"></a>
<!-- pdf-source: page=121; block=2; confidence=0.98 -->
Let $C_k$ be the component of $G_k$ containing $s_k$. Connectivity of $s_k,t_k$ implies connectivity of $s_{k-1},t_{k-1}$. Starting from connected, undirected, nonbipartite $C_0$, Theorem 2.53 gives $\gamma(C_0)\ge 1/\operatorname{poly}(N)$.

<a id="pdf-bf2ce5422088-p121-b003"></a>
<!-- pdf-source: page=121; block=3; confidence=0.97 -->
By Lemma 4.30, we have
\[
\gamma(C_{k-1}^2)\ge 2\cdot\gamma(C_{k-1})\cdot(1-\gamma(C_{k-1})/2)\approx 2\gamma(C_{k-1})
\]
for small \(\gamma(C_{k-1})\). By Theorem 4.35, we have
\[
\gamma(C_{k-1}^2\mathbin{\textcircled{z}}H)\ge \gamma(H)^2\cdot\gamma(C_{k-1}^2)
\]
\[
\ge (3/4)^2\cdot 2\cdot\gamma(C_{k-1})\cdot(1-\gamma(C_{k-1})/2)
\]
\[
\ge \min\{(35/32)\cdot\gamma(C_{k-1}),1/18\}.
\]
In particular, \(C_{k-1}^2\mathbin{\textcircled{z}}H\) is connected, so we have \(C_k=C_{k-1}^2\mathbin{\textcircled{z}}H\) and
\[
\gamma(C_k)\ge \min\{(35/32)\cdot\gamma(C_{k-1}),1/18\}.
\]

<a id="pdf-bf2ce5422088-p121-b004"></a>
<!-- pdf-source: page=121; block=4; confidence=0.96 -->
After $\ell=O(\log N)$ iterations, $\gamma(C_\ell)\ge 1/18$. Also $N_\ell\le N_0(D^4)^\ell=\operatorname{poly}(N)$, so paths of length $O(\log N)$ in $G_\ell$ suffice to decide $s$–$t$ connectivity.

<a id="pdf-bf2ce5422088-p122-b001"></a>
<!-- pdf-source: page=122; block=1; confidence=0.98 -->
To establish logarithmic-space implementation, show each edge-rotation map for $G_k$ can be computed using $O(1)$ more space than for $G_{k-1}$. The proof fixes a multitape Turing-machine model because the claim concerns constant additive space.

<a id="pdf-bf2ce5422088-p122-b002"></a>
<!-- pdf-source: page=122; block=2; confidence=0.96 -->
Define $\operatorname{space}(G_k)$ as workspace for computing its edge-rotation map on a multitape Turing machine. Input: tape 1 holds read-only $G$ with head at its left end; tape 2 holds $(v,i)$, where $v$ is a vertex of $G_i$ and $i\in[D^2]$, with head at the right end of the index; other tape contents may be present. Further work tapes start blank with heads at their left ends. Output: restore tape 1's head to the left end; replace $(v,i)$ on tape 2 by $(w,j)$, where $w$ is the $i$th neighbor of $v$ and $v$ is the $j$th neighbor of $w$, leaving all other tape-2 contents unchanged and the head at the right end of $j$; restore all work tapes to blank with heads at their left ends.

<a id="pdf-bf2ce5422088-p123-b001"></a>
<!-- pdf-source: page=123; block=1; confidence=0.92 -->
Under these conventions, $\operatorname{space}(G_0)=O(\log N)$ and $\operatorname{space}(G_k)=\operatorname{space}(G_{k-1})+O(1)$. First, computing the rotation map of $G_{k-1}^2$ uses $\operatorname{space}(G_{k-1})+O(1)$: for input $(v,(i_1,i_2))$, apply the prior rotation on $(v,i_1)$, swap the resulting $j_1$ with $i_2$, apply it again, then position the head at $j_1$. For $G_{k-1}^2\mathbin{\text{\textcircled{z}}}H$, the rotation uses two constant-size rotations for $H$ and one rotation for $G_{k-1}^2$.

<a id="pdf-bf2ce5422088-p123-b002"></a>
<!-- pdf-source: page=123; block=2; confidence=1.00 -->
**Theorem 4.46.** Undirected S-T Connectivity is in $L$.

<a id="pdf-bf2ce5422088-p123-b003"></a>
<!-- pdf-source: page=123; block=3; confidence=0.98 -->
The general equality $RL=L$ remains open; the stated best deterministic simulation is essentially $L^{3/2}=\operatorname{DSPACE}(\log^{3/2} n)$.

<a id="pdf-bf2ce5422088-p123-b004"></a>
<!-- pdf-source: page=123; block=4; confidence=0.99 -->
**Open Problem 4.47.** Show that $RL\subseteq L^c$ for some constant $c<3/2$.

<a id="pdf-bf2ce5422088-p123-b005"></a>
<!-- pdf-source: page=123; block=5; confidence=0.99 -->
Another open problem is the construction of *universal traversal sequences* — fixed walks of polynomial length that are guaranteed to

<a id="pdf-bf2ce5422088-p124-b001"></a>
<!-- pdf-source: page=124; block=1; confidence=0.99 -->
**Open Problem 4.48 (Open Problem 3.9, restated).** Construct explicit polynomial-length universal traversal sequences for arbitrarily labelled undirected graphs, or even arbitrarily labelled complete graphs.

<a id="pdf-bf2ce5422088-p124-b002"></a>
<!-- pdf-source: page=124; block=2; confidence=0.98 -->
For pseudorandom walk generators, handling general labellings appears to be the main obstacle to extending Theorem 4.46 toward proving RL = L.

<a id="pdf-bf2ce5422088-p124-b003"></a>
<!-- pdf-source: page=124; block=3; confidence=1.00 -->
## 4.5 Exercises

<a id="pdf-bf2ce5422088-p124-b004"></a>
<!-- pdf-source: page=124; block=4; confidence=0.98 -->
**Problem 4.1 (Bipartite Versus Nonbipartite Expanders).** Show that explicit constructions of either (i) D-regular (αN, A) expanders on N vertices for infinitely many N, with constants α > 0, A > 1, D independent of N, or (ii) D-regular-on-both-sides (αN, A) bipartite expanders with N vertices on each side for infinitely many N, can be transformed into explicit constructions of the other type; the transformation need not preserve the constants.

<a id="pdf-bf2ce5422088-p125-b001"></a>
<!-- pdf-source: page=125; block=1; confidence=0.99 -->
**Problem 4.2 (More Combinatorial Consequences of Spectral Expansion).** For a graph G on N vertices with spectral expansion γ = 1 − λ, prove the following:

<a id="pdf-bf2ce5422088-p125-b002"></a>
<!-- pdf-source: page=125; block=2; confidence=0.96 -->
(1) The independence number satisfies α(G) ≤ [λ/(1 + λ)]N. (2) The chromatic number satisfies χ(G) ≥ (1 + λ)/λ. (3) The diameter is O(log_{1/λ} N). Here an independent set contains no edge with both endpoints in the set, and χ(G) is the least number of colors in a proper vertex coloring.

<a id="pdf-bf2ce5422088-p125-b003"></a>
<!-- pdf-source: page=125; block=3; confidence=0.97 -->
The bounds give efficiently computable nontrivial estimates for α(G) and χ(G) on expanders, although computing these parameters exactly is NP-complete.

<a id="pdf-bf2ce5422088-p125-b004"></a>
<!-- pdf-source: page=125; block=4; confidence=0.94 -->
**Problem 4.3 (Limits on Vertex Expansion).** Relate expansion of a D-regular graph to that of the infinite D-regular tree T_D, whose vertices have one parent and D − 1 children; the tree is presented as an extremal comparison graph.

<a id="pdf-bf2ce5422088-p125-b005"></a>
<!-- pdf-source: page=125; block=5; confidence=0.98 -->
(1) If a D-regular digraph G is a (K, A) expander, show T_D is also a (K, A) expander. (2) For every D ∈ ℕ, infinitely many K ∈ ℕ satisfy that T_D is not a (K, D − 1 + 2/K) expander. (3) Deduce that for fixed D ∈ ℕ and α > 0, any D-regular N-vertex digraph that is an (αN, A) vertex expander has A ≤ D − 1 + O(1), where the O(1) term tends to zero as N → ∞ with D, α fixed.

<a id="pdf-bf2ce5422088-p126-b001"></a>
<!-- pdf-source: page=126; block=1; confidence=0.99 -->
**Problem 4.4 (Limits on Spectral Expansion).** Let \(G\) be a \(D\)-regular undirected graph and \(T_D\) be the infinite \(D\)-regular tree (as in Problem 4.3). For a graph \(H\) and \(\ell\in\mathbb N\), let \(p_\ell(H)\) denote the probability that if we choose a random vertex \(v\) in \(H\) and do a random walk of length \(2\ell\), we end back at vertex \(v\).

<a id="pdf-bf2ce5422088-p126-b002"></a>
<!-- pdf-source: page=126; block=2; confidence=0.99 -->
(1) Show that \(p_\ell(G)\ge p_\ell(T_D)\ge C_\ell\cdot(D-1)^\ell/D^{2\ell}\), where \(C_\ell\) is the \(\ell\)th Catalan number, which equals the number of properly parenthesized strings in \(\{(, )\}^{2\ell}\)—strings where no prefix has more )s than (s.

(2) Show that \(N\cdot p_\ell(G)\le 1+(N-1)\cdot\lambda(G)^{2\ell}\). (Hint: use the fact that the trace of a matrix equals the sum of its eigenvalues.)

(3) Using the fact that \(C_\ell=\binom{2\ell}{\ell}/(\ell+1)\), prove that
\[
\lambda(G)\ge \frac{2\sqrt{D-1}}{D}-O(1),
\]
where the \(O(1)\) term vanishes as \(N\to\infty\) (and \(D\) is held constant).

<a id="pdf-bf2ce5422088-p126-b003"></a>
<!-- pdf-source: page=126; block=3; confidence=0.99 -->
**Problem 4.5 (Near-Optimal Sampling).**

<a id="pdf-bf2ce5422088-p126-b004"></a>
<!-- pdf-source: page=126; block=4; confidence=0.99 -->
**Problem 4.5 (Near-Optimal Sampling).**

(1) Describe an algorithm for Sampling that tosses \(O(m+\log(1/\varepsilon)+\log(1/\delta))\) coins, makes \(O((1/\varepsilon^2)\cdot\log(1/\delta))\) queries to a function \(f:\{0,1\}^m\to[0,1]\), and estimates \(\mu(f)\) to within \(\pm\varepsilon\) with probability at least \(1-\delta\). (Hint: use expander walks to generate several sequences of coin tosses for the pairwise-independent averaging sampler, and compute the answer via a “median of averages.”)

(2) Give an explicit \((\delta,\varepsilon)\) hitting sampler \(\operatorname{Samp}:\{0,1\}^n\to(\{0,1\}^m)^t\) that tosses \(n=O(m+\log(1/\varepsilon)+\log(1/\delta))\) coins and generates \(t=O((1/\varepsilon)\cdot\log(1/\delta))\) samples.

<a id="pdf-bf2ce5422088-p127-b001"></a>
<!-- pdf-source: page=127; block=1; confidence=0.98 -->
The preceding bounds on randomness and query/sample complexity are optimal up to constant factors for most relevant parameter choices.

<a id="pdf-bf2ce5422088-p127-b002"></a>
<!-- pdf-source: page=127; block=2; confidence=0.99 -->
**Problem 4.6.** Show that any BPP algorithm with constant error can be converted to one with error at most $1/n$ using exactly the same number of random bits.

<a id="pdf-bf2ce5422088-p127-b003"></a>
<!-- pdf-source: page=127; block=3; confidence=0.95 -->
**Problem 4.7.** Prove the equivalence between hitting samplers and vertex expanders whose expansion condition is required only for left sets of size exactly $K$. Such a graph is called a $(=K,A)$ vertex expander; see Definition 5.32.

<a id="pdf-bf2ce5422088-p127-b004"></a>
<!-- pdf-source: page=127; block=4; confidence=0.99 -->
Given a bipartite multigraph with neighbor map $\Gamma:[N]\times[D]\to[M]$, define $\operatorname{Samp}(x)_y=\Gamma(x,y)$. Conversely, every such sampler determines a bipartite multigraph.

<a id="pdf-bf2ce5422088-p127-b005"></a>
<!-- pdf-source: page=127; block=5; confidence=0.99 -->
Prove that \(\operatorname{Samp}\) is a \((\delta,\varepsilon)\) hitting sampler if and only if \(\Gamma\) is a \((=K,A)\) vertex expander for \(K=\lfloor\delta N\rfloor+1\) and \(A=(1-\varepsilon)M/K\).

<a id="pdf-bf2ce5422088-p127-b006"></a>
<!-- pdf-source: page=127; block=6; confidence=0.99 -->
**Problem 4.8.**

<a id="pdf-bf2ce5422088-p127-b007"></a>
<!-- pdf-source: page=127; block=7; confidence=0.75 -->
(1) For a finite field $F$, define a graph on $F^2$ by connecting $(a,b)$ to $(c,d)$ when $ac=b+d$, equivalently when $(c,d)$ lies on the line $y=ax-b$. Prove that the graph is $|F|$-regular and has $\lambda(G)\le 1/\sqrt{|F|}$; the hint is to consider $G^2$.

<a id="pdf-bf2ce5422088-p128-b001"></a>
<!-- pdf-source: page=128; block=1; confidence=0.99 -->
**Problem 4.8 (A “Constant-Sized” Expander).**

<a id="pdf-bf2ce5422088-p128-b002"></a>
<!-- pdf-source: page=128; block=2; confidence=0.94 -->
(2) Show that for sufficiently large, but constant, $|F|$, suitable operations on the graph from part (1) produce a base graph for the Section 4.3.3 expander construction: a $(D^8,D,7/8)$ graph for some constant $D$.

<a id="pdf-bf2ce5422088-p128-b003"></a>
<!-- pdf-source: page=128; block=3; confidence=1.00 -->
**Problem 4.9.**

<a id="pdf-bf2ce5422088-p128-b004"></a>
<!-- pdf-source: page=128; block=4; confidence=0.99 -->
**Problem 4.9 (The Replacement Product).** Given a \(D_1\)-regular graph \(G_1\) on \(N_1\) vertices and a \(D_2\)-regular graph \(G_2\) on \(D_1\) vertices, consider the following graph \(G_1\mathbin{\textcircled{r}}G_2\) on vertex set \([N_1]\times[D_1]\): vertex \((u,i)\) is connected to \((v,j)\) iff (a) \(u=v\) and \((i,j)\) is an edge in \(G_2\), or (b) \(v\) is the \(i\)th neighbor of \(u\) in \(G_1\) and \(u\) is the \(j\)th neighbor of \(v\).

<a id="pdf-bf2ce5422088-p128-b005"></a>
<!-- pdf-source: page=128; block=5; confidence=0.99 -->
(1) Prove that there is a function \(g\) such that if \(G_1\) has spectral expansion \(\gamma_1>0\) and \(G_2\) has spectral expansion \(\gamma_2>0\) (and both graphs are undirected), then \(G_1\mathbin{\textcircled{r}}G_2\) has spectral expansion \(g(\gamma_1,\gamma_2,D_2)>0\). (Hint: Note that \((G_1\mathbin{\textcircled{r}}G_2)^3\) has \(G_1\mathbin{\textcircled{z}}G_2\) as a subgraph.)

<a id="pdf-bf2ce5422088-p128-b006"></a>
<!-- pdf-source: page=128; block=6; confidence=0.99 -->
(2) Show how an explicit construction of constant-degree spectral expanders yields an explicit construction of degree-three spectral expanders.

<a id="pdf-bf2ce5422088-p128-b007"></a>
<!-- pdf-source: page=128; block=7; confidence=0.99 -->
(3) Without using Theorem 4.14, prove an analogue of Part 1 for edge expansion. That is, there is a function \(h\) such that if \(G_1\) is an \((N_1/2,\varepsilon_1)\) edge expander and \(G_2\) is a \((D_1/2,\varepsilon_2)\) edge expander, then \(G_1\mathbin{\textcircled{r}}G_2\) is an \((N_1D_1/2,h(\varepsilon_1,\varepsilon_2,D_2))\) edge expander, where \(h(\varepsilon_1,\varepsilon_2,D_2)>0\) if \(\varepsilon_1,\varepsilon_2>0\). (Hint: given any set \(S\) of vertices of \(G_1\mathbin{\textcircled{r}}G_2\), partition \(S\) into the clouds that are more than “half-full” and those that are not.)

<a id="pdf-bf2ce5422088-p128-b008"></a>
<!-- pdf-source: page=128; block=8; confidence=0.87 -->
(4) Show that $g$ and $h$ must depend on $D_2$: for $N_1\ge2$, the replacement product cannot be an $(N_1D_1/2,\varepsilon)$ edge expander when $\varepsilon>1/(D_2+1)$.

<a id="pdf-bf2ce5422088-p129-b001"></a>
<!-- pdf-source: page=129; block=1; confidence=0.98 -->
**Problem 4.10.** Let $G$ be a $(K,(1-\varepsilon)D)$ bipartite vertex expander with $N$ left vertices, $M$ right vertices, and left degree $D$.

<a id="pdf-bf2ce5422088-p129-b002"></a>
<!-- pdf-source: page=129; block=2; confidence=0.99 -->
(1) For a set $S$ of left vertices, a $y\in N(S)$ is called a unique neighbor of $S$ if $y$ is incident to exactly one edge from $S$. Prove that every left-set $S$ of size at most $K$ has at least $(1-2\varepsilon)D|S|$ unique neighbors.

<a id="pdf-bf2ce5422088-p129-b003"></a>
<!-- pdf-source: page=129; block=3; confidence=0.97 -->
(2) For $|S|\le K/2$, prove that at most $|S|/2$ vertices outside $S$ have at least $\delta D$ neighbors in $N(S)$, where $\delta=O(\varepsilon)$.

<a id="pdf-bf2ce5422088-p129-b004"></a>
<!-- pdf-source: page=129; block=4; confidence=0.95 -->
The proposed data structure stores $M$ bits, one per right vertex of the expander, and aims to test membership in a small subset $S\subseteq[N]$ by probing one bit. This is compared with the $N$-bit characteristic vector and hash-based storage using $O(|S|)$ words of $O(\log N)$ bits, which requires reading a whole word.

<a id="pdf-bf2ce5422088-p129-b005"></a>
<!-- pdf-source: page=129; block=5; confidence=0.99 -->
**Property $\Pi$.** For every left vertex $x$, all but a $\delta=O(\varepsilon)$ fraction of its neighbors are assigned $\chi_S(x)$, where $\chi_S(x)=1$ iff $x\in S$.

<a id="pdf-bf2ce5422088-p129-b006"></a>
<!-- pdf-source: page=129; block=6; confidence=0.99 -->
(3) Show that any assignment satisfying Property $\Pi$ permits a randomized membership test for $S$ with error probability $\delta$ using one data-structure bit.

<a id="pdf-bf2ce5422088-p129-b007"></a>
<!-- pdf-source: page=129; block=7; confidence=0.98 -->
(4) Show that an assignment satisfying Property $\Pi$ exists when $|S|\le K/2$. Hint: initially assign 1 to all neighbors of $S$ and 0 to all other right vertices, then correct the resulting errors.

<a id="pdf-bf2ce5422088-p129-b008"></a>
<!-- pdf-source: page=129; block=8; confidence=0.95 -->
The text states that suitable expanders exist with $M=O(K\log N)$ for constant $\varepsilon$, yielding a data-structure size of the same order; the sentence continues beyond the supplied page.

<a id="pdf-bf2ce5422088-p130-b001"></a>
<!-- pdf-source: page=130; block=1; confidence=0.99 -->
The hashing-based data structures mentioned in Section 3.5.3 only require storing $O(|S|)$ words, each of $O(\log N)$ bits, but testing membership requires reading an entire word (rather than just one bit). Our data structure will consist of $M$ bits, which we think of as a $\{0,1\}$-assignment to the right vertices of our expander. This assignment will have the following property. ... It turns out that the needed expanders exist with $M=O(K\log N)$ (for any constant $\varepsilon$), so the size of this data structure matches the hashing-based scheme while admitting (randomized) 1-bit probes. However, note that such bipartite vertex expanders do not follow from explicit spectral expanders as given in Theorem 4.39, because the latter do not provide vertex expansion beyond $D/2$ nor do they yield highly imbalanced expanders (with $M\ll N$) as needed here. But in Section 5, we will see how to explicitly construct expanders that are quite good for this application (specifically, with $M=K^{1.01}\cdot\operatorname{polylog}N$).

<a id="pdf-bf2ce5422088-p130-b002"></a>
<!-- pdf-source: page=130; block=2; confidence=1.00 -->
## 4.6 Chapter Notes and References

<a id="pdf-bf2ce5422088-p130-b003"></a>
<!-- pdf-source: page=130; block=3; confidence=0.98 -->
The notes point to surveys of expander graphs and their applications. Early work established expansion in random graphs and concentrators; later applications included circuit lower bounds, logarithmic-depth sorting networks, derandomization, and Dinur’s proof of the PCP Theorem.

<a id="pdf-bf2ce5422088-p130-b004"></a>
<!-- pdf-source: page=130; block=4; confidence=0.98 -->
Spectral expansion implies vertex expansion (Tanner) and edge expansion (Alon–Milman). Converse results, analogous to Cheeger inequalities, relate vertex expansion to spectral expansion and edge expansion to spectral expansion or conductance, including for reversible and nonreversible Markov chains.

<a id="pdf-bf2ce5422088-p131-b001"></a>
<!-- pdf-source: page=131; block=1; confidence=0.98 -->
Theorem 4.11 gives the Alon–Boppana upper bound on spectral expansion; Theorem 4.12 says random graphs are asymptotically Ramanujan. Kahale showed that Ramanujan graphs have vertex expansion roughly $D/2$ on small sets.

<a id="pdf-bf2ce5422088-p131-b002"></a>
<!-- pdf-source: page=131; block=2; confidence=0.99 -->
Forms of the Expander Mixing Lemma trace to Alon and Chung, who considered edges between $S$ and $V\setminus S$. The converse stated as Theorem 4.16 is due to Bilu and Linial; references also cover quasirandomness in dense and sparse graphs.

<a id="pdf-bf2ce5422088-p131-b003"></a>
<!-- pdf-source: page=131; block=3; confidence=0.97 -->
Theorem 4.17’s hitting bound is due to Kahale, and the expander-walk Chernoff bound (Theorem 4.22) to Gillman; the text’s proof follows Healy. The notes also attribute the RP error-reduction problem and its BPP generalization, the equivalence of hitting samplers with bipartite vertex expanders (Problem 4.7), sampling Problem 4.5 and its matching lower bounds, and Open Problem 4.24 to the cited authors.

<a id="pdf-bf2ce5422088-p131-b004"></a>
<!-- pdf-source: page=131; block=4; confidence=0.99 -->
Construction 4.25 is Margulis’s first explicit constant-degree expander construction; Gabber–Galil gave a simpler proof and a specific spectral bound. Construction 4.26 is a variant of the Lubotzky–Phillips–Sarnak construction. Ramanujan graphs in Construction 4.27 were independently constructed by Lubotzky–Phillips–Sarnak and Margulis.

<a id="pdf-bf2ce5422088-p132-b001"></a>
<!-- pdf-source: page=132; block=1; confidence=0.99 -->
Further references cover Ramanujan graphs and the mathematical tools used to analyze them.

<a id="pdf-bf2ce5422088-p132-b002"></a>
<!-- pdf-source: page=132; block=2; confidence=0.98 -->
The zig–zag product and Section 4.3.3 constructions are due to Reingold, Vadhan, and Wigderson; the analysis uses matrix decomposition (Lemma 4.19). Earlier expander constructions used tensor products. Problem 4.9 concerns the replacement product, which can substitute for zig–zag in the constructions and Algorithm 4.45; a Markov-chain decomposition theorem independently yields a better spectral-expansion bound for that product.

<a id="pdf-bf2ce5422088-p132-b003"></a>
<!-- pdf-source: page=132; block=3; confidence=0.99 -->
There has been substantial progress on giving a combinatorial construction of Ramanujan graphs (Open Problem 4.42). Bilu and Linial [68] give a mildly explicit construction achieving $\lambda(G)=\widetilde O(\sqrt D)$, Ben-Aroya and Ta-Shma [58] give a fully explicit construction achieving $\lambda(G)=D^{1/2+o(1)}$, and Batson, Spielman, and Srivastava [53] give a mildly explicit construction of a weighted graph achieving $\lambda(G)=O(\sqrt D)$.

<a id="pdf-bf2ce5422088-p132-b004"></a>
<!-- pdf-source: page=132; block=4; confidence=0.99 -->
Capalbo et al. constructed constant-degree bipartite expanders with expansion $(1-\varepsilon)D$, using a zig–zag variant for randomness condensers. Alon and Capalbo gave an explicit undirected constant-degree unique-neighbor expander, addressing Open Problem 4.44.

<a id="pdf-bf2ce5422088-p132-b005"></a>
<!-- pdf-source: page=132; block=5; confidence=0.98 -->
Reingold’s Algorithm 4.45 gives deterministic logspace undirected $S$–$T$ connectivity. Saks and Zhou proved $\mathrm{RL}\subseteq\mathrm{L}^{3/2}$, with Nisan’s space-bounded pseudorandom generator as a key ingredient. Reingold and subsequent work also give polynomial-length universal traversal sequences and pseudorandom walk generators for consistently labelled regular digraphs.

<a id="pdf-bf2ce5422088-p133-b001"></a>
<!-- pdf-source: page=133; block=1; confidence=0.95 -->
Nisan’s explicit universal traversal sequence has length and construction time $n^{O(\log n)}$ and space $O(\log^2 n)$. The text attributes related results to prior works.

<a id="pdf-bf2ce5422088-p134-b001"></a>
<!-- pdf-source: page=134; block=1; confidence=1.00 -->
# List-Decodable Codes

<a id="pdf-bf2ce5422088-p134-b002"></a>
<!-- pdf-source: page=134; block=2; confidence=0.99 -->
Coding theory studies reliable message recovery under channel corruption. Here codes are treated as pseudorandom objects, linking them with averaging samplers, expander graphs, randomness extractors, and pseudorandom generators.

<a id="pdf-bf2ce5422088-p134-b003"></a>
<!-- pdf-source: page=134; block=3; confidence=1.00 -->
## 5.1 Definitions and Existence

<a id="pdf-bf2ce5422088-p134-b004"></a>
<!-- pdf-source: page=134; block=4; confidence=1.00 -->
### 5.1.1 Definition

<a id="pdf-bf2ce5422088-p134-b005"></a>
<!-- pdf-source: page=134; block=5; confidence=0.99 -->
Restrict transmitted data to strings chosen from a set that remains distinguishable after corruption.

<a id="pdf-bf2ce5422088-p135-b001"></a>
<!-- pdf-source: page=135; block=1; confidence=0.99 -->
**Definition 5.1.** A $q$-ary code is a multiset $C\subseteq\Sigma^{\widehat n}$, where $\Sigma$ is an alphabet of size $q$. Elements of $C$ are called codewords. We define the following key parameters: $\widehat n$ is the block length; $n=\log|C|$ is the message length; and $\rho=n/(\widehat n\cdot\log|\Sigma|)$ is the (relative) rate of the code. An encoding function for $C$ is a bijective mapping $\mathrm{Enc}:\{1,\ldots,|C|\}\to C$. Given such an encoding function, we view the elements of $\{1,\ldots,|C|\}$ as messages. When $n=\log|C|$ is an integer, we often think of messages as strings in $\{0,1\}^n$.

<a id="pdf-bf2ce5422088-p135-b002"></a>
<!-- pdf-source: page=135; block=2; confidence=0.99 -->
The code emphasizes combinatorial properties; its encoding labels codewords for algorithmic use. The notation is chosen to support comparisons with other pseudorandom objects.

<a id="pdf-bf2ce5422088-p135-b003"></a>
<!-- pdf-source: page=135; block=3; confidence=0.99 -->
So far, we haven’t talked at all about the error-correcting properties of codes. Here we need to specify two things: the model of errors (as introduced by the noisy channel) and the notion of a successful recovery. For the errors, the main distinction is between random errors and worst-case errors. For random errors, one needs to specify a stochastic model of the channel. The most basic one is the binary symmetric channel (over alphabet $\Sigma=\{0,1\}$), where each bit is flipped independently with probability $\delta$.

<a id="pdf-bf2ce5422088-p136-b001"></a>
<!-- pdf-source: page=136; block=1; confidence=0.99 -->
Section on worst-case error correction and list decoding.

<a id="pdf-bf2ce5422088-p136-b002"></a>
<!-- pdf-source: page=136; block=2; confidence=0.99 -->
We will focus on worst-case errors, where we simply assume that fewer than a $\delta$ fraction of symbols have been changed. That is, when we send a codeword $c\in\Sigma^{\widehat n}$ over the channel, the received word $r\in\Sigma^{\widehat n}$ differs from $c$ in fewer than $\delta\widehat n$ places.

<a id="pdf-bf2ce5422088-p136-b003"></a>
<!-- pdf-source: page=136; block=3; confidence=0.96 -->
**Definition 5.2.** For strings \(x,y\in\Sigma^n\), relative Hamming distance is \(d_H(x,y)=\Pr_i[x_i\ne y_i]\), and agreement is \(\operatorname{agr}(x,y)=1-d_H(x,y)\). The open Hamming ball \(B(x,\delta)=\{y\in\Sigma^n:d_H(x,y)<\delta\}\).

<a id="pdf-bf2ce5422088-p136-b004"></a>
<!-- pdf-source: page=136; block=4; confidence=0.93 -->
**Definition 5.3.** For \(\operatorname{Enc}:\{0,1\}^n\to\Sigma^N\), a \(\delta\)-decoder \(\operatorname{Dec}:\Sigma^N\to\{0,1\}^n\) satisfies \(\operatorname{Dec}(r)=m\) whenever \(d_H(\operatorname{Enc}(m),r)<\delta\); then the code is \(\delta\)-decodable. A \((\delta,L)\)-list decoder maps \(r\) to a list of at most \(L\) messages and must include every \(m\) with \(d_H(\operatorname{Enc}(m),r)<\delta\); then the code is \((\delta,L)\)-list-decodable. Ordinary decoding is the case \(L=1\).

<a id="pdf-bf2ce5422088-p136-b005"></a>
<!-- pdf-source: page=136; block=5; confidence=0.94 -->
Without computational-efficiency constraints, decodability is determined by the codeword set.

<a id="pdf-bf2ce5422088-p137-b001"></a>
<!-- pdf-source: page=137; block=1; confidence=0.96 -->
**Definition 5.4.** The relative minimum distance of \(C\subseteq\Sigma^N\) is \(\min_{x\ne y\in C}d_H(x,y)\); if a word occurs with multiplicity greater than one, the distance is defined as zero.

<a id="pdf-bf2ce5422088-p137-b002"></a>
<!-- pdf-source: page=137; block=2; confidence=0.99 -->
**Proposition 5.5.** Let $C\subseteq\Sigma^{\widehat n}$ be a code with any encoding function $\mathrm{Enc}$. (1) For $\delta\widehat n\in\mathbb N$, $\mathrm{Enc}$ is $\delta$-decodable iff its minimum distance is at least $2\delta-1/\widehat n$. (2) $\mathrm{Enc}$ is $(\delta,L)$-list-decodable iff for every $r\in\Sigma^{\widehat n}$, $|B(r,\delta)\cap C|\le L$.

<a id="pdf-bf2ce5422088-p137-b003"></a>
<!-- pdf-source: page=137; block=3; confidence=0.95 -->
**Proof.** Item (2) follows from the definitions. Unique decoding is equivalent to no received word lying within distance \(<\delta\) of two codewords. If minimum distance is at least \(2\delta-1/N\), distinct codewords differ in at least \(2\delta N-1\) positions, so any received word must differ from one of them in at least \(\delta N\) positions. Conversely, if minimum distance is smaller, a pair differs in at most \(2\delta N-2\) positions; choose a received word differing from each in at most \(\delta N-1\) positions, contradicting uniqueness.

<a id="pdf-bf2ce5422088-p137-b004"></a>
<!-- pdf-source: page=137; block=4; confidence=0.97 -->
Unique decoding is limited to error fractions at most one half; list decoding can tolerate fractions approaching one with small lists.

<a id="pdf-bf2ce5422088-p137-b005"></a>
<!-- pdf-source: page=137; block=5; confidence=0.99 -->
A coding family aims to maximize correctable fraction and rate, minimize alphabet size and list size, and retain efficient encoding and decoding.

<a id="pdf-bf2ce5422088-p138-b001"></a>
<!-- pdf-source: page=138; block=1; confidence=0.99 -->
Existence bounds are obtained by the probabilistic method and expressed using q-ary entropy.

<a id="pdf-bf2ce5422088-p138-b002"></a>
<!-- pdf-source: page=138; block=2; confidence=0.99 -->
**Definition 5.6.** For $q,\widehat n\in\mathbb N$ and $\delta\in[0,1]$, we define $H_q(\delta,\widehat n)\in[0,1]$ to be such that $|B(x,\delta)|=q^{H_q(\delta,\widehat n)\cdot\widehat n}$ for $x\in\Sigma^{\widehat n}$, where $\Sigma$ is an alphabet of size $q$. We also define the $q$-ary entropy function $H_q(\delta)=\delta\cdot\log_q((q-1)/\delta)+(1-\delta)\cdot\log_q(1/(1-\delta))$.

<a id="pdf-bf2ce5422088-p138-b003"></a>
<!-- pdf-source: page=138; block=3; confidence=0.95 -->
**Proposition 5.7.** For every \(q\in\mathbb N\), \(\delta\in(0,1-1/q)\), and \(\varepsilon\in[0,1/2]\): (1) \(\lim_{N\to\infty}H_q(\delta,N)=H_q(\delta)\); (2) \(H_q(\delta)\le H_2(\delta)/\log q+\delta\); (3) \(H_2(1/2-\varepsilon)=1-\Theta(\varepsilon^2)\).

<a id="pdf-bf2ce5422088-p139-b001"></a>
<!-- pdf-source: page=139; block=1; confidence=1.00 -->
Introduces existence bounds for random error-correcting codes.

<a id="pdf-bf2ce5422088-p139-b002"></a>
<!-- pdf-source: page=139; block=2; confidence=0.99 -->
**Theorem 5.8.** (1) For all $\widehat n,q\in\mathbb N$ and $\delta\in(0,1-1/q)$, there exists a $q$-ary code of block length $\widehat n$, minimum distance at least $\delta$, and rate at least $\rho=1-H_q(\delta,\widehat n)$. (2) For all integers $\widehat n,q,L\in\mathbb N$ and $\delta\in(0,1-1/q)$, there exists a $(\delta,L)$-list-decodable $q$-ary code of block length $\widehat n$ and rate at least $\rho=1-H_q(\delta,\widehat n)-1/(L+1)$.

<a id="pdf-bf2ce5422088-p139-b003"></a>
<!-- pdf-source: page=139; block=3; confidence=0.98 -->
**Proof.** (1) Pick the codewords $c_1,\ldots,c_N$ in sequence, ensuring that $c_i$ is at distance at least $\delta$ from $c_1,\ldots,c_{i-1}$. The union of the Hamming balls of radius $\delta$ around $c_1,\ldots,c_{i-1}$ contains at most $(i-1)\cdot q^{H_q(\delta,\widehat n)\cdot\widehat n}< (N-1)\cdot q^{H_q(\delta,\widehat n)\cdot\widehat n}$, so there is always a choice of $c_i$ outside these balls if we take $N=\lfloor q^{(1-H_q(\delta,\widehat n))\cdot\widehat n}\rfloor$. (2) We use the probabilistic method. Choose the $N$ codewords randomly and independently from $\Sigma^{\widehat n}$. The probability that there is a Hamming ball of radius $\delta$ containing at least $L+1$ codewords is at most $q^{\widehat n}\cdot\binom{N}{L+1}\cdot\left(\frac{q^{H_q(\delta,\widehat n)\cdot\widehat n}}{q^{\widehat n}}\right)^{L+1}\leq\left(\frac{N-1}{q^{(1-H_q(\delta,\widehat n)-1/(L+1))\cdot\widehat n}}\right)^{L+1}$, which is less than $1$ if we take $N=\lfloor q^{(1-H_q(\delta,\widehat n)-1/(L+1))\cdot\widehat n}\rfloor$.

<a id="pdf-bf2ce5422088-p139-b004"></a>
<!-- pdf-source: page=139; block=4; confidence=0.82 -->
The minimum-distance and list-decoding existence bounds are comparable for large lists, but minimum distance guarantees unique decoding only to about half that radius; the text contrasts the tightness of the list-decoding bound with stronger algebraic-geometric minimum-distance constructions.

<a id="pdf-bf2ce5422088-p140-b001"></a>
<!-- pdf-source: page=140; block=1; confidence=0.92 -->
For binary codes near distance $1/2$, the stated rate scale is $\Theta(\varepsilon^2)$, with block length $\Theta(n/\varepsilon^2)$ and list size $\Theta(1/\varepsilon^2)$. For large $q$, the rate approaches $1-\delta$; at $\delta=1-\varepsilon$, rates near $\varepsilon$ are described, including rate $0.99\varepsilon$ with list size $O(1/\varepsilon)$ and alphabet size polynomial in $1/\varepsilon$, and generally rate $(1-\gamma)\varepsilon$ with $q=(1/\varepsilon)^{O(1/\gamma)}$.

<a id="pdf-bf2ce5422088-p140-b002"></a>
<!-- pdf-source: page=140; block=2; confidence=0.99 -->
**Open Problem 5.9.** For each fixed $\delta\in(0,1)$, determine the largest $\rho>0$ such that for every $\varepsilon>0$ there are infinitely many binary codes $C_{\hat n}\subseteq\{0,1\}^{\hat n}$ with rate at least $\rho-\varepsilon$ and minimum distance at least $\delta$.

<a id="pdf-bf2ce5422088-p140-b003"></a>
<!-- pdf-source: page=140; block=3; confidence=0.95 -->
Motivates the parameter regimes of interest and notes that minimum-distance bounds can be converted into list-decodability bounds.

<a id="pdf-bf2ce5422088-p140-b004"></a>
<!-- pdf-source: page=140; block=4; confidence=0.90 -->
**Proposition 5.10 (Johnson Bound).** (1) A code with minimum distance $1-\varepsilon$ is $(1-O(\sqrt{\varepsilon}),O(1/\varepsilon))$-list-decodable. (2) A binary code with minimum distance $1/2-\varepsilon$ is $(1/2-O(\sqrt{\varepsilon}),O(1/\varepsilon))$-list-decodable.

<a id="pdf-bf2ce5422088-p141-b001"></a>
<!-- pdf-source: page=141; block=1; confidence=0.99 -->
**Proof.** We prove Item 1 and leave Item 2 as an exercise in the next section (Problem 6.3). Suppose for contradiction that there are codewords $c_1,\ldots,c_s$ at distance less than $1-\varepsilon'$ from some $r\in\Sigma^{\hat n}$, for $\varepsilon'=2\sqrt{\varepsilon}$ and $s=\lceil 2/\varepsilon'\rceil$. Then
\[
1\ge \text{fraction of positions where }r\text{ agrees with some }c_i
\ge \sum_i \operatorname{agr}(r,c_i)-\sum_{1\le i<j\le s}\operatorname{agr}(c_i,c_j)
> s\varepsilon'-\binom{s}{2}\varepsilon
\ge 2-1=1,
\]
where the last inequality is by our setting of parameters. Hence, contradiction.

<a id="pdf-bf2ce5422088-p141-b002"></a>
<!-- pdf-source: page=141; block=2; confidence=0.91 -->
The conversion loses quadratically in the distance parameter, so optimal minimum-distance codes need not be optimal for list decoding; it can still yield near-maximal decoding radii when the exact rate-radius tradeoff is not required.

<a id="pdf-bf2ce5422088-p141-b003"></a>
<!-- pdf-source: page=141; block=3; confidence=0.99 -->
## 5.1.3 Explicit Codes

<a id="pdf-bf2ce5422088-p141-b004"></a>
<!-- pdf-source: page=141; block=4; confidence=0.99 -->
The section turns to computational efficiency, initially focusing on encoding.

<a id="pdf-bf2ce5422088-p141-b005"></a>
<!-- pdf-source: page=141; block=5; confidence=0.99 -->
**Definition 5.11.** A code $\mathrm{Enc}:\{0,1\}^n\to\Sigma^{\hat n}$ is fully explicit if, given a message $m\in\{0,1\}^n$ and index $i\in\hat n$, the symbol $\mathrm{Enc}(m)_i$ can be computed in time $\operatorname{poly}(n,\log\hat n,\log|\Sigma|)$.

<a id="pdf-bf2ce5422088-p141-b006"></a>
<!-- pdf-source: page=141; block=6; confidence=0.99 -->
Defining symbol-wise computation makes explicitness meaningful even when block length is superpolynomial in message length; weaker notions are also possible.

<a id="pdf-bf2ce5422088-p142-b001"></a>
<!-- pdf-source: page=142; block=1; confidence=1.00 -->
## 5.1 Definitions and Existence

<a id="pdf-bf2ce5422088-p142-b002"></a>
<!-- pdf-source: page=142; block=2; confidence=0.99 -->
The constructions use finite-field arithmetic; codewords may be viewed as functions from `[n̂]` to `Σ`. Explicit encoding requires computing the full codeword in time polynomial in `n̂` and `log |Σ|`.

<a id="pdf-bf2ce5422088-p142-b003"></a>
<!-- pdf-source: page=142; block=3; confidence=0.99 -->
**Construction 5.12 (Hadamard Code).** For `n ∈ ℕ`, the binary Hadamard code has blocklength `n̂ = 2^n` and consists of the linear functions `c : 𝔽₂ⁿ → 𝔽₂`.

<a id="pdf-bf2ce5422088-p142-b004"></a>
<!-- pdf-source: page=142; block=4; confidence=0.98 -->
**Proposition 5.13.** The Hadamard code is explicit under the encoding `m ↦ c_m`, where `m ∈ 𝔽₂ⁿ` and `c_m(x) = ∑ᵢ mᵢxᵢ mod 2`; its minimum distance is `1/2`; and for every `ε > 0` it is `(1/2 − ε, O(1/ε²))` list-decodable.

<a id="pdf-bf2ce5422088-p142-b005"></a>
<!-- pdf-source: page=142; block=5; confidence=0.98 -->
**Proof.** Encoding is explicit by inspection. Distinct linear functions `c,c′` agree on exactly half the inputs, since `c−c′` is a nonzero linear function. The list-decoding bound follows from the Johnson bound.

<a id="pdf-bf2ce5422088-p142-b006"></a>
<!-- pdf-source: page=142; block=6; confidence=0.99 -->
The Hadamard code has binary alphabet and optimal distance `1/2`, but rate `ρ = n/2ⁿ`; larger fields and degrees provide complementary parameters.

<a id="pdf-bf2ce5422088-p142-b007"></a>
<!-- pdf-source: page=142; block=7; confidence=0.99 -->
**Construction 5.14 (Reed–Solomon Codes).** For prime-power `q` and `d ∈ ℕ`, the `q`-ary Reed–Solomon code has blocklength `n̂ = q`, message length `n = (d+1) log q`, and consists of all polynomials `p : 𝔽_q → 𝔽_q` of degree at most `d`.

<a id="pdf-bf2ce5422088-p143-b001"></a>
<!-- pdf-source: page=143; block=1; confidence=0.99 -->
**Proposition 5.15.** The $q$-ary Reed–Solomon code of degree $d$:

1. is explicit with respect to the encoding function that takes a vector of coefficients $m\in\mathbb F_q^{d+1}$ to the polynomial $p_m$ defined by $p_m(x)=\sum_{i=0}^d m_i x^i$ (assuming we have a description of the field $\mathbb F_q$);
2. has minimum distance $\delta=1-d/q$; and
3. is $(1-O(\sqrt{d/q}),O(\sqrt{q/d}))$ list-decodable.

<a id="pdf-bf2ce5422088-p143-b002"></a>
<!-- pdf-source: page=143; block=2; confidence=0.99 -->
**Proof.** Encoding is explicit. Two distinct degree-at-most-`d` polynomials agree at no more than `d` points, giving the stated distance; list-decodability follows from the Johnson bound.

<a id="pdf-bf2ce5422088-p143-b003"></a>
<!-- pdf-source: page=143; block=3; confidence=0.91 -->
Taking `q = O(d)` gives constant rate and distance, with alphabet size `q = n̂ > n`. Taking `q = poly(d)` gives polynomial rate (`n̂ = poly(n)`) and distance `δ = 1 − 1/poly(n)`. Reed–Muller codes vary the number of variables, degree, and field size to interpolate between these examples.

<a id="pdf-bf2ce5422088-p143-b004"></a>
<!-- pdf-source: page=143; block=4; confidence=0.98 -->
**Construction 5.16 (Reed–Muller Codes).** For prime-power `q` and `d,m ∈ ℕ`, the `q`-ary Reed–Muller code of total degree at most `d` in `m` variables has blocklength `n̂ = q^m` and message length `n = binom(m+d,d) log q`; its codewords are evaluations of polynomials `p : 𝔽_q^m → 𝔽_q` of total degree at most `d`.

<a id="pdf-bf2ce5422088-p143-b005"></a>
<!-- pdf-source: page=143; block=5; confidence=0.68 -->
**Proposition 5.17.** The `q`-ary Reed–Muller code of degree `d` and dimension `m` has the properties continued on page 144.

<a id="pdf-bf2ce5422088-p144-b001"></a>
<!-- pdf-source: page=144; block=1; confidence=1.00 -->
## 5.2 List-Decoding Algorithms

<a id="pdf-bf2ce5422088-p144-b002"></a>
<!-- pdf-source: page=144; block=2; confidence=0.88 -->
**Proposition 5.17 (continued).** The code is explicit by encoding coefficient vectors `v ∈ 𝔽_q^{binom(m+d,d)}` as the corresponding polynomial; its minimum distance satisfies `δ ≥ 1 − d/q`; and it is `(1 − O(√(d/q)), O(√(q/d)))` list-decodable.

<a id="pdf-bf2ce5422088-p144-b003"></a>
<!-- pdf-source: page=144; block=3; confidence=0.99 -->
**Proof.** As for Reed–Solomon, with the Schwartz–Zippel lemma (Lemma 2.4) establishing the minimum-distance bound.

<a id="pdf-bf2ce5422088-p144-b004"></a>
<!-- pdf-source: page=144; block=4; confidence=0.99 -->
Reed–Solomon is Reed–Muller with `m=1`; Hadamard is essentially Reed–Muller with `d=1,q=2`, except Reed–Muller also includes affine linear functions.

<a id="pdf-bf2ce5422088-p144-b005"></a>
<!-- pdf-source: page=144; block=5; confidence=0.98 -->
This section presents efficient list-decoding algorithms for Reed–Solomon variants, running in time polynomial in the received word’s bit length, `poly(n̂, log |Σ|)`.

<a id="pdf-bf2ce5422088-p144-b006"></a>
<!-- pdf-source: page=144; block=6; confidence=0.96 -->
**Definition 5.18.** Let $\mathcal C$ be a code with encoding function $\mathrm{Enc}:\{1,\ldots,N\}\to\Sigma^{\hat n}$. For $r\in\Sigma^{\hat n}$, define
\[
\mathrm{LIST}(r,\varepsilon)=\{m\in\{1,\ldots,N\}:\operatorname{agr}(\mathrm{Enc}(m),r)>\varepsilon\}.
\]
Then the task of $(1-\varepsilon)$ list decoding is equivalent to producing the elements of $\mathrm{LIST}(r,\varepsilon)$ given $r\in\Sigma^{\hat n}$.

<a id="pdf-bf2ce5422088-p144-b007"></a>
<!-- pdf-source: page=144; block=7; confidence=1.00 -->
### 5.2.1 Review of Algebra

<a id="pdf-bf2ce5422088-p144-b008"></a>
<!-- pdf-source: page=144; block=8; confidence=0.99 -->
For every field $\mathbb F$, $\mathbb F[X_1,\ldots,X_n]$ is the integral domain consisting of formal polynomials $Q(X_1,\ldots,X_n)$ with coefficients in $\mathbb F$.

<a id="pdf-bf2ce5422088-p145-b001"></a>
<!-- pdf-source: page=145; block=1; confidence=0.96 -->
A nonzero polynomial is irreducible if it has no factorization into two nonconstant polynomials. The multivariate polynomial ring over a field is a unique factorization domain: every nonzero polynomial factors uniquely into irreducibles up to order and nonzero constant factors. If nonzero $Q(Y,Z)$ satisfies $Q(Y,f(Y))=0$, then $Z-f(Y)$ divides $Q$. The text also states polynomial-time algorithms for finding univariate irreducibles over finite fields and factoring polynomials, with randomized and deterministic bounds.

<a id="pdf-bf2ce5422088-p145-b002"></a>
<!-- pdf-source: page=145; block=2; confidence=0.96 -->
**Theorem 5.19.** For $\varepsilon=2\sqrt{d/q}$, the $q$-ary Reed–Solomon code of degree $d$ has a polynomial-time $(1-\varepsilon)$ list-decoding algorithm: given $r:\mathbb F_q\to\mathbb F_q$, it finds every polynomial of degree at most $d$ agreeing with $r$ on more than $\varepsilon q=2\sqrt{dq}$ inputs.

<a id="pdf-bf2ce5422088-p145-b003"></a>
<!-- pdf-source: page=145; block=3; confidence=0.96 -->
An optimized Johnson-bound argument improves the constant $2$ in the theorem’s error parameter to $1$, matching the combinatorial list-decoding radius.

<a id="pdf-bf2ce5422088-p145-b004"></a>
<!-- pdf-source: page=145; block=4; confidence=0.97 -->
**Proof.** Given the received word $r$, the proof constructs a polynomial that vanishes on its graph, then shows every sufficiently close codeword corresponds to a factor.

<a id="pdf-bf2ce5422088-p146-b001"></a>
<!-- pdf-source: page=146; block=1; confidence=0.99 -->
**Proof.** Step 1: Find a nonzero $Q(Y,Z)$ with individual degree bounds $d_Y$ in $Y$ and $d_Z$ in $Z$, satisfying $Q(y,r(y))=0$ for every $y\in\mathbb F_q$. These are $q$ homogeneous linear constraints on $(d_Y+1)(d_Z+1)$ coefficients, so a nonzero solution exists when $(d_Y+1)(d_Z+1)>q$ and can be found by linear algebra.

<a id="pdf-bf2ce5422088-p146-b002"></a>
<!-- pdf-source: page=146; block=2; confidence=0.94 -->
Step 2: For each $f$ agreeing with $r$ on more than $\varepsilon q$ inputs, $Q(Y,f(Y))$ has degree at most $d_Y+d d_Z$ and more than $\varepsilon q$ roots. Thus it is identically zero when $\varepsilon q\ge d_Y+d d_Z$. Consequently $Z-f(Y)$ divides $Q(Y,Z)$, so factoring $Q$ and extracting factors of this form enumerates the list. The two conditions are $(d_Y+1)(d_Z+1)>q$ and $\varepsilon q\ge d_Y+d d_Z$; the stated choice is $d_Y=\lfloor\varepsilon q/2\rfloor$, $d_Z=\lfloor\varepsilon q/(2d)\rfloor$, with $\varepsilon=2\sqrt{d/q}$.

<a id="pdf-bf2ce5422088-p146-b003"></a>
<!-- pdf-source: page=146; block=3; confidence=0.92 -->
The resulting rate is $\rho=(d+1)/q=\Theta(\varepsilon^2)$ and the alphabet size is stated as $q=\widetilde\Omega(n/\rho)=\widetilde\Omega(n/\varepsilon^2)$. The text contrasts this with random codes, which attain rate about $\varepsilon$ and alphabet size polynomial in $1/\varepsilon$, and notes that improving the Reed–Solomon bound is open even for inefficient decoding.

<a id="pdf-bf2ce5422088-p146-b004"></a>
<!-- pdf-source: page=146; block=4; confidence=0.90 -->
**Open Problem 5.20.** Do there exist constants $\varepsilon,\rho\in(0,1)$ with $\varepsilon<\sqrt{\rho}$ and infinitely many prime powers $q$ such that the $q$-ary Reed–Solomon code of degree $d=\lfloor\rho q\rfloor$ is $(1-\varepsilon,\operatorname{poly}(q))$-list-decodable?

<a id="pdf-bf2ce5422088-p147-b001"></a>
<!-- pdf-source: page=147; block=1; confidence=1.00 -->
## 5.2.3 Parvaresh–Vardy Codes

<a id="pdf-bf2ce5422088-p147-b002"></a>
<!-- pdf-source: page=147; block=2; confidence=0.98 -->
The goal is a rate–distance tradeoff $\rho=\widetilde\Theta(\varepsilon)$. Using more variables could reduce interpolation degree from roughly $q$ per variable to roughly $q^{1/m}$.

<a id="pdf-bf2ce5422088-p147-b003"></a>
<!-- pdf-source: page=147; block=3; confidence=0.98 -->
A proposed interpolation uses $Q(Y,Z_1,\ldots,Z_m)$ with individual degree bounds $d_Y$ and $d_Z$, constrained by $Q(y,r(y),\ldots,r(y))=0$. For close polynomials $f$, one would obtain $Q(Y,f(Y),\ldots,f(Y))=0$, suggesting factors of $Q^*(Y,Z)=Q(Y,Z,\ldots,Z)$. This fails because $Q^*$ may vanish identically even when $Q$ is nonzero.

<a id="pdf-bf2ce5422088-p147-b004"></a>
<!-- pdf-source: page=147; block=4; confidence=0.90 -->
A second proposal constrains $Q(y,r(y),r(y)^h,\ldots,r(y)^{h^{m-1}})=0$ and substitutes $Q^*(Y,Z)=Q(Y,Z,Z^h,\ldots,Z^{h^{m-1}})$. With individual $Z_i$ degrees at most $h-1$, distinct monomials map to distinct powers of $Z$, so $Q^*$ is nonzero when $Q$ is. But the degree of $Q^*(Y,f(Y))$ is roughly $d^*=d_Y+d h^m$, too large to meet $\varepsilon q\ge d^*$.

<a id="pdf-bf2ce5422088-p147-b005"></a>
<!-- pdf-source: page=147; block=5; confidence=0.97 -->
The construction sends evaluations of $f$ together with evaluations of $m-1$ additional degree-$d$ polynomials. These provide low-degree coordinates for the root argument while serving the role of successive powers in ensuring the substituted polynomial is nonzero.

<a id="pdf-bf2ce5422088-p147-b006"></a>
<!-- pdf-source: page=147; block=6; confidence=0.99 -->
For univariate polynomials $f(Y)$ and $E(Y)$, $f(Y)\bmod E(Y)$ denotes the remainder upon division of $f$ by $E$.

<a id="pdf-bf2ce5422088-p148-b001"></a>
<!-- pdf-source: page=148; block=1; confidence=0.99 -->
A polynomial modulo a degree-$k$ polynomial $E(Y)$ has a representative of degree at most $k-1$. If $E$ is irreducible over $\mathbb F_q$, then $\mathbb F_q[Y]/(E)$ is a field of size $q^k$. For multivariate $Q(Y,Z_1,\ldots,Z_m)$, reduce each coefficient in $\mathbb F_q[Y]$ modulo $E$ to regard $Q$ as a polynomial in the $Z_i$ over this quotient field.

<a id="pdf-bf2ce5422088-p148-b002"></a>
<!-- pdf-source: page=148; block=2; confidence=0.97 -->
**Construction 5.21 (Parvaresh–Vardy Codes).** Given a prime power $q$, parameters $m,d,h\in\mathbb N$, and irreducible $E(Y)\in\mathbb F_q[Y]$ of degree greater than $d$, the code has alphabet $\Sigma=\mathbb F_q^m$, blocklength $q$, and messages represented by polynomials $f(Y)$ of degree at most $d$. For each $y\in\mathbb F_q$, its encoded symbol is $[f_0(y),\ldots,f_{m-1}(y)]$, where $f_i(Y)=f(Y)^{h^i}\bmod E(Y)$.

<a id="pdf-bf2ce5422088-p148-b003"></a>
<!-- pdf-source: page=148; block=3; confidence=0.99 -->
**Theorem 5.22.** For every prime power $q$, integer $0\le d<q$, and irreducible polynomial $E$ of degree $d+1$, the $q$-ary Parvaresh–Vardy code of degree $d$, redundancy $m=\lceil\log(q/d)\rceil$, power $h=2$, and irreducible $E$ has rate $\rho=\widetilde\Omega(d/q)$ and can be list-decoded in polynomial time up to distance $\delta=1-\widetilde O(d/q)$.

<a id="pdf-bf2ce5422088-p149-b001"></a>
<!-- pdf-source: page=149; block=1; confidence=0.97 -->
**Proof.** Given a received word $r:\mathbb F_q\to\mathbb F_q^m$, seek all $f\in\mathrm{LIST}(r,\varepsilon)$ for $\varepsilon=\widetilde O(d/q)$.

<a id="pdf-bf2ce5422088-p149-b002"></a>
<!-- pdf-source: page=149; block=2; confidence=0.97 -->
Choose a nonzero $Q(Y,Z_0,\ldots,Z_{m-1})$ with degree at most $d_Y$ in $Y$ and at most $h-1$ in each $Z_i$, satisfying $Q(y,r(y))=0$ for every $y\in\mathbb F_q$. Linear algebra finds such a polynomial in time $\mathrm{poly}(q,m)$ when
\[
d_Yh^m>q. \tag{5.1}
\]
Assume $Q$ is not divisible by $E(Y)$: divide out all such factors if necessary, since irreducible $E$ has no roots in $\mathbb F_q$.

<a id="pdf-bf2ce5422088-p149-b003"></a>
<!-- pdf-source: page=149; block=3; confidence=0.98 -->
For each $f\in\mathrm{LIST}(r,\varepsilon)$, we have
\[
Q(Y,f_0(Y),\ldots,f_{m-1}(Y))=0. \tag{5.2}
\]
Since each $f_i$ has degree at most $\deg(E)-1=d$, this is ensured provided
\[
\varepsilon q\ge d_Y+(h-1)\cdot d\cdot m. \tag{5.3}
\]
Reducing both sides of (5.2) modulo $E(Y)$ gives
\[
0=Q(Y,f_0(Y),f_1(Y),\ldots,f_{m-1}(Y))\bmod E(Y)\\
=Q(Y,f(Y),f(Y)^h,\ldots,f(Y)^{h^{m-1}})\bmod E(Y),
\]
where $f_i(Y)=f(Y)^{h^i}\bmod E(Y)$. Thus, defining
\[
Q^*(Z)=Q(Y,Z,Z^h,\ldots,Z^{h^{m-1}})\bmod E(Y),
\]
$f(Y)$ is a root of $Q^*$ over the field $\mathbb F_q[Y]/(E(Y))$.

<a id="pdf-bf2ce5422088-p150-b001"></a>
<!-- pdf-source: page=150; block=1; confidence=0.99 -->
Observe that $Q^*$ is nonzero because $Q$ is not divisible by $E(Y)$ and has degree at most $h-1$ in each $Z_i$. Thus, we can find all elements of $\mathrm{LIST}(r,\varepsilon)$ by factoring $Q^*(Z)$. Constructing and factoring it can be done in time $\mathrm{poly}(q,d,h^m)=\mathrm{poly}(q)$. We satisfy Conditions (5.1) and (5.3) by setting $d_Y=\lceil\varepsilon q-dhm\rceil$, in which case Condition (5.1) holds for
\[
\varepsilon=\frac{1}{h^m}+\frac{dhm}{q}=\widetilde O(d/q), \tag{5.4}
\]
for $h=2$ and $m=\lceil\log(q/d)\rceil$. The rate is $\rho=d/(mq)=\widetilde\Omega(d/q)$, completing the proof.

<a id="pdf-bf2ce5422088-p150-b002"></a>
<!-- pdf-source: page=150; block=2; confidence=0.99 -->
The rate expression has a factor $m$ and (5.4) has a factor $hm$; the next construction addresses these losses.

<a id="pdf-bf2ce5422088-p150-b003"></a>
<!-- pdf-source: page=150; block=3; confidence=0.99 -->
## 5.2.4 Folded Reed–Solomon Codes

<a id="pdf-bf2ce5422088-p150-b004"></a>
<!-- pdf-source: page=150; block=4; confidence=0.92 -->
The section aims for rate $\rho$ arbitrarily close to the agreement parameter $\varepsilon$. In the PV construction take $E(Y)=Y^{q-1}-\gamma$, where $\gamma$ generates $\mathbb F_q^*$. This polynomial is irreducible, and the relation $f^q(Y)\bmod E(Y)=f(Y^q)\bmod E(Y)=f(\gamma Y)$ allows $h=q$ while the resulting $f_i$ retain degree $d$. For $y=\gamma^j\ne0$, the encoded symbol is
\[
[f(y),f(\gamma y),\ldots,f(\gamma^{m-1}y)]=[f(\gamma^j),f(\gamma^{j+1}),\ldots,f(\gamma^{j+m-1})]. \tag{5.5}
\]
Adjacent symbols overlap in all but one component, suggesting that roughly one in every $m$ symbols suffices to specify the word; the discussion continues beyond the supplied pages.

<a id="pdf-bf2ce5422088-p151-b001"></a>
<!-- pdf-source: page=151; block=1; confidence=0.98 -->
The folded Reed–Solomon construction is introduced after noting its rate is $\rho=d/q$, as for Reed–Solomon codes.

<a id="pdf-bf2ce5422088-p151-b002"></a>
<!-- pdf-source: page=151; block=2; confidence=0.99 -->
**Construction 5.23 (Folded Reed–Solomon Codes).** For a prime power $q$, a generator $\gamma$ of $\mathbb F_q^*$, and integers $m,d\in\mathbb N$, the $q$-ary folded Reed–Solomon code of degree $d$, folding parameter $m$, and generator $\gamma$ is defined as follows:

- The alphabet is $\Sigma=\mathbb F_q^m$.
- The blocklength is $\hat n=\lceil(q-1)/m\rceil$.
- The message space is $\mathbb F_q^{d+1}$, where we view each message as representing a polynomial $f(Y)$ of degree at most $d$ over $\mathbb F_q$.
- For $k\in[\hat n]$, the $k$th symbol of $\mathrm{Enc}(f)$ is
  \[
  [f(\gamma^{(k-1)m}),f(\gamma^{(k-1)m+1}),\ldots,f(\gamma^{km-1})].
  \]

<a id="pdf-bf2ce5422088-p151-b003"></a>
<!-- pdf-source: page=151; block=3; confidence=0.97 -->
The next result gives efficient list decoding near distance \(1-\rho\), where \(\rho=d/q\); the larger folding parameter preserves this rate while increasing runtime, list size, and alphabet size exponentially in \(m\).

<a id="pdf-bf2ce5422088-p151-b004"></a>
<!-- pdf-source: page=151; block=4; confidence=0.98 -->
**Theorem 5.24.** For prime power \(q\), integers \(0\le d,m\le q\), and generator \(\gamma\in\mathbb F_q^*\), the folded Reed–Solomon code of degree \(d\) and folding parameter \(m\) has rate at least \(\rho=d/q\) and can be list-decoded in time \(q^{O(m)}\) up to distance \(\delta=1-d/q-O(1/m)\).

<a id="pdf-bf2ce5422088-p151-b005"></a>
<!-- pdf-source: page=151; block=5; confidence=0.98 -->
**Proof.** Given a received word \(r:[\hat n]\to\mathbb F_q^m\), the goal is to find all codewords in \(\operatorname{LIST}(r,\varepsilon)\), with \(\varepsilon=d/q+O(1/m)\).

<a id="pdf-bf2ce5422088-p152-b001"></a>
<!-- pdf-source: page=152; block=1; confidence=0.97 -->
**Step 0: Unpack to a PV received word.** From $r$, we obtain a received word $r':\mathbb F_q\to\mathbb F_q^{m'}$ for the Parvaresh–Vardy code of degree $d$, power $h=q$, redundancy $m'=\lfloor\sqrt m-1\rfloor$, and irreducible $E(Y)=Y^{q-1}-\gamma$. Specifically, following Equation (5.5), each symbol of $r$ yields $m-m'$ symbols of $r'$. If $r$ agrees with the FRS encoding of $f$ in more than $\varepsilon\hat n$ positions, then $r'$ agrees with the PV encoding of $f$ in more than $\varepsilon\hat n(m-m')$ positions. We have
\[
\varepsilon\hat n(m-m')\ge\varepsilon\cdot\left(\frac{q-1}{m}-1\right)(m-m')=(\varepsilon-O(1/\sqrt m))\cdot q.
\]
Thus our task is to find $\mathrm{LIST}(r',\varepsilon')$ for $\varepsilon'=\varepsilon-O(1/\sqrt m)$, which we do in a similar manner to the decoding algorithm for Parvaresh–Vardy codes.

<a id="pdf-bf2ce5422088-p152-b002"></a>
<!-- pdf-source: page=152; block=2; confidence=0.97 -->
**Step 1.** Find nonzero \(Q(Y,Z_0,\ldots,Z_{m'-1})\) such that \(Q(y,r'(y))=0\) for every \(y\in\mathbb F_q\), with degree at most \(d_Y\) in \(Y\) and total degree at most 1 in the \(Z_i\) variables. There are \((d_Y+1)m'\) candidate monomials \(Y^jZ_i\), so linear algebra finds such a \(Q\) in polynomial time when \((d_Y+1)m'>q\), condition (5.6). Assume \(Q\) is not divisible by \(E(Y)\).

<a id="pdf-bf2ce5422088-p152-b003"></a>
<!-- pdf-source: page=152; block=3; confidence=0.95 -->
**Step 2.** For each \(f\in\operatorname{LIST}(r',\varepsilon')\), the agreement bound implies \(Q(Y,f_0(Y),\ldots,f_{m'-1}(Y))=0\), equation (5.7), provided \(\varepsilon' q\ge d_Y+d\), condition (5.8).

<a id="pdf-bf2ce5422088-p153-b001"></a>
<!-- pdf-source: page=153; block=1; confidence=0.98 -->
Since each \(f_i\) has degree at most \(d\), this is ensured provided
\[
\varepsilon' q\ge dy+d. \tag{5.8}
\]

Now, as in the Parvaresh–Vardy decoding, we can reduce both sides of Equation (5.7) modulo \(E(Y)\) and deduce
\[
0=Q(Y,f_0(Y),f_1(Y),\ldots,f_{m-1}(Y))\pmod{E(Y)}
=Q(Y,f(Y),f(Y)^h,\ldots,f(Y)^{h^{m-1}})\pmod{E(Y)}.
\]
Thus, if we define the univariate polynomial
\[
Q^*(Z)=Q(Y,Z,Z^h,\ldots,Z^{h^{m-1}})\pmod{E(Y)},
\]
then \(f(Y)\) is a root of \(Q^*\) over the field \(\mathbb F_q[Y]/E(Y)\). Observe that \(Q^*\) is nonzero because \(Q\) is not divisible by \(E(Y)\) and has degree at most \(h-1\) in each \(Z_i\). Thus, we can find all elements of \(\mathrm{LIST}(r',\varepsilon')\) by factoring \(Q^*(Z)\). Constructing and factoring \(Q^*(Z)\) can be done in time \(\operatorname{poly}(q,h^m)=q^{O(m)}\).

<a id="pdf-bf2ce5422088-p153-b002"></a>
<!-- pdf-source: page=153; block=2; confidence=0.91 -->
For this algorithm to work, we need to satisfy Conditions (5.6) and (5.8). We can satisfy Condition (5.6) by setting \(d_Y=\lfloor q/m'\rfloor\), in which case Condition (5.8) is satisfied for
\[
\varepsilon'\ge 1/m'+d/q.
\]
Recalling that \(\varepsilon'=\varepsilon-O(1/\sqrt m)\) and \(m'=\lfloor\sqrt{m-1}\rfloor\), we can take \(\varepsilon=d/q+O(1/\sqrt m)\).

<a id="pdf-bf2ce5422088-p153-b003"></a>
<!-- pdf-source: page=153; block=3; confidence=0.98 -->
**Theorem 5.25.** For all constants \(\varepsilon,\gamma>0\) and every \(n\in\mathbb N\), there exists an explicit code of message length \(n\), rate \(\rho=\varepsilon-\gamma\), and alphabet size \(q=\operatorname{poly}(n)\), list-decodable in polynomial time from distance \(1-\varepsilon\).

<a id="pdf-bf2ce5422088-p154-b001"></a>
<!-- pdf-source: page=154; block=1; confidence=0.98 -->
The discussed constructions have running time, alphabet size, and list size of the form \(n^{O(1/\gamma^2)}\). Nonconstructively, alphabet size \((1/\varepsilon)^{O(\varepsilon/\gamma)}\) and list size \(O(1/\gamma)\) are possible; recent randomized constructions achieve these parameters, while a fully explicit deterministic construction and capacity-achieving list decoding over a fixed-size alphabet such as \(q=2\) remain open.

<a id="pdf-bf2ce5422088-p154-b002"></a>
<!-- pdf-source: page=154; block=2; confidence=0.99 -->
**Open Problem 5.26.** For any desired constants \(\rho,\delta>0\) such that \(\rho>1-H_2(\delta)\), construct an explicit family of codes \(\mathrm{Enc}_n:\{0,1\}^n\to\{0,1\}^{\hat n}\) that have rate at least \(\rho\) and are \(\delta\)-list-decodable in polynomial time.

<a id="pdf-bf2ce5422088-p154-b003"></a>
<!-- pdf-source: page=154; block=3; confidence=1.00 -->
## 5.3 List-decoding Views of Samplers and Expanders

<a id="pdf-bf2ce5422088-p154-b004"></a>
<!-- pdf-source: page=154; block=4; confidence=0.99 -->
Averaging samplers and expander graphs can be expressed as variants of list-decodable codes, using a shared function representation.

<a id="pdf-bf2ce5422088-p154-b005"></a>
<!-- pdf-source: page=154; block=5; confidence=0.99 -->
**Construction 5.27 (Syntactic Correspondence of Expanders, Samplers, and Codes).** Each object is represented by \(\Gamma:[N]\times[D]\to[M]\): (1) for a bipartite multigraph with \(N\) left vertices, \(M\) right vertices, and left degree \(D\), let \(\Gamma(x,y)\) be the \(y\)-th neighbor of \(x\); (2) for a sampler \(\mathrm{Samp}:[N]\to[M]^D\), set \(\Gamma(x,y)=\mathrm{Samp}(x)_y\).

<a id="pdf-bf2ce5422088-p155-b001"></a>
<!-- pdf-source: page=155; block=1; confidence=0.99 -->
**Construction 5.27 (continued).** For a code \(\mathrm{Enc}:[N]\to[q]^D\), set \(M=qD\), identify \([q]\times[D]\) with \([M]\), and define \(\Gamma(x,y)=(y,\mathrm{Enc}(x)_y)\).

<a id="pdf-bf2ce5422088-p155-b002"></a>
<!-- pdf-source: page=155; block=2; confidence=0.99 -->
Note that codes correspond to expanders and samplers where the first component of a neighbor/sample equals the edge-label/sample-number. Conversely, any such expander/sampler can be viewed as a code. Many constructions of expanders and samplers have or can be easily modified to have this property. This syntactic constraint turns out to be quite natural in the setting of samplers. It corresponds to the case where we have \(D\) functions \(f_1,\ldots,f_D:[M]\to[0,1]\), we are interested in estimating the total average \((1/D)\sum_i\mu(f_i)\), but can only evaluate each \(f_i\) on a single sample.

<a id="pdf-bf2ce5422088-p155-b003"></a>
<!-- pdf-source: page=155; block=3; confidence=0.99 -->
**Definition 5.28.** For \(\Gamma:[N]\times[D]\to[M]\), \(T\subseteq[M]\), and \(\varepsilon\in[0,1)\), define \(\mathrm{LIST}_{\Gamma}(T,\varepsilon)=\{x:\Pr_{y}[\Gamma(x,y)\in T]>\varepsilon\}\), and define \(\mathrm{LIST}_{\Gamma}(T,1)=\{x:\forall y,\ \Gamma(x,y)\in T\}\). For \(f:[M]\to[0,1]\), define \(\mathrm{LIST}_{\Gamma}(f,\varepsilon)=\{x:\mathbb{E}_{y}[f(\Gamma(x,y))]>\varepsilon\}\).

<a id="pdf-bf2ce5422088-p155-b004"></a>
<!-- pdf-source: page=155; block=4; confidence=0.99 -->
The next propositions express list decoding, averaging-sampler guarantees, and vertex expansion using these list sets.

<a id="pdf-bf2ce5422088-p156-b001"></a>
<!-- pdf-source: page=156; block=1; confidence=0.99 -->
**Proposition 5.29.** Let \(\mathrm{Enc}\) and \(\Gamma\) be as in Construction 5.27. Then \(\mathrm{Enc}\) is \((1-1/q-\varepsilon,K)\) list-decodable iff for every \(r\in[M]^D\), \(|\mathrm{LIST}_{\Gamma}(T_r,1/q+\varepsilon)|\le K\), where \(T_r=\{(y,r_y):y\in[D]\}\).

<a id="pdf-bf2ce5422088-p156-b002"></a>
<!-- pdf-source: page=156; block=2; confidence=0.99 -->
**Proof.** Observe that, for each \(x\in[N]\) and \(r\in[M]^D\),
\[
\Pr_y[\Gamma(x,y)\in T_r]
=\Pr_y[(y,\mathrm{Enc}(x)_y)\in T_r]
=\Pr_y[\mathrm{Enc}(x)_y=r_y]
=\mathrm{agr}(\mathrm{Enc}(x),r).
\]
Thus \(|\mathrm{LIST}_{\Gamma}(T_r,1/q+\varepsilon)|\le K\) if and only if there are at most \(K\) messages \(x\) whose encodings have agreement greater than \(1/q+\varepsilon\) with \(r\), which is the same as being \((1-1/q-\varepsilon,K)\) list-decodable.

<a id="pdf-bf2ce5422088-p156-b003"></a>
<!-- pdf-source: page=156; block=3; confidence=0.99 -->
**Proposition 5.30.** Let \(\mathrm{Samp}\) and \(\Gamma\) be as in Construction 5.27. (1) \(\mathrm{Samp}\) is a \((\delta,\varepsilon)\) averaging sampler iff for every \(f:[M]\to[0,1]\), \(|\mathrm{LIST}_{\Gamma}(f,\mu(f)+\varepsilon)|\le\delta N\). (2) It is a \((\delta,\varepsilon)\) boolean averaging sampler iff for every \(T\subseteq[M]\), \(|\mathrm{LIST}_{\Gamma}(T,\mu(T)+\varepsilon)|\le\delta N\).

<a id="pdf-bf2ce5422088-p156-b004"></a>
<!-- pdf-source: page=156; block=4; confidence=0.99 -->
**Proof.** Membership \(x\in\mathrm{LIST}_{\Gamma}(f,\mu(f)+\varepsilon)\) is equivalent to the sampler output being bad: if \((z_1,\ldots,z_D)=\mathrm{Samp}(x)\), then \(\frac1D\sum_{i=1}^D f(z_i)>\mu(f)+\varepsilon\). Thus the sampler's error probability over uniform \(x\in[N]\) is at most \(\delta\) iff the list set has size at most \(\delta N\). The boolean case follows by taking \(f\) to be the indicator of \(T\).

<a id="pdf-bf2ce5422088-p157-b001"></a>
<!-- pdf-source: page=157; block=1; confidence=0.98 -->
The sampler-to-code implication uses the sets from Proposition 5.29, each of density $1/q$.

<a id="pdf-bf2ce5422088-p157-b002"></a>
<!-- pdf-source: page=157; block=2; confidence=0.97 -->
**Corollary 5.31.** If $\mathrm{Samp}(x)_y=(y,\mathrm{Enc}(x)_y)$ is a $(\delta,\varepsilon)$ Boolean averaging sampler, then $\mathrm{Enc}$ is $(1-1/q-\varepsilon,\delta N)$ list-decodable.

<a id="pdf-bf2ce5422088-p157-b003"></a>
<!-- pdf-source: page=157; block=3; confidence=0.98 -->
Typical parameter regimes differ: codes favor small alphabet $q$ and block length $D$ polynomial in message length $n=\log N$, while samplers often target exponentially large domains. The later converse states that a $(1-1/q-\varepsilon,\delta N)$ list-decodable encoding yields a $(\delta/\varepsilon,q\varepsilon)$ averaging sampler when $q$ is small.

<a id="pdf-bf2ce5422088-p157-b004"></a>
<!-- pdf-source: page=157; block=4; confidence=0.99 -->
**Definition 5.32.** A bipartite multigraph is an $(=K,A)$ vertex expander if every set $S$ of exactly $K$ left vertices has neighborhood size $|N(S)|\ge AK$. It is a $(K,A)$ vertex expander in the usual sense exactly when it is an $(=K',A)$ expander for every positive integer $K'\le K$.

<a id="pdf-bf2ce5422088-p157-b005"></a>
<!-- pdf-source: page=157; block=5; confidence=0.99 -->
**Proposition 5.33.** For \(K\in\mathbb N\), \(\Gamma:[N]\times[D]\to[M]\) is an \((=K,A)\) vertex expander iff for every set \(T\subseteq[D]\times[M]\) such that \(|T|<KA\), we have
\[
|\mathrm{LIST}_{\Gamma}(T,1)|<K.
\]

<a id="pdf-bf2ce5422088-p158-b001"></a>
<!-- pdf-source: page=158; block=1; confidence=0.95 -->
**Proof.** Failure of expansion is equivalent to a set $S\subseteq[N]$ with $|S|=K$ and $|N(S)|<KA$, equivalently one with $|S|\ge K$ and the same neighborhood bound. This in turn is equivalent to some $T\subseteq[M]$ with $|\mathrm{LIST}(T,1)|\ge K$ and $|T|<KA$: take $T=N(S)$ in one direction, and $S=\mathrm{LIST}(T,1)$ in the other, using $S\subseteq\mathrm{LIST}(N(S),1)$ and $N(\mathrm{LIST}(T,1))\subseteq T$.

<a id="pdf-bf2ce5422088-p158-b002"></a>
<!-- pdf-source: page=158; block=2; confidence=0.98 -->
The condition uses lists at threshold $1$, but expansion requires a sharp relation between list size and $|T|$; constant-factor losses can substantially reduce expansion.

<a id="pdf-bf2ce5422088-p158-b003"></a>
<!-- pdf-source: page=158; block=3; confidence=1.00 -->
## 5.4 Expanders from Parvaresh–Vardy Codes

<a id="pdf-bf2ce5422088-p158-b004"></a>
<!-- pdf-source: page=158; block=4; confidence=0.99 -->
The section applies the code-to-graph construction to obtain vertex expansion $A=(1-\varepsilon)D$ from Parvaresh–Vardy codes.

<a id="pdf-bf2ce5422088-p158-b005"></a>
<!-- pdf-source: page=158; block=5; confidence=0.99 -->
Consider the bipartite multigraph obtained from the Parvaresh–Vardy codes via the correspondence of Construction 5.27. That is, we define a neighbor function \(\Gamma:\mathbb F_q^n\times\mathbb F_q\to\mathbb F_q\times\mathbb F_q^m\) by
\[
\Gamma(f,y)=[y,f_0(y),f_1(y),\ldots,f_{m-1}(y)],
\]
where \(f(Y)\) is a polynomial of degree at most \(n-1\) over \(\mathbb F_q\), and we define \(f_i(Y)=f(Y)^{h^i}\bmod E(Y)\), where \(E\) is a fixed irreducible polynomial of degree \(n\) over \(\mathbb F_q\).

<a id="pdf-bf2ce5422088-p159-b001"></a>
<!-- pdf-source: page=159; block=1; confidence=0.99 -->
**Theorem 5.34.** Let \(\Gamma:\mathbb F_q^n\times\mathbb F_q\to\mathbb F_q^{m+1}\) be the neighbor function of the bipartite multigraph corresponding to the \(q\)-ary Parvaresh–Vardy code of degree \(d=n-1\), power \(h\), and redundancy \(m\) via Construction 5.27. Then \(\Gamma\) is a \((K_{\max},A)\) expander for \(K_{\max}=h^m\) and \(A=q-nhm\).

<a id="pdf-bf2ce5422088-p159-b002"></a>
<!-- pdf-source: page=159; block=2; confidence=0.79 -->
**Proof.** For each $K\le K_{\max}=h^m$, set $A=q-nmh$. By Proposition 5.33 it suffices to prove that every $T\subseteq\mathbb F_q^{m+1}$ with $|T|\le AK-1$ has $|\mathrm{LIST}(T,1)|\le K-1$. First handle $K=K_{\max}$, then adapt the argument for smaller $K$, following the Parvaresh–Vardy list-decoding proof.

<a id="pdf-bf2ce5422088-p159-b003"></a>
<!-- pdf-source: page=159; block=3; confidence=0.99 -->
**Step 1: Find a low-degree \(Q\) vanishing on \(T\).** We find a nonzero polynomial \(Q(Y,Z_0,\ldots,Z_{m-1})\) of degree at most \(d_Y=A-1\) in its first variable \(Y\) and at most \(h-1\) in each of the remaining variables such that \(Q(z)=0\) for all \(z\in T\). This is possible because
\[
A\cdot h^m=AK>|T|.
\]
Moreover, we may assume that \(Q\) is not divisible by \(E(Y)\). If it is, we can divide out all the factors of \(E(Y)\), which will not affect the conditions \(Q(z)=0\) since \(E\) has no roots (being irreducible).

<a id="pdf-bf2ce5422088-p159-b004"></a>
<!-- pdf-source: page=159; block=4; confidence=0.99 -->
**Step 2: Argue that each \(f(Y)\in\mathrm{LIST}(T,1)\) is a “root” of a related univariate polynomial \(Q^*\).** First, we argue as in the list-decoding algorithm that if \(f\in\mathrm{LIST}(T,1)\), we have
\[
Q(Y,f_0(Y),\ldots,f_{m-1}(Y))=0.
\]
This is ensured because
\[
q>A-1+nmh.
\]

<a id="pdf-bf2ce5422088-p160-b001"></a>
<!-- pdf-source: page=160; block=1; confidence=0.91 -->
Reducing the interpolation identity modulo $E(Y)$ gives $Q(Y,f(Y),f(Y)^h,\ldots,f(Y)^{h^{m-1}})=0$. Thus $f(Y)$ is a root over $\mathbb F_q[Y]/E(Y)$ of $Q^*(Z)=Q(Y,Z,Z^h,\ldots,Z^{h^{m-1}})\bmod E(Y)$. Since $Q$ is not divisible by $E(Y)$ and has individual degree at most $h-1$, $Q^*\ne0$ and $\deg Q^*\le(h-1)(1+h+\cdots+h^{m-1})=K-1$. Hence $|\mathrm{LIST}(T,1)|\le K-1$ (at the preceding parameter choice, the bound is $h-1$).

<a id="pdf-bf2ce5422088-p160-b002"></a>
<!-- pdf-source: page=160; block=2; confidence=0.90 -->
Restrict $Q$ to monomials $Y^i\mathrm{Mon}_j(Z_1,\ldots,Z_m)$ with $0\le i<A$, $0\le j<K$, where $j=j_0+j_1h+\cdots+j_{m-1}h^{m-1}$ and $\mathrm{Mon}_j=Z_1^{j_0}\cdots Z_m^{j_{m-1}}$. There are $AK>|T|$ such monomials, so the interpolation step is possible. Substitution $(Z,Z^h,\ldots,Z^{h^{m-1}})$ sends $\mathrm{Mon}_j$ to $Z^j$, giving $\deg Q^*\le K-1$ and the desired list-size bound.

<a id="pdf-bf2ce5422088-p160-b003"></a>
<!-- pdf-source: page=160; block=3; confidence=0.99 -->
**Theorem 5.35.** For every constant \(\alpha>0\), every \(N\in\mathbb N\), \(K\le N\), and \(\varepsilon>0\), there is an explicit \((K,(1-\varepsilon)D)\) expander with \(N\) left vertices, \(M\) right vertices, left-degree
\[
D=O\left(\left(\frac{(\log N)(\log K)}{\varepsilon}\right)^{1+1/\alpha}\right)
\]
and \(M\le D^2\cdot K^{1+\alpha}\). Moreover, \(D\) is a power of \(2\).

<a id="pdf-bf2ce5422088-p161-b001"></a>
<!-- pdf-source: page=161; block=1; confidence=0.99 -->
**Proof.** Let $n=\log N$ and $k=\log K_{\max}$. Let $h=\lceil(2nk/\varepsilon)^{1/\alpha}\rceil$ and let $q$ be the power of $2$ in the interval $(h^{1+\alpha/2},h^{1+\alpha}]$. Set $m=\lceil(\log K_{\max})/(\log h)\rceil$, so that $h^{m-1}\le K_{\max}\le h^m$. Then, by Theorem 5.34, the graph $\Gamma:F_q^n\times F_q\to F_q^{m+1}$ defined in (5.9) is an $(h^m,A)$ expander for $A=q-nhm$. Since $K_{\max}\le h^m$, it is also a $(K_{\max},A)$ expander.

Note that the number of left-vertices in $\Gamma$ is $q^n\ge N$, and the number of right-vertices is
\[
M=q^{m+1}\le q^2\cdot h^{(1+\alpha)(m-1)}\le q^2\cdot K_{\max}^{1+\alpha}.
\]
The degree is
\[
D=q\le h^{1+\alpha}=O((nk/\varepsilon)^{1+1/\alpha})=O(((\log N)(\log K_{\max})/\varepsilon)^{1+1/\alpha}).
\]
To see that the expansion factor $A=q-nhm\ge q-nhk$ is at least $(1-\varepsilon)D=(1-\varepsilon)q$, note that
\[
nhk\le(\varepsilon/2)\cdot h^{1+\alpha}\le\varepsilon q,
\]
where the first inequality holds because $h^\alpha\ge2nk/\varepsilon$. Finally, the construction is explicit because a description of $\mathbb F_q$ for $q$ a power of $2$ (i.e., an irreducible polynomial of degree $\log q$ over $\mathbb F_2$) as well as an irreducible polynomial $E(Y)$ of degree $n$ over $\mathbb F_q$ can be found in time $\mathrm{poly}(n,\log q)=\mathrm{poly}(\log N,\log D)$.

<a id="pdf-bf2ce5422088-p161-b002"></a>
<!-- pdf-source: page=161; block=2; confidence=0.84 -->
These graphs have polylogarithmic degree, near-maximal expansion, and right-side size near the lower bound $M\ge KA=(1-\varepsilon)KD$. They support a membership data structure for a $K$-element subset of $[N]$ using $K^{1.01}\mathrm{polylog}(N)$ bits and one-bit probabilistic queries. Efficient use also requires finding left vertices with many neighbors in a given right-side subset; a variant of the list-decoding algorithm provides this property.

<a id="pdf-bf2ce5422088-p162-b001"></a>
<!-- pdf-source: page=162; block=1; confidence=0.90 -->
For constant $\alpha$, Theorem 5.35 gives right-side size polynomial in $K,D$, while the optimal scale is $O(KD/\varepsilon)$. Obtaining that scale with polylogarithmic degree remains open; a construction with degree quasipolynomial in $\log N$ is known.

<a id="pdf-bf2ce5422088-p162-b002"></a>
<!-- pdf-source: page=162; block=2; confidence=0.97 -->
**Open Problem 5.36.** Construct $(K,A)$ bipartite expanders with $N$ left vertices, degree $D=\mathrm{poly}(\log N)$, expansion $A=0.99D$, and $M=O(KD)$ right vertices.

<a id="pdf-bf2ce5422088-p162-b003"></a>
<!-- pdf-source: page=162; block=3; confidence=0.99 -->
## 5.5 Exercises

<a id="pdf-bf2ce5422088-p162-b004"></a>
<!-- pdf-source: page=162; block=4; confidence=0.99 -->
**Problem 5.1 (Limits of List Decoding).** Show that if there exists a $q$-ary code $C\subseteq\Sigma^{\widehat n}$ of rate $\rho$ that is $(\delta,L)$ list-decodable, then
\[
\rho\le1-H_q(\delta,\widehat n)+(\log_q L)/\widehat n.
\]

<a id="pdf-bf2ce5422088-p162-b005"></a>
<!-- pdf-source: page=162; block=5; confidence=0.91 -->
**Problem 5.2 (Concatenated Codes).** Given $\mathrm{Enc}_1:\{1,\ldots,N\}\to\Sigma_1^{n_1}$ and $\mathrm{Enc}_2:\Sigma_1\to\Sigma_2^{n_2}$, define $\mathrm{Enc}(m)=\mathrm{Enc}_2(\mathrm{Enc}_1(m)_1)\cdots\mathrm{Enc}_2(\mathrm{Enc}_1(m)_{n_1})$, mapping into $\Sigma_2^{n_1n_2}$. This construction is used to reduce alphabet size, for example to $\Sigma_2=\{0,1\}$.

<a id="pdf-bf2ce5422088-p162-b006"></a>
<!-- pdf-source: page=162; block=6; confidence=0.83 -->
**Problem 5.2.** (1) Prove that if $\mathrm{Enc}_1$ and $\mathrm{Enc}_2$ have minimum distances $\delta_1$ and $\delta_2$, then $\mathrm{Enc}$ has minimum distance at least $\delta_1\delta_2$. (2) Prove that if $\mathrm{Enc}_1$ is $(1-\varepsilon_1,L_1)$ list-decodable and $\mathrm{Enc}_2$ is $(\delta_2,L_2)$ list-decodable, then $\mathrm{Enc}$ is $((1-\varepsilon_1L_2)\delta_2,L_1L_2)$ list-decodable.

<a id="pdf-bf2ce5422088-p163-b001"></a>
<!-- pdf-source: page=163; block=1; confidence=0.97 -->
Show that concatenation gives, for every n and ε>0, an explicit binary code of blocklength O(n²/ε²) and minimum distance at least 1/2−ε; with polynomial blocklength in n,1/ε, obtain polynomial-time list decoding up to radius 1/2−ε with list size poly(1/ε). The inner code may be brute-force decoded.

<a id="pdf-bf2ce5422088-p163-b002"></a>
<!-- pdf-source: page=163; block=2; confidence=0.99 -->
**Problem 5.3. List Decoding implies Unique Decoding for Random Errors.**

<a id="pdf-bf2ce5422088-p163-b003"></a>
<!-- pdf-source: page=163; block=3; confidence=0.98 -->
For a code C⊂{0,1}^n̂ with minimum distance ≥1/4 and rate ≤αε², transmit c∈C through independent bit flips of probability 1/2−2ε. Prove that for sufficiently small absolute constant α, except with exponentially small error probability, c is the unique codeword within distance 1/2−ε of the received word.

<a id="pdf-bf2ce5422088-p163-b004"></a>
<!-- pdf-source: page=163; block=4; confidence=0.96 -->
Deduce from Problem 5.2 that for every ε>0 and n, an explicit code of blocklength poly(n,1/ε) can be uniquely decoded in polynomial time from the random error model of part (1).

<a id="pdf-bf2ce5422088-p163-b005"></a>
<!-- pdf-source: page=163; block=5; confidence=0.99 -->
**Definition.** For prime power q, a q-ary code C⊂F_q^n̂ is linear if it is a vector subspace: u+v∈C and αu∈C for u,v∈C and α∈F_q.

<a id="pdf-bf2ce5422088-p163-b006"></a>
<!-- pdf-source: page=163; block=6; confidence=0.99 -->
Verify that Hadamard, Reed–Solomon, and Reed–Muller codes are linear.

<a id="pdf-bf2ce5422088-p163-b007"></a>
<!-- pdf-source: page=163; block=7; confidence=0.98 -->
For a linear code C, prove that minimum distance equals minimum nonzero weight, where wt(c)=|{i:c_i≠0}|/n̂ and the minimum weight is min_{c∈C\{0}}wt(c).

<a id="pdf-bf2ce5422088-p164-b001"></a>
<!-- pdf-source: page=164; block=1; confidence=0.97 -->
If C has dimension n, show its rate is n/n̂ and it has a linear encoding Enc:F_q^n→F_q^n̂. Choose n coordinates S⊂[n̂] so Enc(m)|_S=m for every message m; such an encoding is systematic and is later used for locally decodable codes.

<a id="pdf-bf2ce5422088-p164-b002"></a>
<!-- pdf-source: page=164; block=2; confidence=0.98 -->
Give explicit systematic encodings for Hadamard and Reed–Solomon codes.

<a id="pdf-bf2ce5422088-p164-b003"></a>
<!-- pdf-source: page=164; block=3; confidence=0.99 -->
(5) Show that the nonconstructive bound of Theorem 5.8, Part 1, can be achieved by a linear code. That is, for all prime powers $q$, integers $n,\widehat n\in\mathbb N$, and $\delta\in(0,1-1/q)$, there exists a linear $q$-ary code of block length $\widehat n$, minimum distance at least $\delta$, and rate at least $\rho=n/\widehat n$ provided $\rho\le1-H_q(\delta,\widehat n)$. (Hint: choose a random linear map $\mathrm{Enc}:\mathbb F_q^n\to\mathbb F_q^{\widehat n}$ and use Part 2.)

<a id="pdf-bf2ce5422088-p164-b004"></a>
<!-- pdf-source: page=164; block=4; confidence=0.99 -->
**Problem 5.5. LDPC Codes.**

<a id="pdf-bf2ce5422088-p164-b005"></a>
<!-- pdf-source: page=164; block=5; confidence=0.98 -->
**Definition.** For a bipartite multigraph G with N left vertices and M right vertices, define C={c∈{0,1}^N : for every j∈[M], ⊕_{i∈Γ(j)}c_i=0}, with {0,1} viewed as F₂ and Γ(j) the neighbors of j. If the left degree D is small (for example O(1)), C is an LDPC code.

<a id="pdf-bf2ce5422088-p164-b006"></a>
<!-- pdf-source: page=164; block=6; confidence=0.99 -->
Show that this code has rate at least 1−M/N.

<a id="pdf-bf2ce5422088-p164-b007"></a>
<!-- pdf-source: page=164; block=7; confidence=0.98 -->
If G is a (K,A)-expander with A>D/2, prove C has minimum distance at least δ=K/N.

<a id="pdf-bf2ce5422088-p164-b008"></a>
<!-- pdf-source: page=164; block=8; confidence=0.95 -->
For sufficiently small constant ε, show that a (K,(1−ε)D)-expander gives a polynomial-time δ-decoder, δ=(1−3ε)K/N, assuming G is supplied. Hint: flip each received coordinate whose neighboring parity checks are unsatisfied in at least 2/3 of cases, and show the error count contracts by a constant factor; Problem 4.10 may help.

<a id="pdf-bf2ce5422088-p165-b001"></a>
<!-- pdf-source: page=165; block=1; confidence=0.96 -->
A probabilistic argument as in Theorem 4.4 gives graphs with D=O(1), K=Ω(N), M=(1−Ω(1))N, arbitrarily small constant ε>0, and N→∞; explicit constructions are also known. These yield explicit LDPC codes with constant rate and distance.

<a id="pdf-bf2ce5422088-p165-b002"></a>
<!-- pdf-source: page=165; block=2; confidence=0.99 -->
**Problem 5.6. Improved list decoding of Reed–Solomon Codes.**

<a id="pdf-bf2ce5422088-p165-b003"></a>
<!-- pdf-source: page=165; block=3; confidence=0.99 -->
(1) Show that there is a polynomial-time algorithm for list decoding the Reed–Solomon codes of degree $d$ over $\mathbb F_q$ up to distance $1-\sqrt{2d/q}$, improving the $1-2\sqrt{d/q}$ bound from Theorem 5.19. (Hint: do not use fixed upper bounds on the individual degrees of the interpolating polynomial $Q(Y,Z)$, but rather allow as many monomials as possible.)

<a id="pdf-bf2ce5422088-p165-b004"></a>
<!-- pdf-source: page=165; block=4; confidence=0.99 -->
(2) (*) Improve the list-decoding radius further to $1-\sqrt{d/q}$ by using the following “method of multiplicities.” First, require the interpolating polynomial $Q(Y,Z)$ to have a zero of multiplicity $s$ at each point $(y,r(y))$—that is, the polynomial $Q(Y+y,Z+r(y))$ should have no monomials of degree smaller than $s$. Second, use the fact that a univariate polynomial $R(Y)$ of degree $t$ can have at most $t$ roots, counting multiplicities.

<a id="pdf-bf2ce5422088-p165-b005"></a>
<!-- pdf-source: page=165; block=5; confidence=0.90 -->
**Problem 5.7. Twenty Questions.** The oracle holds two secrets s₁,s₂∈{0,1}^n and may adversarially choose which secret governs each yes/no answer; the excerpt begins introducing this variant after noting that one secret requires n questions.

<a id="pdf-bf2ce5422088-p166-b001"></a>
<!-- pdf-source: page=166; block=1; confidence=0.99 -->
For an unknown secret in a pair \(\{s_1,s_2\}\subseteq\{0,1\}^n\), each query \(f:\{0,1\}^n\to\{0,1\}\) may return either \(f(s_1)\) or \(f(s_2)\). Exact identification is impossible, but the goal is to find a list \(L\) with \(|L\cap\{s_1,s_2\}|>0\), potentially with \(|L|=2\).

<a id="pdf-bf2ce5422088-p166-b002"></a>
<!-- pdf-source: page=166; block=2; confidence=0.98 -->
Given a code \(\mathrm{Enc}:\{0,1\}^n\to\{0,1\}^{\hat n}\) whose distinct codewords agree in at least a \((1/2-\varepsilon)\) fraction of coordinates, and a polynomial-time \((1/4+\varepsilon,\ell)\) list-decoder, show that the pair-secret problem can be solved in polynomial time using the \(\hat n\) queries \(f_i(x)=\mathrm{Enc}(x)_i\).

<a id="pdf-bf2ce5422088-p166-b003"></a>
<!-- pdf-source: page=166; block=3; confidence=0.99 -->
Using the code from Problem 1, deduce that \(\hat n=\operatorname{poly}(n)\) queries suffice.

<a id="pdf-bf2ce5422088-p166-b004"></a>
<!-- pdf-source: page=166; block=4; confidence=1.00 -->
## 5.6 Chapter Notes and References

<a id="pdf-bf2ce5422088-p166-b005"></a>
<!-- pdf-source: page=166; block=5; confidence=0.97 -->
The notes cite standard coding theory and list-decoding references, then trace the field from Shannon’s stochastic-error capacity result through Hamming’s worst-case decoding and the independent introductions of list decoding by Elias and Wozencraft. Theorem 5.8(1)’s nonconstructive rate–distance bound is Gilbert’s; Problem 5.4(5)’s linear-code extension is Varshamov’s, together forming the Gilbert–Varshamov bound. Algebraic-geometric codes can surpass that bound.

<a id="pdf-bf2ce5422088-p167-b001"></a>
<!-- pdf-source: page=167; block=1; confidence=0.98 -->
Theorem 5.8(2)’s nonconstructive list-decoding bound is due to Elias, with extensions to linear codes; Proposition 5.10 is the binary Johnson bound. The notes review Reed–Muller and Reed–Solomon codes, unique decoding, Goldreich–Levin’s local Hadamard list decoding, Sudan’s Theorem 5.19, and later list-decoding constructions including Guruswami–Sudan, Parvaresh–Vardy, and folded Reed–Solomon codes.

<a id="pdf-bf2ce5422088-p167-b002"></a>
<!-- pdf-source: page=167; block=2; confidence=0.98 -->
The notes describe connections among extractors, expanders, averaging samplers, and list-decodable codes, and attribute a list-decoding formulation of vertex expansion and an expander construction from Parvaresh–Vardy codes to Guruswami, Umans, and Vadhan.

<a id="pdf-bf2ce5422088-p168-b001"></a>
<!-- pdf-source: page=168; block=1; confidence=0.98 -->
Forney introduced code concatenation (Problem 5.2) to obtain explicit efficiently decodable binary codes reaching capacity for random errors; efficient list decoding for Reed–Solomon concatenated with Hadamard is also cited. Gallager introduced LDPC codes (Problem 5.5), and Sipser–Spielman used expansion to analyze them and their decoding; explicit expanders for that problem and surveys on expander-based codes and LDPC codes are referenced.

<a id="pdf-bf2ce5422088-p168-b002"></a>
<!-- pdf-source: page=168; block=2; confidence=0.99 -->
Problem 5.7’s Twenty Questions challenge arose from Internet-routing motivation; its list-decoding solution is attributed to [20].

<a id="pdf-bf2ce5422088-p169-b001"></a>
<!-- pdf-source: page=169; block=1; confidence=1.00 -->
# 6 Randomness Extractors

<a id="pdf-bf2ce5422088-p169-b002"></a>
<!-- pdf-source: page=169; block=2; confidence=0.99 -->
Extractors convert biased, correlated sources into nearly uniform bits and connect several pseudorandomness constructions, including expanders, list-decodable codes, generators, and samplers.

<a id="pdf-bf2ce5422088-p170-b001"></a>
<!-- pdf-source: page=170; block=1; confidence=1.00 -->
## 6.1 Motivation and Definition

<a id="pdf-bf2ce5422088-p170-b002"></a>
<!-- pdf-source: page=170; block=2; confidence=1.00 -->
### 6.1.1 Deterministic Extractors

<a id="pdf-bf2ce5422088-p170-b003"></a>
<!-- pdf-source: page=170; block=3; confidence=0.99 -->
A deterministic extractor could preprocess a weak random input so an algorithm designed for uniform bits can still run correctly; formally, one seeks Ext mapping {0,1}^n to {0,1}^m whose output on the source is uniform or nearly uniform.

<a id="pdf-bf2ce5422088-p170-b004"></a>
<!-- pdf-source: page=170; block=4; confidence=0.99 -->
For independent identically distributed bits with unknown bias δ, von Neumann’s procedure groups bits into pairs: output 0 on 01, output 1 on 10, and discard 00 or 11. The retained bit is unbiased; the expected number of pairs per output bit is 1/(2δ(1−δ)).

<a id="pdf-bf2ce5422088-p170-b005"></a>
<!-- pdf-source: page=170; block=5; confidence=0.98 -->
The text next considers independent bits with potentially different biases, each bounded away from 0 and 1; this discussion continues on the next page.

<a id="pdf-bf2ce5422088-p171-b001"></a>
<!-- pdf-source: page=171; block=1; confidence=0.99 -->
It can be shown that when we take a parity of $\ell$ bits from such an independent-bit source, the result approaches an unbiased coin flip exponentially fast in $\ell$, i.e., $\left|\Pr\left[\bigoplus_{i=1}^{\ell}X_i=1\right]-1/2\right|=2^{-\Omega(\ell)}$. The result is not a perfect coin flip but is as good as one for almost all purposes.

<a id="pdf-bf2ce5422088-p171-b002"></a>
<!-- pdf-source: page=171; block=2; confidence=0.99 -->
A source on {0,1}^n is a random variable taking values there. IndBits_{n,δ} consists of sources whose bits are independent and satisfy δ ≤ Pr[Xi=1] ≤ 1−δ. IIDBits_{n,δ} adds the requirement that all bit marginals are equal.

<a id="pdf-bf2ce5422088-p171-b003"></a>
<!-- pdf-source: page=171; block=3; confidence=0.99 -->
**Definition 6.1 (deterministic extractors).** Given a class C of sources on {0,1}^n, an ε-extractor is a function Ext:{0,1}^n→{0,1}^m such that for every X∈C, Ext(X) is ε-close to the uniform distribution U_m.

<a id="pdf-bf2ce5422088-p171-b004"></a>
<!-- pdf-source: page=171; block=4; confidence=0.99 -->
A single extractor must work for every source in C without knowing its exact distribution. It receives one sample unless multiple independent samples are explicitly included in the source model.

<a id="pdf-bf2ce5422088-p171-b005"></a>
<!-- pdf-source: page=171; block=5; confidence=0.99 -->
The term deterministic, or seedless, distinguishes these extractors from the seeded probabilistic extractors introduced later.

<a id="pdf-bf2ce5422088-p172-b001"></a>
<!-- pdf-source: page=172; block=1; confidence=0.99 -->
## 6.1 Motivation and Definition

<a id="pdf-bf2ce5422088-p172-b002"></a>
<!-- pdf-source: page=172; block=2; confidence=0.99 -->
**Definition 6.2.** For random variables $X,Y$ over $U$, their statistical (variation) distance is $\Delta(X,Y)=\max_{T\subseteq U}|\Pr[X\in T]-\Pr[Y\in T]|$. They are $\varepsilon$-close if $\Delta(X,Y)\leq\varepsilon$.

<a id="pdf-bf2ce5422088-p172-b003"></a>
<!-- pdf-source: page=172; block=3; confidence=0.98 -->
**Lemma 6.3 (properties of statistical difference).** For $U$-valued random variables $X,Y,Z,X_1,X_2,Y_1,Y_2$: (1) $\Delta(X,Y)\geq0$, with equality iff their distributions coincide; (2) $\Delta(X,Y)\leq1$, with equality iff their supports are disjoint; (3) symmetry: $\Delta(X,Y)=\Delta(Y,X)$; (4) triangle inequality: $\Delta(X,Z)\leq\Delta(X,Y)+\Delta(Y,Z)$; (5) for every function $f$, $\Delta(f(X),f(Y))\leq\Delta(X,Y)$; (6) if $X_1,X_2$ are independent and $Y_1,Y_2$ are independent, then $\Delta((X_1,X_2),(Y_1,Y_2))\leq\Delta(X_1,Y_1)+\Delta(X_2,Y_2)$; (7) $\Delta(X,Y)=\frac12|X-Y|_1$, where $|\cdot|_1$ is the $\ell_1$ distance.

<a id="pdf-bf2ce5422088-p172-b004"></a>
<!-- pdf-source: page=172; block=4; confidence=0.99 -->
An extractor can replace uniform random bits in an algorithm while increasing its error by at most the extractor error.

<a id="pdf-bf2ce5422088-p172-b005"></a>
<!-- pdf-source: page=172; block=5; confidence=0.97 -->
**Proposition 6.4.** Suppose randomized algorithm $A(w;r)$ has error at most $\gamma$ when $r\sim U_m$, and $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ is an $\varepsilon$-extractor for source class $\mathcal C$. Define $A^*(w;x)=A(w;\mathrm{Ext}(x))$. Then for every $X\in\mathcal C$, $A^*(w;X)$ has error at most $\gamma+\varepsilon$.

<a id="pdf-bf2ce5422088-p173-b001"></a>
<!-- pdf-source: page=173; block=1; confidence=0.99 -->
The discussion motivates requiring efficient extractors and polynomially many weak-source bits to produce $m$ nearly uniform bits.

<a id="pdf-bf2ce5422088-p173-b002"></a>
<!-- pdf-source: page=173; block=2; confidence=0.97 -->
**Proposition 6.5.** For every constant $\delta>0$ and $n,m\in\mathbb N$, there is a polynomial-time function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ that is an $\varepsilon$-extractor for $\mathrm{IndBits}_{n,\delta}$, with $\varepsilon=m\cdot2^{-\Omega(n/m)}$. In particular, $n=m^2$ gives exponentially small error using a polynomial-length source.

<a id="pdf-bf2ce5422088-p173-b003"></a>
<!-- pdf-source: page=173; block=3; confidence=0.96 -->
**Proof.** Partition the source into $m$ blocks, each of length approximately $n/m$, and output the parity of each block.

<a id="pdf-bf2ce5422088-p173-b004"></a>
<!-- pdf-source: page=173; block=4; confidence=0.99 -->
## Unpredictable-Bit Sources (Santha–Vazirani sources)

<a id="pdf-bf2ce5422088-p173-b005"></a>
<!-- pdf-source: page=173; block=5; confidence=0.98 -->
These are the sources that for every $i$, every $x_1,\ldots,x_n\in\{0,1\}$ and some constant $\delta>0$, satisfy
\[
\delta\le\Pr[X_i=1\mid X_1=x_1,X_2=x_2,\ldots,X_{i-1}=x_{i-1}]\le1-\delta.
\]

<a id="pdf-bf2ce5422088-p173-b006"></a>
<!-- pdf-source: page=173; block=6; confidence=0.98 -->
The parity construction does not extract from these sources; the text states that no nontrivial extractor exists and that outputting the first bit is optimal.

<a id="pdf-bf2ce5422088-p173-b007"></a>
<!-- pdf-source: page=173; block=7; confidence=0.98 -->
**Proposition 6.6.** For every $n\in\mathbb N$, $\delta>0$, and fixed $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}$, some $X\in\mathrm{UnpredBits}_{n,\delta}$ satisfies either $\Pr[\mathrm{Ext}(X)=1]\leq\delta$ or $\Pr[\mathrm{Ext}(X)=1]\geq1-\delta$. Consequently, no $\varepsilon$-extractor for this class exists when $\varepsilon<1/2-\delta$.

<a id="pdf-bf2ce5422088-p174-b001"></a>
<!-- pdf-source: page=174; block=1; confidence=0.99 -->
The proof is assigned as Problem 6.6; the text then announces that a broader source class will permit simulation of BPP algorithms.

<a id="pdf-bf2ce5422088-p174-b002"></a>
<!-- pdf-source: page=174; block=2; confidence=0.99 -->
## 6.1.2 Entropy Measures and General Weak Sources

<a id="pdf-bf2ce5422088-p174-b003"></a>
<!-- pdf-source: page=174; block=3; confidence=0.99 -->
Extracting $m$ nearly uniform bits suggests requiring at least $m$ bits of source randomness; entropy measures formalize this requirement.

<a id="pdf-bf2ce5422088-p174-b004"></a>
<!-- pdf-source: page=174; block=4; confidence=0.98 -->
**Definition 6.7 (entropy measures).** Let $X$ be a random variable. Then

- the Shannon entropy of $X$ is:
  \[
  H_{\mathrm{Sh}}(X)=\mathbb E_{x\leftarrow X}\left[\log\frac1{\Pr[X=x]}\right].
  \]
- the Rényi entropy of $X$ is:
  \[
  H_2(X)=\log\left(\frac1{\mathbb E_{x\leftarrow X}[\Pr[X=x]]}\right)=\log\frac1{\mathrm{CP}(X)},
  \]
  and
- the min-entropy of $X$ is:
  \[
  H_\infty(X)=\min_x\left\{\log\frac1{\Pr[X=x]}\right\},
  \]
where all logs are base 2.

<a id="pdf-bf2ce5422088-p174-b005"></a>
<!-- pdf-source: page=174; block=5; confidence=0.94 -->
The Rényi entropy $H_2(X)$ is distinct from the binary entropy function $H_2(\delta)$; the $q$-ary entropy $H_q(\delta)$ equals the Shannon entropy of a variable that is $1$ with probability $1-\delta$ and uniform on $\{2,\ldots,q\}$ with probability $\delta$.

<a id="pdf-bf2ce5422088-p175-b001"></a>
<!-- pdf-source: page=175; block=1; confidence=0.99 -->
**Lemma 6.8.** For each entropy measure \(H\in\{H_{\mathrm{Sh}},H_2,H_\infty\}\): (i) \(H(X)\ge 0\), with equality exactly when \(X\) is supported at one point; (ii) \(H(X)\le \log|\operatorname{Supp}(X)|\), with equality exactly when \(X\) is uniform on its support; (iii) independent \(X,Y\) satisfy \(H((X,Y))=H(X)+H(Y)\); (iv) every deterministic \(f\) satisfies \(H(f(X))\le H(X)\); and (v) \(H_\infty(X)\le H_2(X)\le H_{\mathrm{Sh}}(X)\).

<a id="pdf-bf2ce5422088-p175-b002"></a>
<!-- pdf-source: page=175; block=2; confidence=0.98 -->
For a source equal to \(0^n\) with probability \(0.99\) and uniform on \(\{0,1\}^n\) with probability \(0.01\), the text gives \(H_{\mathrm{Sh}}(X)\ge 0.01n\), \(H_2(X)\le\log(1/0.99^2)<1\), and \(H_\infty(X)\le\log(1/0.99)<1\). It motivates using stronger entropy measures for one-sample extraction; Shannon entropy is often useful for many independent samples and has convenient identities.

<a id="pdf-bf2ce5422088-p176-b001"></a>
<!-- pdf-source: page=176; block=1; confidence=0.99 -->
**Definition 6.9.** A random variable \(X\) is a \(k\)-source if \(H_\infty(X)\ge k\), equivalently \(\Pr[X=x]\le 2^{-k}\) for every \(x\). The min-entropy rate is \(\delta=k/n\) in the setting \(k=\delta n\). Common regimes listed are \(k=\operatorname{polylog}(n)\), \(k=n^\gamma\) for constant \(\gamma\in(0,1)\), \(k=\delta n\) for constant \(\delta\in(0,1)\), and \(k=n-O(1)\).

<a id="pdf-bf2ce5422088-p176-b002"></a>
<!-- pdf-source: page=176; block=2; confidence=0.96 -->
Examples include oblivious bit-fixing sources (\(k\) independent random bits and \(n-k\) fixed bits), adaptive bit-fixing sources (the remaining bits may depend on the random bits), unpredictable-bit sources with bias \(\delta\), stated to have \(k=\log(1/(1-\delta)^n)=\Theta(\delta n)\), and flat \(k\)-sources, uniform on a set of size \(2^k\).

<a id="pdf-bf2ce5422088-p176-b003"></a>
<!-- pdf-source: page=176; block=3; confidence=0.99 -->
**Lemma 6.10.** Every $k$-source is a convex combination of flat $k$-sources (provided that $2^k\in\mathbb N$), i.e., $X=\sum_i p_iX_i$ with $0\le p_i\le1$, $\sum_i p_i=1$ and all the $X_i$ are flat $k$-sources.

<a id="pdf-bf2ce5422088-p176-b004"></a>
<!-- pdf-source: page=176; block=4; confidence=0.98 -->
A general \(k\)-source can be sampled by first choosing a flat \(k\)-source according to the mixture weights, then sampling from it; thus an algorithm working for flat sources extends to all \(k\)-sources.

<a id="pdf-bf2ce5422088-p177-b001"></a>
<!-- pdf-source: page=177; block=1; confidence=0.99 -->
**Proof.** Let $X$ be a $k$-source on $[N]$. View $X$ as partitioning the unit circle into $N$ half-open intervals, where interval $I_t$ has length exactly $\Pr[X=t]$. Associate the circle with $[0,1)$, so $I_t=[\Pr[X<t],\Pr[X\le t])$. Let $S$ be a set of $K$ equally spaced points on the circle. Since each interval is half-open and has length at most $1/K$, each interval contains at most one point from $S$. Thus the uniform distribution on $T(S)=\{t:S\cap I_t\ne\emptyset\}$ is a flat $k$-source. If we rotate $S$ uniformly at random to obtain $R$ and choose a uniformly random element of $T(R)$, the probability of outputting any value $t\in[N]$ is exactly the length of $I_t$, which equals $\Pr[X=t]$. Thus $X=\sum_T p_TU_T$, where the sum is over subsets $T\subseteq[N]$ of size $K$, and $p_T=\Pr_R[T(R)=T]$.

<a id="pdf-bf2ce5422088-p177-b002"></a>
<!-- pdf-source: page=177; block=2; confidence=0.98 -->
View a distribution on \([N]\) as a vector \(X\in\mathbb R^N\). The \(k\)-sources are exactly those satisfying \(0\le X(i)\le2^{-k}\) for each \(i\), and \(\sum_iX(i)=1\). This is a convex polytope; its vertices have \(X(i)=2^{-k}\) at \(2^k\) coordinates and zero elsewhere, hence are flat \(k\)-sources. Every point of the polytope is a convex combination of its vertices.

<a id="pdf-bf2ce5422088-p177-b003"></a>
<!-- pdf-source: page=177; block=3; confidence=0.99 -->
## 6.1.3 Seeded Extractors

<a id="pdf-bf2ce5422088-p177-b004"></a>
<!-- pdf-source: page=177; block=4; confidence=0.98 -->
The text notes that Proposition 6.6 rules out deterministic extractors for unpredictable sources, then turns to the more general class of \(k\)-sources.

<a id="pdf-bf2ce5422088-p178-b001"></a>
<!-- pdf-source: page=178; block=1; confidence=0.96 -->
Deterministic extractors cannot work for all sources in the discussion; the impossibility for general min-entropy sources is simpler to show.

<a id="pdf-bf2ce5422088-p178-b002"></a>
<!-- pdf-source: page=178; block=2; confidence=0.99 -->
**Proposition 6.11.** For every function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}$, there is an $(n-1)$-source $X$ such that $\mathrm{Ext}(X)$ is constant.

<a id="pdf-bf2ce5422088-p178-b003"></a>
<!-- pdf-source: page=178; block=3; confidence=0.99 -->
**Proof.** Some $b\in\{0,1\}$ has $|\mathrm{Ext}^{-1}(b)|\ge 2^{n-1}$. Let $X$ be uniform on $\mathrm{Ext}^{-1}(b)$; then $\mathrm{Ext}(X)=b$ always.

<a id="pdf-bf2ce5422088-p178-b004"></a>
<!-- pdf-source: page=178; block=4; confidence=0.97 -->
When the extractor may depend on the source, a random function can extract from a fixed flat source with high probability.

<a id="pdf-bf2ce5422088-p178-b005"></a>
<!-- pdf-source: page=178; block=5; confidence=0.99 -->
**Proposition 6.12.** For every $n,k,m\in\mathbb{N}$, every $\varepsilon>0$, and every flat $k$-source $X$, if we choose a random function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ with $m=k-2\log(1/\varepsilon)-O(1)$, then $\mathrm{Ext}(X)$ will be $\varepsilon$-close to $U_m$ with probability $1-2^{-\Omega(K\varepsilon^2)}$, where $K=2^k$.

<a id="pdf-bf2ce5422088-p178-b006"></a>
<!-- pdf-source: page=178; block=6; confidence=0.96 -->
**Proof.** For each $T\subseteq[M]$, require $\left|\Pr[\mathrm{Ext}(X)\in T]-\Pr[U_m\in T]\right|\le\varepsilon$. For flat $X$, this is the condition that the fraction of support points mapped into $T$ differs from the density $\mu(T)$ by at most $\varepsilon$. Each support point maps into $T$ independently with probability $\mu(T)$, so Chernoff's bound gives failure probability at most $2^{-\Omega(K\varepsilon^2)}$ for each fixed $T$. A union bound over the $2^M$ subsets gives total failure probability at most $2^M2^{-\Omega(K\varepsilon^2)}<1$ for the stated choice of $m$.

<a id="pdf-bf2ce5422088-p178-b007"></a>
<!-- pdf-source: page=178; block=7; confidence=0.92 -->
Although the fixed-source failure probability is doubly exponentially small in $k$, the number of flat $k$-sources is approximately $\binom{N}{K}$, where $N=2^n$, so a direct union bound is insufficient.

<a id="pdf-bf2ce5422088-p179-b001"></a>
<!-- pdf-source: page=179; block=1; confidence=0.98 -->
**Definition 6.13 (seeded extractor).** A function $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$-extractor if, for every $k$-source $X$ on $\{0,1\}^n$, $\mathrm{Ext}(X,U_d)$ is $\varepsilon$-close to $U_m$. For domains and ranges $[N],[D],[M]$, respectively, use the analogous condition $\mathrm{Ext}(X,U_{[D]})$ is $\varepsilon$-close to $U_{[M]}$.

<a id="pdf-bf2ce5422088-p179-b002"></a>
<!-- pdf-source: page=179; block=2; confidence=0.99 -->
The construction aims to minimize seed length $d$ and maximize output length $m$.

<a id="pdf-bf2ce5422088-p179-b003"></a>
<!-- pdf-source: page=179; block=3; confidence=0.99 -->
**Theorem 6.14.** For every $n\in\mathbb N$, $k\in[0,n]$, and $\varepsilon>0$, there is a $(k,\varepsilon)$-extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $m=k+d-2\log(1/\varepsilon)-O(1)$ and $d=\log(n-k)+2\log(1/\varepsilon)+O(1)$.

<a id="pdf-bf2ce5422088-p179-b004"></a>
<!-- pdf-source: page=179; block=4; confidence=0.98 -->
A motivating regime takes $k=\delta n$ and constant $\varepsilon$, for fixed $\delta>0$.

<a id="pdf-bf2ce5422088-p179-b005"></a>
<!-- pdf-source: page=179; block=5; confidence=0.99 -->
**Proof.** Choose the extractor $\mathrm{Ext}$ at random. By Lemma 6.10, it suffices for $\mathrm{Ext}$ to work for flat $k$-sources. The probability that the extractor fails is at most the number of flat $k$-sources times the probability that $\mathrm{Ext}$ fails for a fixed flat $k$-source. By Proposition 6.12, the probability of failure for a fixed flat $k$-source is at most $2^{-\Omega(KD\varepsilon^2)}$, since $(X,U_d)$ is a flat $(k+d)$-source and $m=k+d-2\log(1/\varepsilon)-O(1)$. Thus the total failure probability is at most $\binom{N}{K}\cdot 2^{-\Omega(KD\varepsilon^2)}\le \left(\frac{Ne}{K}\right)^K2^{-\Omega(KD\varepsilon^2)}$.

<a id="pdf-bf2ce5422088-p180-b001"></a>
<!-- pdf-source: page=180; block=1; confidence=0.99 -->
The latter expression is less than $1$ if $D\varepsilon^2\ge c\log(Ne/K)=c\cdot(n-k)+c'$ for constants $c,c'$. This is equivalent to $d\ge\log(n-k)+2\log(1/\varepsilon)+O(1)$.

<a id="pdf-bf2ce5422088-p180-b002"></a>
<!-- pdf-source: page=180; block=2; confidence=0.98 -->
The bounds on $m$ and $d$ are each tight up to additive $O(1)$. A logarithmic seed can be exhaustively enumerated and combined by majority to simulate randomized algorithms from a weak source.

<a id="pdf-bf2ce5422088-p180-b003"></a>
<!-- pdf-source: page=180; block=3; confidence=0.98 -->
**Proposition 6.15.** Suppose randomized $A(w;r)$ computes $f$ with $\Pr[A(w;U_m)\ne f(w)]\le\gamma$, and $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$-extractor. Define $A'(w;x)=\operatorname{maj}_{y\in\{0,1\}^d}A(w;\mathrm{Ext}(x,y))$. For every $k$-source $X$, $A'(w;X)$ errs with probability at most $2(\gamma+\varepsilon)$.

<a id="pdf-bf2ce5422088-p180-b004"></a>
<!-- pdf-source: page=180; block=4; confidence=0.97 -->
**Proof.** Extractor closeness bounds the error probability of $A(w;\mathrm{Ext}(X,U_d))$ by $\gamma+\varepsilon$. If the majority over seeds is incorrect, at least half the seeds yield an error, so its probability is at most $2(\gamma+\varepsilon)$.

<a id="pdf-bf2ce5422088-p180-b005"></a>
<!-- pdf-source: page=180; block=5; confidence=0.98 -->
Enumeration costs a factor $2^d$ in running time; polynomial-time simulation with running time polynomial in $m$ calls for $d=O(\log n)$, efficiently computable $\mathrm{Ext}$, and $m=n^{\Omega(1)}$. The error can be made exponentially small using an extractor for slightly lower min-entropy (Problem 6.2).

<a id="pdf-bf2ce5422088-p181-b001"></a>
<!-- pdf-source: page=181; block=1; confidence=0.99 -->
Seeded extractors do not cover every randomness application, including cryptography; deterministic extractors for restricted sources remain of interest.

<a id="pdf-bf2ce5422088-p181-b002"></a>
<!-- pdf-source: page=181; block=2; confidence=0.99 -->
Extractors connect to hash-function families and expanding graphs.

<a id="pdf-bf2ce5422088-p181-b003"></a>
<!-- pdf-source: page=181; block=3; confidence=0.99 -->
View extractors as families of hash functions with an almost-uniform mapping property.

<a id="pdf-bf2ce5422088-p181-b004"></a>
<!-- pdf-source: page=181; block=4; confidence=0.94 -->
For a set $S\subseteq[N]$ of size $K$, a uniformly random function $h:[N]\to[M]$ (with $M\le K$) maps uniform $X\in S$ so that $(H,H(X))$ is statistically close to $(H,U_{[M]})$, where $H$ is uniform over all such functions. This motivates using smaller hash families.

<a id="pdf-bf2ce5422088-p181-b005"></a>
<!-- pdf-source: page=181; block=5; confidence=0.99 -->
**Definition 6.16.** An extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a strong $(k,\varepsilon)$-extractor if, for every $k$-source $X$, $(U_d,\mathrm{Ext}(X,U_d))$ is $\varepsilon$-close to $(U_d,U_m)$. Equivalently, $\mathrm{Ext}^{\star}(x,y)=(y,\mathrm{Ext}(x,y))$ is a standard $(k,\varepsilon)$-extractor.

<a id="pdf-bf2ce5422088-p182-b001"></a>
<!-- pdf-source: page=182; block=1; confidence=0.99 -->
The nonconstructive existence argument for Theorem 6.14 also yields strong extractors with output length approximately $k$.

<a id="pdf-bf2ce5422088-p182-b002"></a>
<!-- pdf-source: page=182; block=2; confidence=0.99 -->
**Theorem 6.17.** For every $n,k\in\mathbb{N}$ and $\varepsilon>0$, there exists a strong $(k,\varepsilon)$-extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $m=k-2\log(1/\varepsilon)-O(1)$ and $d=\log(n-k)+2\log(1/\varepsilon)+O(1)$.

<a id="pdf-bf2ce5422088-p182-b003"></a>
<!-- pdf-source: page=182; block=3; confidence=0.98 -->
A strong extractor outputs about $k$ bits because its output must be independent of the seed; this is less than the roughly $k+d$ bits for a standard extractor.

<a id="pdf-bf2ce5422088-p182-b004"></a>
<!-- pdf-source: page=182; block=4; confidence=0.99 -->
Strong extractors provide small hash-function families with the almost-uniform mapping property; pairwise-independent hashing gives the first explicit construction described here.

<a id="pdf-bf2ce5422088-p182-b005"></a>
<!-- pdf-source: page=182; block=5; confidence=0.99 -->
**Theorem 6.18 (Leftover Hash Lemma).** If $H=\{h:\{0,1\}^n\to\{0,1\}^m\}$ is pairwise independent (or $2$-universal) and $m=k-2\log(1/\varepsilon)$, then $\mathrm{Ext}(x,h)=h(x)$ is a strong $(k,\varepsilon)$-extractor. Equivalently, $(h,h(x))$ defines a standard $(k,\varepsilon)$-extractor.

<a id="pdf-bf2ce5422088-p182-b006"></a>
<!-- pdf-source: page=182; block=6; confidence=0.99 -->
Choosing $h$ requires at least $n$ random bits, while the output length $m=k-2\log(1/\varepsilon)$ is optimal up to an additive constant.

<a id="pdf-bf2ce5422088-p182-b007"></a>
<!-- pdf-source: page=182; block=7; confidence=0.99 -->
**Proof.** For an arbitrary $k$-source $X$, let $H$ be uniform in the hash family and let $d$ be the seed length. The proof bounds the collision probability of $(H,H(X))$, converts that bound to an $L_2$-distance bound from $U_d\times U_m$, then bounds statistical distance using the $L_1$/$L_2$ relation.

<a id="pdf-bf2ce5422088-p182-b008"></a>
<!-- pdf-source: page=182; block=8; confidence=0.99 -->
**Proof step (1).** Show that the collision probability of $(H,H(X))$ is close to that of $U_d\times U_m$.

<a id="pdf-bf2ce5422088-p183-b001"></a>
<!-- pdf-source: page=183; block=1; confidence=0.99 -->
**Proof steps (2)–(3).** Convert the collision-probability bound into a small squared $L_2$ distance from $U_d\times U_m$, then use statistical distance $\Delta=\tfrac12\|\cdot\|_1$ and an $L_1$ bound by $L_2$.

<a id="pdf-bf2ce5422088-p183-b002"></a>
<!-- pdf-source: page=183; block=2; confidence=0.99 -->
**Proof of (1).** By definition, $\mathrm{CP}(H,H(X))=\Pr[(H,H(X))=(H',H'(X'))]$, where $(H',X')$ is independent of and identically distributed to $(H,X)$. Since $(H,H(X))=(H',H'(X'))$ iff $H=H'$ and either $X=X'$ or $X\ne X'$ but $H(X)=H(X')$, we have
\[
\mathrm{CP}(H,H(X))=\mathrm{CP}(H)\bigl(\mathrm{CP}(X)+\Pr[H(X)=H(X')\mid X\ne X']\bigr)\le \frac1D\left(\frac1K+\frac1M\right)\le\frac{1+\varepsilon^2}{DM}.
\]
To see the penultimate inequality, note that $\mathrm{CP}(H)=1/D$ because there are $D$ hash functions, $\mathrm{CP}(X)\le1/K$ because $H_\infty(X)\ge k$, and $\Pr[H(X)=H(X')\mid X\ne X']\le1/M$ by 2-universality.

<a id="pdf-bf2ce5422088-p183-b003"></a>
<!-- pdf-source: page=183; block=3; confidence=0.99 -->
**Proof step (2).** The uniform distribution on the $DM$ pairs has collision probability $1/(DM)$, so
\[
\|(H,H(X))-U_d\times U_m\|_2^2
=\mathrm{CP}(H,H(X))-\frac1{DM}
\le\frac{\varepsilon^2}{DM}.
\]

<a id="pdf-bf2ce5422088-p183-b004"></a>
<!-- pdf-source: page=183; block=4; confidence=0.99 -->
**Proof step (3).** Since the sample space has size $DM$,
\[
\Delta((H,H(X)),U_d\times U_m)=\tfrac12\|(H,H(X))-U_d\times U_m\|_1
\le \tfrac12\sqrt{DM}\,\|(H,H(X))-U_d\times U_m\|_2
\le\varepsilon/2.
\]
Hence the argument proves a strong $(k,\varepsilon/2)$-extractor.

<a id="pdf-bf2ce5422088-p184-b001"></a>
<!-- pdf-source: page=184; block=1; confidence=0.94 -->
The preceding result also gives a strong Rényi-entropy extractor: for collision probability entropy $H_2(Z)=\log(1/\mathrm{CP}(Z))$, input entropy at least $k$ yields output entropy at least $m-\varepsilon$, or joint seed-output entropy at least $m+d-\varepsilon$ in the strong case. Pairwise-independent hashing achieves the strong form. In general, such extractors require seed length $d\geq \min\{m/2,n-k\}-O(1)$.

<a id="pdf-bf2ce5422088-p184-b002"></a>
<!-- pdf-source: page=184; block=2; confidence=0.99 -->
## 6.2.2 Extractors versus Expanders

<a id="pdf-bf2ce5422088-p184-b003"></a>
<!-- pdf-source: page=184; block=3; confidence=0.98 -->
Interpret $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ as the neighbor function of a bipartite multigraph with $N=2^n$ left vertices, $M=2^m$ right vertices, and left degree $D=2^d$. For a flat $k$-source uniform on a left set $S$ of size $K=2^k$, extraction implies $|N(S)|\geq(1-\varepsilon)M$. This is expansion for sets of size exactly $K$, motivating a weaker extractor variant.

<a id="pdf-bf2ce5422088-p185-b001"></a>
<!-- pdf-source: page=185; block=1; confidence=0.99 -->
**Definition 6.19 (Disperser).** A function $\mathrm{Disp}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$-disperser if, for every $k$-source $X$, the support of $\mathrm{Disp}(X,U_d)$ has size at least $(1-\varepsilon)2^m$.

<a id="pdf-bf2ce5422088-p185-b002"></a>
<!-- pdf-source: page=185; block=2; confidence=0.98 -->
Extractors can simulate BPP algorithms from weak randomness; dispersers analogously support RP simulation.

<a id="pdf-bf2ce5422088-p185-b003"></a>
<!-- pdf-source: page=185; block=3; confidence=0.99 -->
**Proposition 6.20.** For $K=2^k$, a function $\mathrm{Disp}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$-disperser iff its associated bipartite multigraph, with left degree $D$, is an $(=K,A)$ vertex expander for $A=(1-\varepsilon)M/K$.

<a id="pdf-bf2ce5422088-p185-b004"></a>
<!-- pdf-source: page=185; block=4; confidence=0.94 -->
Note that extractors and dispersers are interesting even when $M\ll K$, so the expansion parameter $A$ may be less than $1$. Indeed, $A<1$ is interesting for vertex expanders when the graph is highly imbalanced. Still, for an optimal extractor, we have $M=\Theta(\varepsilon^2KD)$ (because $m=k-2\log(1/\varepsilon)-\Theta(1)$), which corresponds to expansion factor $A=\Theta(\varepsilon^2D)$. An optimal disperser actually gives $A=\Theta(D/\log(1/varepsilon))$. This is smaller than the expansion factor of $D/2$ in Ramanujan graphs and $D-O(1)$ in random graphs; the reason is that those expansion factors are for small sets, whereas here we ask for sets to expand to almost the entire right-hand side.

<a id="pdf-bf2ce5422088-p185-b005"></a>
<!-- pdf-source: page=185; block=5; confidence=0.97 -->
For each left set $S\subseteq[N]$ of size $K$, extraction is equivalent to $\Delta(\mathrm{Ext}(U_S,U_{[D]}),U_{[M]})=\max_{T\subseteq[M]}|\Pr[\mathrm{Ext}(U_S,U_{[D]})\in T]-\Pr[U_{[M]}\in T]|\leq\varepsilon$.

<a id="pdf-bf2ce5422088-p186-b001"></a>
<!-- pdf-source: page=186; block=1; confidence=0.96 -->
For $S\subseteq[N]$ of size $K$ and $T\subseteq[M]$, the probability difference is $\left|\frac{e(S,T)}{|S|D}-\frac{|T|}{M}\right|=\left|\frac{e(S,T)}{ND}-\mu(S)\mu(T)\right|\leq\varepsilon\mu(S)$, where $e(S,T)$ counts edges from $S$ to $T$ and $\mu$ denotes relative set size.

<a id="pdf-bf2ce5422088-p186-b002"></a>
<!-- pdf-source: page=186; block=2; confidence=0.98 -->
**Proposition 6.21.** The function $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$-extractor iff its associated bipartite multigraph with left degree $D$ satisfies $\left|e(S,T)/(ND)-\mu(S)\mu(T)\right|\leq\varepsilon\mu(S)$ for every $S\subseteq[N]$ of size $K$ and every $T\subseteq[M]$.

<a id="pdf-bf2ce5422088-p186-b003"></a>
<!-- pdf-source: page=186; block=3; confidence=0.99 -->
The Expander Mixing Lemma states that if a graph $G$ has spectral expansion $\lambda$, then for all sets $S,T\subseteq[N]$ we have
\[
\left|\frac{e(S,T)}{ND}-\mu(S)\mu(T)\right|\le\lambda\sqrt{\mu(S)\mu(T)}.
\]
It follows that if $\lambda\sqrt{\mu(S)\mu(T)}\le\varepsilon\mu(S)$ for all $S\subseteq[N]$ of size $K$ and all $T\subseteq[N]$, then $G$ gives rise to a $(k,\varepsilon)$-extractor. It suffices for $\lambda\le\varepsilon\sqrt{K/N}$ for this to work.

<a id="pdf-bf2ce5422088-p186-b004"></a>
<!-- pdf-source: page=186; block=4; confidence=0.99 -->
To achieve $\lambda\le\varepsilon\cdot\sqrt{K/N}$, we can take an appropriate power of a constant-degree expander. Specifically, if $G_0$ is a $D_0$-regular expander on $N$ vertices with bounded second eigenvalue, we can consider the $t$th power of $G_0$, $G=G_0^t$, where $t=O(\log((1/\varepsilon)\sqrt{N/K}))=O(n-k+\log(1/\varepsilon))$. The degree of $G$ is $D=D_0^t$, so $d=\log D=O(t)$.

<a id="pdf-bf2ce5422088-p186-b005"></a>
<!-- pdf-source: page=186; block=5; confidence=0.99 -->
**Theorem 6.22.** For every $n,k\in\mathbb{N}$ and $\varepsilon>0$, there is an explicit $(k,\varepsilon)$-extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^n$ with $d=O(n-k+\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p187-b001"></a>
<!-- pdf-source: page=187; block=1; confidence=0.99 -->
Note that the seed length is significantly better than in the construction from pairwise-independent hashing when $k$ is close to $n$, say $k=n-O(n)$ (i.e., $K=N^{1-o(1)}$). The output length is $n$, which is much larger than the typical output length for extractors (usually $m\ll n$). Using a Ramanujan graph (rather than an arbitrary constant-degree expander), the seed length can be improved to $d=n-k+2\log(1/\varepsilon)+O(1)$, which yields an optimal output length $n=k+d-2\log(1/\varepsilon)-O(1)$. Another way of proving Theorem 6.22 is to use the fact that a random step on an expander decreases the $\ell_2$ distance to uniform, like in the proof of the Leftover Hash Lemma. This analysis shows that we actually get a Rényi-entropy extractor; and thus explains the large seed length $d\approx n-k$.

<a id="pdf-bf2ce5422088-p187-b002"></a>
<!-- pdf-source: page=187; block=2; confidence=0.98 -->
The comparison distinguishes expanders, measured by vertex or spectral expansion, typically of constant degree and requiring all sets of size at most K to expand, from extractors, measured by min-entropy and statistical difference, typically of logarithmic or polylogarithmic degree and requiring sets of size exactly or at least K to expand. Extractors are typically unbalanced bipartite graphs; expanders are typically balanced.

<a id="pdf-bf2ce5422088-p187-b003"></a>
<!-- pdf-source: page=187; block=3; confidence=1.00 -->
## 6.2.3 List Decoding View of Extractors

<a id="pdf-bf2ce5422088-p187-b004"></a>
<!-- pdf-source: page=187; block=4; confidence=0.95 -->
Functions Γ : [N] × [D] → [M] are analyzed through lists LISTΓ(T, ε) = {x : Prᵧ[Γ(x,y) ∈ T] > ε}, for T ⊆ [M]. For f : [M] → [0,1], the fractional-list version is LISTΓ(f, ε) = {x : Eᵧ[f(Γ(x,y))] > ε}. An extractor already has this function form, with N = 2ⁿ, D = 2ᵈ, and M = 2ᵐ.

<a id="pdf-bf2ce5422088-p188-b001"></a>
<!-- pdf-source: page=188; block=1; confidence=0.99 -->
For $f:[M]\to[0,1]$, define $\mathrm{LIST}_\Gamma(f,\varepsilon)=\{x:\mathbb{E}_y[f(\Gamma(x,y))]>\varepsilon\}$.

<a id="pdf-bf2ce5422088-p188-b002"></a>
<!-- pdf-source: page=188; block=2; confidence=0.97 -->
**Proposition 6.23.** Let Γ = Ext : [N] × [D] → [M], K = 2ᵏ ∈ ℕ, and ε ∈ [0,1]. (1) If Ext is a (k, ε)-extractor, then for every f : [M] → [0,1], |LISTΓ(f, μ(f) + ε)| < K. (2) If every T ⊆ [M] satisfies |LISTΓ(T, μ(T) + ε)| ≤ K, then Ext is a (k + log(1/ε), 2ε)-extractor.

<a id="pdf-bf2ce5422088-p188-b003"></a>
<!-- pdf-source: page=188; block=3; confidence=0.95 -->
**Proof.** If the fractional list had size at least K, let X be uniform on that list. Then X is a k-source and E[f(Ext(X,U[D]))] > μ(f) + ε = E[f(U[M])] + ε. By Problem 6.1, Ext(X,U[D]) is ε-far from U[M], contradicting that Ext is a (k, ε)-extractor.

<a id="pdf-bf2ce5422088-p188-b004"></a>
<!-- pdf-source: page=188; block=4; confidence=0.97 -->
**Proof step.** For any (k + log(1/ε))-source X, it suffices to show that for every T ⊆ [M], Pr[Ext(X,U[D]) ∈ T] ≤ μ(T) + 2ε.

<a id="pdf-bf2ce5422088-p189-b001"></a>
<!-- pdf-source: page=189; block=1; confidence=0.92 -->
**Proof step.** For arbitrary T ⊆ [M], split according to whether X lies in LIST(T, μ(T) + ε). The list assumption and the source min-entropy give Pr[Ext(X,U[D]) ∈ T] ≤ |LIST(T, μ(T)+ε)|·2⁻⁽ᵏ⁺ˡᵒᵍ⁽¹/ε⁾⁾ + μ(T)+ε ≤ K·2⁻⁽ᵏ⁺ˡᵒᵍ⁽¹/ε⁾⁾ + μ(T)+ε = μ(T)+2ε.

<a id="pdf-bf2ce5422088-p189-b002"></a>
<!-- pdf-source: page=189; block=2; confidence=0.98 -->
The proposition does not give an exact list-decoding characterization of extractors, as the two parts are not exactly converses of each other. One difference is the extra $\log(1/\varepsilon)$ bits of entropy and the factor of $2$ in $\varepsilon$ appearing in Part 6.23. These are typically insignificant differences for extractors; indeed even an optimal extractor loses $\Theta(\log(1/\varepsilon))$ bits of entropy (cf. Theorem 6.14). A second difference is that Part 6.23 shows that extractors imply bounds on $|\mathrm{LIST}_\Gamma(f,\mu(f)+\varepsilon)|$ even for fractional functions $f$, whereas Part 6.23 only requires bounds on $|\mathrm{LIST}_\Gamma(T,\mu(T)+\varepsilon)|$ to deduce the extractor property. This only makes the result stronger, and indeed we will utilize this below. Notice that the conditions characterizing extractors here are identical to the ones characterizing averaging samplers in Proposition 5.30. Actually, the condition in Part 6.23 is the one characterizing averaging samplers, whereas the condition in Part 6.23 is the one characterizing boolean averaging samplers.

<a id="pdf-bf2ce5422088-p189-b003"></a>
<!-- pdf-source: page=189; block=3; confidence=0.99 -->
**Corollary 6.24.** Let $\mathrm{Ext}:[N]\times[D]\to[M]$ and $\mathrm{Samp}:[N]\to[M]^D$ be such that $\mathrm{Ext}(x,y)=\mathrm{Samp}(x)_y$. Then:

(1) If $\mathrm{Ext}$ is a $(k,\varepsilon)$ extractor, then $\mathrm{Samp}$ is a $(K/N,\varepsilon)$ averaging sampler, where $K=2^k$.

(2) If $\mathrm{Samp}$ is a $(K/N,\varepsilon)$ boolean averaging sampler, then $\mathrm{Ext}$ is a $(k+\log(1/\varepsilon),2\varepsilon)$ extractor.

(3) If $\mathrm{Samp}$ is a $(\delta,\varepsilon)$ boolean averaging sampler, then $\mathrm{Samp}$ is a $(\delta/\varepsilon,2\varepsilon)$ averaging sampler.

<a id="pdf-bf2ce5422088-p190-b001"></a>
<!-- pdf-source: page=190; block=1; confidence=0.99 -->
### 6.2 Connections to Other Pseudorandom Objects

<a id="pdf-bf2ce5422088-p190-b002"></a>
<!-- pdf-source: page=190; block=2; confidence=0.92 -->
Extractor and averaging-sampler formulations differ mainly in perspective: sampler error is $delta=K/N=2^k/2^n$, while extractors emphasize the min-entropy threshold $k$. The sampler view is useful when $delta$ is relatively large versus $1/N$; the extractor view is useful near $1/N$. When $k=o(n)$, the corresponding sampler error is $delta=2^{-(1-o(1))n}$, so each of its $n$ random bits nearly halves the error.

<a id="pdf-bf2ce5422088-p190-b003"></a>
<!-- pdf-source: page=190; block=3; confidence=0.98 -->
Strong extractors are closely related to list-decodable codes when the output alphabet is small.

<a id="pdf-bf2ce5422088-p190-b004"></a>
<!-- pdf-source: page=190; block=4; confidence=0.99 -->
**Proposition 6.25.** Suppose $\mathrm{Ext}:[N]\times[D]\to[M]$ and $\mathrm{Enc}:[N]	o[M]^D$ satisfy $\mathrm{Ext}(x,y)=\mathrm{Enc}(x)_y$, and let $K=2^k\in\mathbb N$. (1) If $\mathrm{Ext}$ is a strong $(k,\varepsilon)$ extractor, then $\mathrm{Enc}$ is $(1-1/M-\varepsilon,K)$ list-decodable. (2) If $\mathrm{Enc}$ is $(1-1/M-\varepsilon,K)$ list-decodable, then $\mathrm{Ext}$ is a strong $(k+\log(1/\varepsilon),M\varepsilon)$ extractor.

<a id="pdf-bf2ce5422088-p190-b005"></a>
<!-- pdf-source: page=190; block=5; confidence=0.99 -->
**Proof.** (1) Follows from Corollaries 5.31 and 6.24.

(2) Let $X$ be a $(k+\log(1/\varepsilon))$-source and $Y=U_{[D]}$. Then the statistical difference between $(Y,\mathrm{Ext}(X,Y))$ and $Y\times U_{[M]}$ equals
\[
\Delta((Y,\mathrm{Ext}(X,Y)),Y\times U_{[M]})=\mathbb{E}_{y\leftarrow Y}[\Delta(\mathrm{Ext}(X,y),U_{[M]})]=\mathbb{E}_{y\leftarrow Y}[\Delta(\mathrm{Enc}(X)_y,U_{[M]})]
\le \frac M2\mathbb{E}_{y\leftarrow Y}\left[\max_z\Pr[\mathrm{Enc}(X)_y=z]-1/M\right],
\]
where the last inequality follows from the $\ell_1$ formulation of statistical difference.

<a id="pdf-bf2ce5422088-p191-b001"></a>
<!-- pdf-source: page=191; block=1; confidence=0.99 -->
So if we define $r\in[M]^D$ by setting $r_y$ to be the value $z$ maximizing $\Pr[\mathrm{Enc}(X)_y=z]-1/M$, we have:
\[
\begin{aligned}
\Delta((Y,\mathrm{Ext}(X,Y)),Y\times U_{[M]})
&\le \frac M2\cdot\left(\Pr[(Y,\mathrm{Enc}(X)_Y)\in T_r]-1/M\right),\\
&\le \frac M2\cdot\left(\Pr[X\in\mathrm{LIST}(T_r,1/M+\varepsilon)]+\varepsilon\right),\\
&\le \frac M2\cdot\left(2^{-(k+\log(1/\varepsilon))}\cdot K+\varepsilon\right),\\
&\le M\cdot\varepsilon.
\end{aligned}
\]

<a id="pdf-bf2ce5422088-p191-b002"></a>
<!-- pdf-source: page=191; block=2; confidence=0.96 -->
The parameter relationship in Proposition 6.25 worsens rapidly as output alphabet size grows, though the list-decoding interpretation from Proposition 6.23 remains useful.

<a id="pdf-bf2ce5422088-p191-b003"></a>
<!-- pdf-source: page=191; block=3; confidence=0.99 -->
### 6.3 Constructing Extractors

<a id="pdf-bf2ce5422088-p191-b004"></a>
<!-- pdf-source: page=191; block=4; confidence=0.97 -->
Earlier constructions via universal hashing and spectral expanders do not attain optimal seed length or yield a polynomial-time simulation of BPP from weak randomness. Better constructions can extract a constant fraction of min-entropy with logarithmic seed, or all min-entropy with polylogarithmic seed.

<a id="pdf-bf2ce5422088-p191-b005"></a>
<!-- pdf-source: page=191; block=5; confidence=0.99 -->
### 6.3.1 Block Sources

<a id="pdf-bf2ce5422088-p191-b006"></a>
<!-- pdf-source: page=191; block=6; confidence=0.97 -->
The section introduces a structured source model to facilitate extractor constructions.

<a id="pdf-bf2ce5422088-p192-b001"></a>
<!-- pdf-source: page=192; block=1; confidence=0.99 -->
**Definition 6.26.** A tuple-valued random variable $X=(X_1,\ldots,X_t)$ is a $(k_1,\ldots,k_t)$ block source if for each $i$ and every preceding block assignment $x_1,\ldots,x_{i-1}$, the conditional variable $X_i\mid X_1=x_1,\ldots,X_{i-1}=x_{i-1}$ is a $k_i$-source. When all $k_i=k$, it is called a $t\times k$ block source.

<a id="pdf-bf2ce5422088-p192-b002"></a>
<!-- pdf-source: page=192; block=2; confidence=0.99 -->
A $(k_1,k_2,\ldots,k_t)$ block source is also a $(k_1+\cdots+k_t)$-source, but it comes with additional structure—each block is guaranteed to contribute some min-entropy. Thus, extracting randomness from block sources is an easier task than extracting from general sources. If $X\in\mathrm{UnpredBits}_{n,\delta}$ is broken into $t$ blocks of length $\ell=n/t$, then the result is a $t\times\delta'\ell$ block source, where $\delta'=\log(1/(1-\delta))$.

<a id="pdf-bf2ce5422088-p192-b003"></a>
<!-- pdf-source: page=192; block=3; confidence=0.96 -->
For two blocks, extract nearly uniform bits from the later block, which are essentially independent of the earlier block, and use them as the earlier block's extractor seed.

<a id="pdf-bf2ce5422088-p192-b004"></a>
<!-- pdf-source: page=192; block=4; confidence=0.99 -->
**Lemma 6.27.** Let $\mathrm{Ext}_1:\{0,1\}^{n_1}\times\{0,1\}^{d_1}\to\{0,1\}^{m_1}$ be a $(k_1,\varepsilon_1)$-extractor and $\mathrm{Ext}_2:\{0,1\}^{n_2}\times\{0,1\}^{d_2}\to\{0,1\}^{m_2}$ a $(k_2,\varepsilon_2)$-extractor, with $m_2\ge d_1$. Define $\mathrm{Ext}'((x_1,x_2),y_2)=(\mathrm{Ext}_1(x_1,y_1),z_2)$, where $(y_1,z_2)$ splits $\mathrm{Ext}_2(x_2,y_2)$ into a prefix of length $d_1$ and a suffix of length $m_2-d_1$. For every $(k_1,k_2)$ block source $X=(X_1,X_2)$ on $\{0,1\}^{n_1}\times\{0,1\}^{n_2}$, the output $\mathrm{Ext}'(X,U_{d_2})$ is $(\varepsilon_1+\varepsilon_2)$-close to $U_{m_1}\times U_{m_2-d_1}$.

<a id="pdf-bf2ce5422088-p193-b001"></a>
<!-- pdf-source: page=193; block=1; confidence=0.99 -->
**Proof.** Since $X_2$ is a $k_2$-source conditioned on any value of $X_1$ and $\mathrm{Ext}_2$ is a $(k_2,\varepsilon_2)$-extractor, it follows that $(X_1,Y_1,Z_2)=(X_1,\mathrm{Ext}_2(X_2,U_{d_2}))$ is $\varepsilon_2$-close to $(X_1,U_{m_2})=(X_1,U_{d_1},U_{m_2-d_1})$. Thus, $(\mathrm{Ext}_1(X_1,Y_1),Z_2)$ is $\varepsilon_2$-close to $(\mathrm{Ext}_1(X_1,U_{d_1}),U_{m_2-d_1})$, which is $\varepsilon_1$-close to $(U_{m_1},U_{m_2-d_1})$ because $X_1$ is a $k_1$-source and $\mathrm{Ext}_1$ is a $(k_1,\varepsilon_1)$-extractor. By the triangle inequality, $\mathrm{Ext}'(X,U_{d_2})=(\mathrm{Ext}_1(X_1,Y_1),Z_2)$ is $(\varepsilon_1+\varepsilon_2)$-close to $(U_{m_1},U_{m_2-d_1})$.

<a id="pdf-bf2ce5422088-p193-b002"></a>
<!-- pdf-source: page=193; block=2; confidence=0.96 -->
The construction combines extraction across blocks with seed length determined by $\mathrm{Ext}_2$; it may be shorter than $\mathrm{Ext}_1$'s seed. The composition extends to multiple blocks.

<a id="pdf-bf2ce5422088-p193-b003"></a>
<!-- pdf-source: page=193; block=3; confidence=0.98 -->
**Lemma 6.28.** For $i=1,\ldots,t$, let $\mathrm{Ext}_i:\{0,1\}^{n_i}\times\{0,1\}^{d_i}\to\{0,1\}^{m_i}$ be a $(k_i,\varepsilon_i)$-extractor, with $m_i\ge d_{i-1}$ and $d_0=0$. For input $(x_1,\ldots,x_t)$ and seed $y_t$, recursively, for $i=t,\ldots,1$, partition $\mathrm{Ext}_i(x_i,y_i)$ into a $d_{i-1}$-bit prefix $y_{i-1}$ and an $(m_i-d_{i-1})$-bit suffix $z_i$; output $(z_1,\ldots,z_t)$. For every $(k_1,\ldots,k_t)$ block source $X$, $\mathrm{Ext}^{\star}(X,U_{d_t})$ is $\varepsilon$-close to $U_m$, where $\varepsilon=\sum_{i=1}^t\varepsilon_i$ and $m=\sum_{i=1}^t(m_i-d_{i-1})$. The construction preserves strongness when each component is strong; if all $d_i$ are equal, the same seed is used for every block.

<a id="pdf-bf2ce5422088-p193-b004"></a>
<!-- pdf-source: page=193; block=4; confidence=0.94 -->
The text begins an application of block composition to simulate BPP from unpredictable-bit sources; the parameter calculations continue on the next page.

<a id="pdf-bf2ce5422088-p194-b001"></a>
<!-- pdf-source: page=194; block=1; confidence=0.99 -->
Blocks of length $\ell$ yield a $t\times k$ block source for $t=n/\ell$, $k=\delta'\ell$, and $\delta'=\log(1/(1-\delta))$. Suppose that $\delta$ is a constant. Set $\ell=(10/\delta')\log n$, so that $X$ is a $t\times k$ block source for $k=10\log n$, and define $\varepsilon=n^{-2}$. Letting $\mathrm{Ext}:{0,1}^\ell\times{0,1}^d\to{0,1}^{d+m}$ be the $(k,\varepsilon)$ extractor using universal hash functions (Theorem 6.18), we have $d=O(\ell)=O(\log n)$ and $m=k-2\log\frac1\varepsilon-O(1)>k/2$. Composing $\mathrm{Ext}$ with itself $t$ times as in Lemma 6.27, we obtain $\mathrm{Ext}' : {0,1}^{t\ell}\times{0,1}^d\to{0,1}^{d+t\cdot m}$ such that $\mathrm{Ext}'(X,U_d)$ is $\varepsilon'=1/n$-close to uniform. Specifically, $\mathrm{Ext}'((x_1,\ldots,x_t),h)=(h,h(x_1),\ldots,h(x_t))$. This tells us that $\mathrm{Ext}'$ essentially extracts half of the min-entropy from $X$, given a random seed of logarithmic length.

<a id="pdf-bf2ce5422088-p194-b002"></a>
<!-- pdf-source: page=194; block=2; confidence=0.99 -->
**Theorem 6.29.** For every constant $\delta>0$, BPP can be simulated using an unpredictable-bit source with parameter $\delta$: for each $L\in\mathrm{BPP}$ and constant $\delta>0$, there exist a polynomial-time algorithm $A$ and polynomial $q$ such that for every input $w$ and source $X\in\mathrm{UnpredBits}_{q(|w|),\delta}$, $A(w;X)$ errs with probability at most $1/|w|$.

<a id="pdf-bf2ce5422088-p194-b003"></a>
<!-- pdf-source: page=194; block=3; confidence=0.99 -->
## 6.3.2 Reducing General Sources to Block Sources

<a id="pdf-bf2ce5422088-p194-b004"></a>
<!-- pdf-source: page=194; block=4; confidence=0.94 -->
One proposed reduction samples a (pseudo)random subset $S$ of the bits of a $k$-source $X$ of length $n$, and sets $W=X|_S$. For $|S|=\ell$, one expects about $\delta\ell$ min-entropy in $W$ when $k=\delta n$; revealing $W$ costs at most $\ell$ bits, so entropy may remain in $X$. This can make $(W,X)$ a block source for suitable sampling schemes and motivates Lemma 6.30.

<a id="pdf-bf2ce5422088-p195-b001"></a>
<!-- pdf-source: page=195; block=1; confidence=0.93 -->
The subset-sampling method and recursive variants can yield extractors. Conditioning on a short-support variable loses at most its support-length bound in min-entropy, formalized by the next lemma. The Shannon entropy analogy is $H_{\rm Sh}(X\mid W)=H_{\rm Sh}(W,X)-H_{\rm Sh}(W)$, with conditional entropy defined by averaging $H_{\rm Sh}(X\mid W=w)$ over $w$; unlike that identity's direct bound, min-entropy requires small support and incurs an additional $\log(1/\varepsilon)$ loss.

<a id="pdf-bf2ce5422088-p195-b002"></a>
<!-- pdf-source: page=195; block=2; confidence=0.99 -->
**Lemma 6.30 (chain rule for min-entropy).** If $(W,X)$ is jointly distributed and is a $k$-source, and $|\operatorname{Supp}(W)|\le 2^{\ell}$, then for every $\varepsilon>0$, with probability at least $1-\varepsilon$ over $w\leftarrow W$, the conditional distribution $X\mid W=w$ is a $(k-\ell-\log(1/\varepsilon))$-source.

<a id="pdf-bf2ce5422088-p195-b003"></a>
<!-- pdf-source: page=195; block=3; confidence=0.97 -->
The proof of Lemma 6.30 is assigned as Problem 6.1. The text notes that a suitable conditional min-entropy notion can avoid the extra $\log(1/\varepsilon)$ loss (Problems 6.7 and 6.8).

<a id="pdf-bf2ce5422088-p195-b004"></a>
<!-- pdf-source: page=195; block=4; confidence=0.95 -->
An alternative strategy is to first convert a general source into one of high min-entropy rate; any source with rate greater than $1/2$ is close to a block source.

<a id="pdf-bf2ce5422088-p195-b005"></a>
<!-- pdf-source: page=195; block=5; confidence=0.99 -->
**Lemma 6.31.** If $X$ is an $(n-\Delta)$-source of length $n$ and is partitioned as $(X_1,X_2)$ into blocks of lengths $n_1,n_2$, then for every $\varepsilon>0$, $(X_1,X_2)$ is $\varepsilon$-close to some $(n_1-\Delta,\;n_2-\Delta-\log(1/\varepsilon))$ block source.

<a id="pdf-bf2ce5422088-p195-b006"></a>
<!-- pdf-source: page=195; block=6; confidence=0.99 -->
For $\Delta=\alpha n$ with constant $\alpha<1/2$ and $n_1=n_2=n/2$, each block contributes at least $(1/2-\alpha)n$ bits of min-entropy. Proofs of Lemmas 6.30 and 6.31 are assigned as Problem 6.1.

<a id="pdf-bf2ce5422088-p196-b001"></a>
<!-- pdf-source: page=196; block=1; confidence=1.00 -->
Section heading introducing condensers as a method for increasing source min-entropy rate.

<a id="pdf-bf2ce5422088-p196-b002"></a>
<!-- pdf-source: page=196; block=2; confidence=0.99 -->
A condenser can raise min-entropy rate, simplifying extraction; when its target entropy equals output length, it is an extractor. View `Con` as the neighbor function of a bipartite multigraph with `N=2^n` left vertices, degree `D=2^d`, and `M=2^m` right vertices.

<a id="pdf-bf2ce5422088-p196-b003"></a>
<!-- pdf-source: page=196; block=3; confidence=0.99 -->
**Definition 6.32.** A map `Con:{0,1}^n×{0,1}^d→{0,1}^m` is a `k→_ε k'` condenser if for every `k`-source `X`, `Con(X,U_d)` is `ε`-close to some `k'`-source. It is lossless when `k'=k+d`.

<a id="pdf-bf2ce5422088-p196-b004"></a>
<!-- pdf-source: page=196; block=4; confidence=1.00 -->
Lossless condensing is characterized by vertex expansion close to the left degree.

<a id="pdf-bf2ce5422088-p196-b005"></a>
<!-- pdf-source: page=196; block=5; confidence=0.99 -->
**Proposition 6.33.** Let \(n,d,m\in\mathbb N\), \(K=2^k\in\mathbb N\), and \(\varepsilon>0\). A function \(\mathrm{Con}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m\) is a \(k\xrightarrow{\varepsilon} k+d\) lossless condenser if and only if the corresponding bipartite multigraph \(G=([N],[M],E)\) of left degree \(D\) is a \((=K,(1-\varepsilon)D)\) vertex expander.

<a id="pdf-bf2ce5422088-p196-b006"></a>
<!-- pdf-source: page=196; block=6; confidence=0.99 -->
**Proof.** \(\Rightarrow\): Let \(S\subseteq[N]\) be any set of size \(K\). Then \(U_S\) is a \(k\)-source, so \(\mathrm{Con}(U_S,U_d)\) is \(\varepsilon\)-close to a \((k+d)\)-source. This implies that \(|\mathrm{Supp}(\mathrm{Con}(U_S,U_d))|\ge (1-\varepsilon)\cdot 2^{k+d}\). Noting that \(\mathrm{Supp}(\mathrm{Con}(U_S,U_d))=N(S)\) completes the proof.\n\n\(\Leftarrow\): By Lemma 6.10, it suffices to prove that for every subset \(S\subseteq[N]\) of size \(K\), \(\mathrm{Con}(U_S,U_d)\) is \(\varepsilon\)-close to a \((k+d)\)-source. By expansion, we know that \(|N(S)|\ge (1-\varepsilon)\cdot KD\). Since there are only \(KD\) edges leaving \(S\), by redirecting \(\varepsilon KD\) of the edges, we can ensure that they all go to \(KD\) distinct vertices in \([M]\). The uniform distribution on these \(KD\) vertices is a \((k+d)\)-source that is \(\varepsilon\)-close to \(\mathrm{Con}(U_S,U_d)\).

<a id="pdf-bf2ce5422088-p197-b001"></a>
<!-- pdf-source: page=197; block=1; confidence=0.99 -->
Vertex expansion alone guarantees support size, but expansion nearly equal to degree also forces the random-neighbor distribution to be nearly flat.

<a id="pdf-bf2ce5422088-p197-b002"></a>
<!-- pdf-source: page=197; block=2; confidence=0.99 -->
**Theorem 6.34.** For every constant `α>0`, positive integers `n≥k`, and `ε>0`, there is an explicit lossless `k→_ε k+d` condenser `Con:{0,1}^n×{0,1}^d→{0,1}^m` with `d=O(log n+log(1/ε))` and `m=(1+α)k+O(log(n/ε))`.

<a id="pdf-bf2ce5422088-p197-b003"></a>
<!-- pdf-source: page=197; block=3; confidence=0.98 -->
Taking `α` small gives output entropy rate near one; combining this condenser with the high-rate extractor from Problem 6.5 yields `Ω(k)` almost-uniform bits with constant error and seed length `O(log n)`. The text notes that nonconstructive lossless condensers can have `m=k+d+log(1/ε)+O(1)`, and poses the following explicit-construction problem.

<a id="pdf-bf2ce5422088-p197-b004"></a>
<!-- pdf-source: page=197; block=4; confidence=0.99 -->
**Open Problem 6.35.** Construct explicitly a `k→_ε k+d` lossless condenser `Con:{0,1}^n×{0,1}^d→{0,1}^m` with `d=O(log n)`, `m=k+d+O(1)`, and `ε=0.01`.

<a id="pdf-bf2ce5422088-p198-b001"></a>
<!-- pdf-source: page=198; block=1; confidence=0.99 -->
Such a condenser, followed by spectral-expander extractors (Theorem 6.22), would give extractors recovering all but `O(1)` bits of min-entropy.

<a id="pdf-bf2ce5422088-p198-b002"></a>
<!-- pdf-source: page=198; block=2; confidence=1.00 -->
Section introduces an optimal-up-to-constant-factors extractor using condensing and block-source extraction.

<a id="pdf-bf2ce5422088-p198-b003"></a>
<!-- pdf-source: page=198; block=3; confidence=0.99 -->
**Theorem 6.36.** For positive integers `n≥k` and `ε>0`, there is an explicit `(k,ε)` extractor `Ext:{0,1}^n×{0,1}^d→{0,1}^m` with `m≥k/2` and `d=O(log(n/ε))`.

<a id="pdf-bf2ce5422088-p198-b004"></a>
<!-- pdf-source: page=198; block=4; confidence=1.00 -->
The construction uses a building block from Problem 6.9.

<a id="pdf-bf2ce5422088-p198-b005"></a>
<!-- pdf-source: page=198; block=5; confidence=0.99 -->
**Lemma 6.37.** For every constant `t>0`, positive integers `n≥k`, and `ε>0`, there is an explicit `(k,ε)` extractor `Ext:{0,1}^n×{0,1}^d→{0,1}^m` with `m≥k/2` and `d=k/t+O(log(n/ε))`.

<a id="pdf-bf2ce5422088-p198-b006"></a>
<!-- pdf-source: page=198; block=6; confidence=0.96 -->
The lemma permits seed length smaller than output length by an arbitrarily large constant factor. Used as `Ext₂` in Lemma 6.27's block-source composition, it makes the composed seed (the seed of `Ext₂`) smaller by a constant factor than `Ext₁`'s seed, which can equal `Ext₂`'s output length `m₂=d₁`.

<a id="pdf-bf2ce5422088-p198-b007"></a>
<!-- pdf-source: page=198; block=7; confidence=0.99 -->
For small min-entropies \(k=O(\log(n/\varepsilon))\), the extractor we want is already given by Lemma 6.37 with seed length \(d\) smaller than the output length \(m\) by any constant factor. (If we allow \(d\ge m\), then extraction is trivial—just output the seed.) Thus, our goal will be to recursively construct extractors for large min-entropies using extractors for smaller min-entropies. Of course, if \(\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m\) is a \((k_0,\varepsilon)\)

<a id="pdf-bf2ce5422088-p199-b001"></a>
<!-- pdf-source: page=199; block=1; confidence=0.99 -->
For a target min-entropy $k$, repeated extraction can increase the output beyond the initial $k_0/2$ bits; block-source extraction is used to control the resulting seed-length growth.

<a id="pdf-bf2ce5422088-p199-b002"></a>
<!-- pdf-source: page=199; block=2; confidence=0.99 -->
**Lemma 6.38.** Suppose $\mathrm{Ext}_1:\{0,1\}^n\times\{0,1\}^{d_1}\to\{0,1\}^{m_1}$ is a $(k_1,\varepsilon_1)$ extractor and $\mathrm{Ext}_2:\{0,1\}^n\times\{0,1\}^{d_2}\to\{0,1\}^{m_2}$ is a $(k_2,\varepsilon_2)$ extractor, where $k_2=k_1-m_1-\log(1/\varepsilon_3)$. Then $\mathrm{Ext}^\star(x,(y_1,y_2))=(\mathrm{Ext}_1(x,y_1),\mathrm{Ext}_2(x,y_2))$, with seed length $d_1+d_2$ and output length $m_1+m_2$, is a $(k_1,\varepsilon_1+\varepsilon_2+\varepsilon_3)$ extractor.

<a id="pdf-bf2ce5422088-p199-b003"></a>
<!-- pdf-source: page=199; block=3; confidence=0.97 -->
**Proof.** By Lemma 6.30, after conditioning a $k_1$-source $X$ on $W=\mathrm{Ext}_1(X,U_{d_1})$, its min-entropy remains at least $k_1-m_1-\log(1/\varepsilon_3)=k_2$ except with probability $\varepsilon_3$. Applying $\mathrm{Ext}_2$ extracts another $m_2$ nearly uniform bits; the errors sum to at most $\varepsilon_1+\varepsilon_2+\varepsilon_3$.

<a id="pdf-bf2ce5422088-p199-b004"></a>
<!-- pdf-source: page=199; block=4; confidence=0.99 -->
To see how we might apply this, consider setting \(k_1=0.8k\) and \(m_1=k_1/2\), \(\varepsilon_1=\varepsilon_2=\varepsilon_3=\varepsilon\ge 2^{-0.1k}\), \(k_2=k_1-m_1-\log(1/\varepsilon_3)\in[0.3k,0.4k]\), and \(m_2=k_2/2\). Then we obtain a \((k,3\varepsilon)\) extractor \(\mathrm{Ext}'\) with output length \(m=m_1+m_2>k/2\) from two extractors for min-entropies \(k_1,k_2\) that are smaller than \(k\) by a constant factor, and we can hope to construct the latter two extractors recursively via the same construction.

<a id="pdf-bf2ce5422088-p200-b001"></a>
<!-- pdf-source: page=200; block=1; confidence=0.99 -->
The recursive construction tolerates constant-factor error growth over logarithmically many levels by choosing polynomially small base error. Its proof first reduces seed length via block-source extraction, then raises output length using Lemma 6.38.

<a id="pdf-bf2ce5422088-p200-b002"></a>
<!-- pdf-source: page=200; block=2; confidence=0.98 -->
**Proof of Theorem 6.36.** Fix \(n\in\mathbb N\) and \(\varepsilon_0>0\). Set \(d=c\log(n/\varepsilon_0)\) for an error parameter \(\varepsilon_0\) and a sufficiently large constant \(c\) to be determined in the proof below. (To avoid ambiguity, we will keep the dependence on \(c\) explicit throughout the proof, and all big-Oh notation hides universal constants independent of \(c\).) For \(k\in[0,n]\), let \(i(k)\) be the smallest nonnegative integer \(i\) such that \(k\le 2^i\cdot 8d\). This will be the level of recursion in which we handle min-entropy \(k\); note that \(i(k)\le\log k\le\log n\).\n\nFor every \(k\in[0,n]\), we will construct an explicit \(\mathrm{Ext}_k:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^{k/2}\) that is a \((k,\varepsilon_{i(k)})\) extractor, for an appropriate sequence \(\varepsilon_0\le\varepsilon_1\le\varepsilon_2\cdots\). Note that we require the seed length to remain \(d\) and the fraction of min-entropy extracted to remain \(1/2\) for all values of \(k\). The construction will be by induction on \(i(k)\).

<a id="pdf-bf2ce5422088-p200-b003"></a>
<!-- pdf-source: page=200; block=3; confidence=0.97 -->
If $i(k)=0$ (so $k\le 8d$), construct $\mathrm{Ext}_k$ from Lemma 6.37 with parameter $t=9$ and sufficiently large $c$.

<a id="pdf-bf2ce5422088-p200-b004"></a>
<!-- pdf-source: page=200; block=4; confidence=0.97 -->
For $i(k)\ge1$, on a $k$-source $X$ of length $n$: (1) apply the condenser of Theorem 6.34 to obtain $X'$ that is $\varepsilon_0$-close to a $k$-source of length $(9/8)k+O(\log(n/\varepsilon_0))$, using $O(\log(n/\varepsilon_0))$ seed bits; (2) split $X'$ into equal halves $(X_1,X_2)$. By Lemma 6.31 this pair is $2\varepsilon_0$-close to a $2\times k'$ block source, where $k'=k/2-k/8-O(\log(n/\varepsilon_0))$.

<a id="pdf-bf2ce5422088-p201-b001"></a>
<!-- pdf-source: page=201; block=1; confidence=0.96 -->
The chosen $k'$ satisfies $i(k')<i(k)$ and, since $i(k)\ge1$, $k'\ge3d-O(\log(n/\varepsilon_0))\ge2d$ for sufficiently large $c$.

<a id="pdf-bf2ce5422088-p201-b002"></a>
<!-- pdf-source: page=201; block=2; confidence=0.99 -->
(3) Now we apply block-source extraction as in Lemma 6.27. We take \(\mathrm{Ext}_2\) to be a \((2d,\varepsilon_0)\) extractor from Lemma 6.37 with parameter \(t=16\), which will give us \(m_2=d\) output bits using a seed of length \(d_2=(2d)/16+O(\log(n/\varepsilon_0))\). For \(\mathrm{Ext}_1\), we use our recursively constructed \(\mathrm{Ext}_{k'}\), which has seed length \(d\), error \(\varepsilon_{i(k')}\), and output length \(k'/2\ge k/6\) (where the latter inequality holds for a sufficiently large choice of the constant \(c\), because \(k>8d>8c\log(1/\varepsilon_0)\)).

<a id="pdf-bf2ce5422088-p201-b003"></a>
<!-- pdf-source: page=201; block=3; confidence=0.99 -->
With one application of the extractor above, we extract at least \(m_1=k/6\) bits of the source min-entropy. Then with another application of the extractor above for min-entropy threshold \(k_2=k-m_1-\log(1/\varepsilon_0)=5k/6-\log(1/\varepsilon_0)\), by Lemma 6.38, we extract another \((5k/6-\log(1/\varepsilon_0))/6\) bits and so on. After four applications, we have extracted all but \((5/6)^4\cdot k+O(\log(1/\varepsilon_0))\le k/2\) bits of the min-entropy. Our seed length is then \(4\cdot(d/8+O(\log(n/\varepsilon_0)))\le d\) and the total error is \(\varepsilon_{i(k)}=O(\varepsilon_{i(k)-1})\).\n\nSolving the recurrence for the error, we get \(\varepsilon_i=2^{O(i)}\cdot\varepsilon_0\le\mathrm{poly}(n)\cdot\varepsilon_0\), so we can obtain error \(\varepsilon\) by setting \(\varepsilon_0=\varepsilon/\mathrm{poly}(n)\).

<a id="pdf-bf2ce5422088-p201-b004"></a>
<!-- pdf-source: page=201; block=4; confidence=0.99 -->
As far as explicitness, we note that computing \(\mathrm{Ext}_k\) consists of four evaluations of our condenser from Theorem 6.34, four evaluations of \(\mathrm{Ext}_{k'}\) for values of \(k'\) such that \(i(k')<(i(k)-1)\), four evaluations of the explicit extractor from Lemma 6.37, and simple string manipulations that can be done in time \(\mathrm{poly}(n,d)\). Thus, the total computation time is at most \(4^{i(k)}\cdot\mathrm{poly}(n,d)=\mathrm{poly}(n,d)\).

<a id="pdf-bf2ce5422088-p202-b001"></a>
<!-- pdf-source: page=202; block=1; confidence=1.00 -->
## 6.3 Constructing Extractors

<a id="pdf-bf2ce5422088-p202-b002"></a>
<!-- pdf-source: page=202; block=2; confidence=1.00 -->
**Corollary 6.39.** For every constant $\alpha>0$, integers $n\ge 0$, $0\le k\le n$, and $\varepsilon>0$, there is an explicit $(k,\varepsilon)$-extractor $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $m\ge(1-\alpha)k$ and $d=O(\log(n/\varepsilon))$.

<a id="pdf-bf2ce5422088-p202-b003"></a>
<!-- pdf-source: page=202; block=3; confidence=0.99 -->
**Corollary 6.40.** For integers $n\ge0$, $0\le k\le n$, and $\varepsilon>0$, there is an explicit $(k,\varepsilon)$-extractor $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $m=k-O(\log(1/\varepsilon))$ and $d=O(\log k\cdot\log(n/\varepsilon))$.

<a id="pdf-bf2ce5422088-p202-b004"></a>
<!-- pdf-source: page=202; block=4; confidence=0.98 -->
The constructions can be adapted to strong extractors with the stated output lengths, avoiding seed-entropy loss in Corollary 6.40.

<a id="pdf-bf2ce5422088-p202-b005"></a>
<!-- pdf-source: page=202; block=5; confidence=0.96 -->
**Table 6.2. Parameters for some constructions of \((k,0.01)\) extractors.**\n\n| Method | Seed Length \(d\) | Output Length \(m\) |\n|---|---:|---:|\n| Optimal and Nonconstructive | \(\log(n-k)+O(1)\) | \(k+d-O(1)\) |\n| Necessary for BPP |  | \(k^{\Omega(1)}\) |\n| Simulation | \(O(\log n)\) |  |\n| Spectral Expanders | \(O(n-k)\) | \(n\) |\n| Pairwise Independent Hashing | \(O(n)\) | \(k+d-O(1)\) |\n| Corollary 6.39 | \(O(\log n)\) | \((1-\gamma)k\), any constant \(\gamma>0\) |\n| Corollary 6.40 | \(O(\log^2 n)\) | \(k-O(1)\) |

<a id="pdf-bf2ce5422088-p202-b006"></a>
<!-- pdf-source: page=202; block=6; confidence=0.98 -->
Theorem 6.36 and Corollary 6.39 achieve constant-factor optimality in seed and output lengths; obtaining additive-constant optimality in one while retaining constant-factor optimality in the other remains open.

<a id="pdf-bf2ce5422088-p202-b007"></a>
<!-- pdf-source: page=202; block=7; confidence=1.00 -->
**Open Problem 6.41.** Construct an explicit $(k,0.01)$-extractor $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $d=O(\log n)$ and $m=k+d-O(1)$.

<a id="pdf-bf2ce5422088-p203-b001"></a>
<!-- pdf-source: page=203; block=1; confidence=0.98 -->
Using the condenser of Theorem 6.34 reduces the target to high min-entropy rate, such as $k=0.99n$; an improved condenser could also suffice. A recent construction achieves $d=O(\log n)$ and $m=(1-1/\operatorname{polylog}(n))k$ for constant or slightly subconstant error, improving on the $m=\Omega(k)$ guarantee of Corollary 6.39.

<a id="pdf-bf2ce5422088-p203-b002"></a>
<!-- pdf-source: page=203; block=2; confidence=1.00 -->
**Open Problem 6.42.** Construct an explicit $(k,0.01)$-extractor $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $d=\log n+O(1)$ and $m=\Omega(k)$, or even $m=k^{\Omega(1)}$.

<a id="pdf-bf2ce5422088-p203-b003"></a>
<!-- pdf-source: page=203; block=3; confidence=0.98 -->
Some extractor applications have complexity exponential in seed length $d$ or entropy loss $k+d-m$, so additive improvements in these parameters can yield constant-factor complexity gains.

<a id="pdf-bf2ce5422088-p203-b004"></a>
<!-- pdf-source: page=203; block=4; confidence=0.98 -->
Theorem 6.36 combines a condenser, the Leftover Hash Lemma (Theorem 6.18), and composition lemmas 6.27 and 6.38 recursively. A more direct construction could be simpler to implement and clarify the theory; Chapter 7 gives a direct approach via pseudorandom generators, with weaker parameters.

<a id="pdf-bf2ce5422088-p203-b005"></a>
<!-- pdf-source: page=203; block=5; confidence=1.00 -->
**Open Problem 6.43.** Construct a direct $(k,\varepsilon)$-extractor $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $d=O(\log(n/\varepsilon))$ and $m=\Omega(k)$.

<a id="pdf-bf2ce5422088-p204-b001"></a>
<!-- pdf-source: page=204; block=1; confidence=1.00 -->
## 6.3.5 Block-Source Extraction versus the Zig–Zag Product

<a id="pdf-bf2ce5422088-p204-b002"></a>
<!-- pdf-source: page=204; block=2; confidence=0.99 -->
The block-source extraction method from Section 6.3.1, used in Theorem 6.36, parallels the zig–zag graph product from Section 4.3.2.3, used in Theorem 4.39.

<a id="pdf-bf2ce5422088-p204-b003"></a>
<!-- pdf-source: page=204; block=3; confidence=0.98 -->
For the case $m_2=d_1$, define $\operatorname{Ext}^{\blacktriangle}:\{0,1\}^{n_1+n_2}\times\{0,1\}^{d_2}\to\{0,1\}^{m_1}$ by $\operatorname{Ext}^{\blacktriangle}((x_1,x_2),y_2)=\operatorname{Ext}_1(x_1,\operatorname{Ext}_2(x_2,y_2))$. As bipartite graphs, the left vertices are $[N_1]\times[N_2]$ and left degree is $D_2$. A random step from $(x_1,x_2)$ first follows $G_2$ from $x_2$ to a right vertex $y_1\in\{0,1\}^{m_2}$, treated as an edge label for $G_1$, then follows the corresponding neighbor of $x_1$.

<a id="pdf-bf2ce5422088-p204-b004"></a>
<!-- pdf-source: page=204; block=4; confidence=0.99 -->
The settings differ: spectral expansion starts from an arbitrary distribution with limited Rényi entropy and seeks to add entropy, whereas block-source extraction assumes entropy in both blocks and seeks near-uniform output, possibly with fewer bits than the input entropy.

<a id="pdf-bf2ce5422088-p204-b005"></a>
<!-- pdf-source: page=204; block=5; confidence=0.99 -->
For this reason, we keep track of the edge used in the \(G_1\)-step—that is, we remember \(b_1\) such that \(x_1\) is the \(b_1\)th neighbor of \(z_1=\mathrm{Ext}(x_1,y_1)\). This ensures that the (edge-rotation) mapping \((x_1,y_1)\mapsto(z_1,b_1)\) is a permutation and does not lose any entropy. We can think of \(b_1\) as a “buffer”

<a id="pdf-bf2ce5422088-p205-b001"></a>
<!-- pdf-source: page=205; block=1; confidence=0.93 -->
Two entropy configurations motivate retaining intermediate output and adding a final expander step: when only the second block is uniform, the first zig–zag step transfers entropy to $z_1$, which the added step can extract. A condenser variant yields constant-degree bipartite expanders with expansion $(1-\varepsilon)D$ in balanced or nearly balanced cases; several stronger explicit-expander goals remain open.

<a id="pdf-bf2ce5422088-p205-b002"></a>
<!-- pdf-source: page=205; block=2; confidence=1.00 -->
## 6.4 Exercises

<a id="pdf-bf2ce5422088-p205-b003"></a>
<!-- pdf-source: page=205; block=3; confidence=1.00 -->
**Problem 6.1 (Min-entropy and Statistical Difference).**

<a id="pdf-bf2ce5422088-p205-b004"></a>
<!-- pdf-source: page=205; block=4; confidence=0.99 -->
**Problem 6.1 (Min-entropy and Statistical Difference).**\n\n(1) Prove that for every two random variables \(X\) and \(Y\),\n\n\[\Delta(X,Y)=\max_f |\mathbb E[f(X)]-\mathbb E[f(Y)]|=\frac12\cdot\lVert X-Y\rVert_1,\]\n\nwhere the maximum is over all \([0,1]\)-valued functions \(f\). (Hint: first identify the functions \(f\) that maximize \(|\mathbb E[f(X)]-\mathbb E[f(Y)]|\).)

<a id="pdf-bf2ce5422088-p206-b001"></a>
<!-- pdf-source: page=206; block=1; confidence=0.99 -->
Suppose that $(W,X)$ are jointly distributed random variables, where $(W,X)$ is a $k$-source and $|\operatorname{Supp}(W)|\le 2^\ell$. Show that for every $\varepsilon>0$, with probability at least $1-\varepsilon$ over $w\sim W$, we have that $X\mid W=w$ is a $(k-\ell-\log(1/\varepsilon))$-source.

<a id="pdf-bf2ce5422088-p206-b002"></a>
<!-- pdf-source: page=206; block=2; confidence=0.92 -->
If $X$ is an $(n-\Delta)$-source on $\{0,1\}^n$, split it into the first $n_1$ bits $X_1$ and remaining $n_2=n-n_1$ bits $X_2$. Prove that for every $\varepsilon>0$, $(X_1,X_2)$ is $\varepsilon$-close to a block source with block min-entropies $(n_1-\Delta,\ n_2-\Delta-\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p206-b003"></a>
<!-- pdf-source: page=206; block=3; confidence=1.00 -->
**Problem 6.2 (Simulating Randomized Algorithms with Weak Sources).**

<a id="pdf-bf2ce5422088-p206-b004"></a>
<!-- pdf-source: page=206; block=4; confidence=0.93 -->
Let randomized $A(w;r)$ compute $f$ using $m$ random bits with error at most $1/3$ under uniform $r$. Given a $(k,1/7)$ extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$, define $A^*(w;x)$ as the majority of $A(w;\mathrm{Ext}(x;y))$ over $y\in\{0,1\}^d$ (breaking ties arbitrarily). Prove that for any $(k+t)$-source $X$, $A^*(w;X)$ errs with probability at most $2^{-t}$.

<a id="pdf-bf2ce5422088-p206-b005"></a>
<!-- pdf-source: page=206; block=5; confidence=0.99 -->
Let $A(w;r)$ be a randomized algorithm for deciding a language $L$ using $m$ random bits such that $A(w;U_m)$ has one-sided error probability at most $1/2$ (i.e., if $w\in L$, then $\Pr[A(w;U_m)=1]\ge 1/2$ and if $w\notin L$, then $\Pr[A(w;U_m)=1]=0$), and let $\mathrm{Disp}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ be a $(k,1/3)$-disperser. Show how to decide $L$ with one-sided error at most $2^{-t}$ given a single sample from a $(k+t)$-source $X$ (with no other randomness) and running $A$ and $\mathrm{Disp}$ each $2^d$ times.

<a id="pdf-bf2ce5422088-p206-b006"></a>
<!-- pdf-source: page=206; block=6; confidence=0.88 -->
**Problem 6.3 (Almost-Universal Hashing).** A family of maps $[N]\to[M]$ has collision probability at most $\delta$ if every distinct pair collides with probability at most $\delta$ under a uniformly chosen family member. The page begins the exercise defining almost universality.

<a id="pdf-bf2ce5422088-p207-b001"></a>
<!-- pdf-source: page=207; block=1; confidence=0.99 -->
A family $\mathcal H$ of functions mapping $[N]$ to $[M]$ is said to have collision probability at most $\delta$ if for every $x_1\ne x_2\in[N]$, we have $\Pr_{H\sim_R\mathcal H}[H(x_1)=H(x_2)]\le\delta$. $\mathcal H$ is $\varepsilon$-almost universal if it has collision probability at most $(1+\varepsilon)/M$. (Note that this is a relaxation of the notion of $\varepsilon$-almost pairwise independence from Problem 3.4.)

<a id="pdf-bf2ce5422088-p207-b002"></a>
<!-- pdf-source: page=207; block=2; confidence=0.91 -->
Show that if $H=\{h:[N]\to[M]\}$ is $\varepsilon^2$-almost universal, then $\mathrm{Ext}(x,h)=h(x)$ is a strong $(k,\varepsilon)$ extractor for $k=m+2\log(1/\varepsilon)+O(1)$, where $m=\log M$.

<a id="pdf-bf2ce5422088-p207-b003"></a>
<!-- pdf-source: page=207; block=3; confidence=0.90 -->
Using Problem 3.4, deduce that for every $n\in\mathbb N$, $k\le n$, and $\varepsilon>0$, there is a strong $(k,\varepsilon)$ extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $d=O(k+\log(n/\varepsilon))$ and $m=k-2\log(1/\varepsilon)-O(1)$.

<a id="pdf-bf2ce5422088-p207-b004"></a>
<!-- pdf-source: page=207; block=4; confidence=0.96 -->
For $H$ mapping $[N]$ to $[M]$, define the code $\mathrm{Enc}:[N]\to[M]^{|H|}$ by $\mathrm{Enc}(x)_h=h(x)$. Prove that $H$ has collision probability at most $\delta$ exactly when $\mathrm{Enc}$ has minimum relative distance at least $1-\delta$.

<a id="pdf-bf2ce5422088-p207-b005"></a>
<!-- pdf-source: page=207; block=5; confidence=0.89 -->
Using these connections and the list-decoding characterization of extractors (Proposition 6.23), prove the small-alphabet Johnson bound: if $\mathrm{Enc}:[N]\to[M]^n$ has minimum distance at least $1-1/M-\gamma/M$, it is $(1-1/M-\gamma,\ O(M/\gamma))$ list-decodable.

<a id="pdf-bf2ce5422088-p207-b006"></a>
<!-- pdf-source: page=207; block=6; confidence=0.99 -->
**Problem 6.4 (Rényi extractors).** Call a function $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ a $(k,\varepsilon)$ Rényi extractor if for every source $X$ on $\{0,1\}^n$ of Rényi entropy at least $k$, it holds that $\mathrm{Ext}(X,U_d)$ has Rényi entropy at least $m-\varepsilon$.

<a id="pdf-bf2ce5422088-p207-b007"></a>
<!-- pdf-source: page=207; block=7; confidence=0.94 -->
Prove that every $(k,\varepsilon)$ Rényi extractor is also a $(k,O(\sqrt{\varepsilon}))$ extractor.

<a id="pdf-bf2ce5422088-p207-b008"></a>
<!-- pdf-source: page=207; block=8; confidence=0.90 -->
Prove that for all $n,k,m\in\mathbb N$ with $m\le n$ and $\varepsilon>0$, a $(k,\varepsilon)$ Rényi extractor exists with seed length $d=O(\min\{n-k+\log(1/\varepsilon),\ m/2+\log(n/\varepsilon)\})$.

<a id="pdf-bf2ce5422088-p208-b001"></a>
<!-- pdf-source: page=208; block=1; confidence=0.99 -->
Show that if $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,1)$ Rényi extractor, then $d\ge\min\{n-k,m/2\}-O(1)$. (Hint: consider a $k$-source that is uniform over $\{x:\exists y\ \mathrm{Ext}(x,y)\in T\}$ for an appropriately chosen set $T$.)

<a id="pdf-bf2ce5422088-p208-b002"></a>
<!-- pdf-source: page=208; block=2; confidence=0.98 -->
**Problem 6.5 (Extractors versus Samplers).** Use the connection between extractors and averaging samplers to establish the following claims.

<a id="pdf-bf2ce5422088-p208-b003"></a>
<!-- pdf-source: page=208; block=3; confidence=0.98 -->
For constants $\varepsilon,\alpha>0$, show that some constant $\beta<1$ allows, for every $n$, an explicit $(\beta n,\varepsilon)$ extractor with seed length $d\le\log n$ and output length $m\ge(1-\alpha)n$.

<a id="pdf-bf2ce5422088-p208-b004"></a>
<!-- pdf-source: page=208; block=4; confidence=0.96 -->
Prove that for every $m\in\mathbb N$, $\varepsilon,\delta>0$, there exists a nonconstructive $(\delta,\varepsilon)$ averaging sampler $\mathrm{Samp}:\{0,1\}^n\to(\{0,1\}^m)^t$ using $n=m+2\log(1/\varepsilon)+\log(1/\delta)+O(1)$ random bits and $t=O((1/\varepsilon^2)\cdot\log(1/\delta))$ samples.

<a id="pdf-bf2ce5422088-p208-b005"></a>
<!-- pdf-source: page=208; block=5; confidence=0.99 -->
Suppose we are given a constant-error BPP algorithm that uses $r=r(n)$ random bits on inputs of length $n$. Show how, using the explicit extractor of Theorem 6.36, we can reduce its error probability to $2^{-\ell}$ using $O(r)+\ell$ random bits, for any polynomial $\ell=\ell(n)$. (Note that this improves the $r+O(\ell)$ given by expander walks for $\ell\gg r$.) Conclude that every problem in BPP has a randomized polynomial-time algorithm that only errs for $2^{q^{0.01}}$ choices of its $q=q(n)$ random bits.

<a id="pdf-bf2ce5422088-p208-b006"></a>
<!-- pdf-source: page=208; block=6; confidence=0.99 -->
**Problem 6.6 (Extracting from Unpredictable-Bit Sources).**

<a id="pdf-bf2ce5422088-p208-b007"></a>
<!-- pdf-source: page=208; block=7; confidence=0.94 -->
If a source $X\in\{0,1\}^n$ satisfies $\Pr[X=x]/\Pr[X=y]\le(1-\delta)/\delta$ for all $x,y$, show that $X\in\mathrm{UnpredBits}_{n,\delta}$.

<a id="pdf-bf2ce5422088-p208-b008"></a>
<!-- pdf-source: page=208; block=8; confidence=0.99 -->
For every function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}$ and every $\delta>0$, there exists a source $X\in\mathrm{UnpredBits}_{n,\delta}$ with parameter $\delta$ such that $\Pr[\mathrm{Ext}(X)=1]\le\delta$ or $\Pr[\mathrm{Ext}(X)=0]\ge1-\delta$. (Hint: for $b\in\{0,1\}$, consider $X$ that is uniform on $\mathrm{Ext}^{-1}(b)$ with probability $1-\delta$ and is uniform on $\mathrm{Ext}^{-1}(\bar b)$ with probability $\delta$.)

<a id="pdf-bf2ce5422088-p209-b001"></a>
<!-- pdf-source: page=209; block=1; confidence=0.98 -->
Show how to extract from $\mathrm{UnpredBits}_{n,\delta}$ sources using a seeded extractor whose seed length depends on $\delta$ and the target statistical error $\varepsilon$, but not on source length $n$, while extracting $\Omega(\delta n)$ bits.

<a id="pdf-bf2ce5422088-p209-b002"></a>
<!-- pdf-source: page=209; block=2; confidence=0.99 -->
**Problem 6.7 (Average Min-Entropy).** For jointly distributed $(X,Y)$, define average conditional min-entropy by
\[
H_\infty(Y\mid X)=\log\frac{1}{\mathbb E_{x\sim X}[\max_y\Pr[Y=y\mid X=x]]}.
\]

<a id="pdf-bf2ce5422088-p209-b003"></a>
<!-- pdf-source: page=209; block=3; confidence=0.99 -->
Prove
\[
H_\infty(Y\mid X)=\log\frac{1}{\max_P\Pr[P(X)=Y]},
\]
where the maximum ranges over functions from the domain of $X$ to that of $Y$.

<a id="pdf-bf2ce5422088-p209-b004"></a>
<!-- pdf-source: page=209; block=4; confidence=0.99 -->
If $H_\infty(Y\mid X)\ge k$, show that with probability at least $1-\varepsilon$ over $x\sim X$, $H_\infty(Y\mid X=x)\ge k-\log(1/\varepsilon)$.

<a id="pdf-bf2ce5422088-p209-b005"></a>
<!-- pdf-source: page=209; block=5; confidence=0.99 -->
Show that $H_\infty(Y)\ge H_\infty(Y\mid X)\ge H_\infty(X,Y)-\log|\operatorname{Supp}(X)|$.

<a id="pdf-bf2ce5422088-p209-b006"></a>
<!-- pdf-source: page=209; block=6; confidence=0.99 -->
Use the previous two items to deduce Problem 6.1, Part 6.1.

<a id="pdf-bf2ce5422088-p209-b007"></a>
<!-- pdf-source: page=209; block=7; confidence=0.99 -->
Construct $n$-bit random variables with $H_\infty(Y)=n$ while both $H_\infty(Y\mid X)$ and $H_\infty(X)$ are $O(1)$.

<a id="pdf-bf2ce5422088-p209-b008"></a>
<!-- pdf-source: page=209; block=8; confidence=0.99 -->
**Problem 6.8 (Average Min-Entropy Extractors).**

<a id="pdf-bf2ce5422088-p210-b001"></a>
<!-- pdf-source: page=210; block=1; confidence=0.99 -->
**Definition.** A function $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon)$ average min-entropy extractor if, for every jointly distributed $(X,Y)$ with $X\in\{0,1\}^n$ and $H_\infty(X\mid Y)\ge k$,
\[
(\mathrm{Ext}(X,U_d),Y)\quad\text{is }\varepsilon\text{-close to }(U_m,Y),
\]
where $U_d,U_m$ are independent of $(X,Y)$.

<a id="pdf-bf2ce5422088-p210-b002"></a>
<!-- pdf-source: page=210; block=2; confidence=0.97 -->
The text notes that a $(k,\varepsilon)$ extractor gives a $(k+\log(1/\varepsilon),2\varepsilon)$ average min-entropy extractor via Problem 6.7(2), then poses a route to remove the entropy loss.

<a id="pdf-bf2ce5422088-p210-b003"></a>
<!-- pdf-source: page=210; block=3; confidence=0.99 -->
Assuming $k\le n-1$, show that if $\mathrm{Ext}$ is a $(k,\varepsilon)$ extractor, then for every $t>0$ it is a $(k-t,2^{t+1}\varepsilon)$ extractor. The hint compares, for each test $T\subseteq\{0,1\}^m$, the largest distinguishing advantage among $(k-t)$-sources and among $k$-sources.

<a id="pdf-bf2ce5422088-p210-b004"></a>
<!-- pdf-source: page=210; block=4; confidence=0.99 -->
Show that every $(k,\varepsilon)$ extractor is a $(k,3\varepsilon)$ average min-entropy extractor.

<a id="pdf-bf2ce5422088-p210-b005"></a>
<!-- pdf-source: page=210; block=5; confidence=0.98 -->
Using these results and Problem 6.3, construct, for every $n\in\mathbb N$, $k\le n$, and $\varepsilon>0$, an explicit $(k,\varepsilon)$ extractor with
\[
d=O((\log k)(\log(n/\varepsilon))),\qquad m=k+d-2\log(1/\varepsilon)-O(1).
\]

<a id="pdf-bf2ce5422088-p210-b006"></a>
<!-- pdf-source: page=210; block=6; confidence=0.99 -->
**Problem 6.9 (The Building-Block Extractor).**

<a id="pdf-bf2ce5422088-p210-b007"></a>
<!-- pdf-source: page=210; block=7; confidence=0.99 -->
Prove Lemma 6.37: Show that for every constant $t>0$, all positive integers $n\ge k$, and all $\varepsilon>0$, there is an explicit $(k,\varepsilon)$-extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with $m\ge k/2$ and $d=k/t+O(\log(n/\varepsilon))$. (Hint: convert the source into a block source with blocks of length $k/O(t)+O(\log(n/\varepsilon))$.)

<a id="pdf-bf2ce5422088-p210-b008"></a>
<!-- pdf-source: page=210; block=8; confidence=0.99 -->
**Problem 6.10 (Encryption and Deterministic Extraction).**

<a id="pdf-bf2ce5422088-p210-b009"></a>
<!-- pdf-source: page=210; block=9; confidence=0.99 -->
A (one-time) encryption scheme with key length $n$ and message length $m$ consists of an encryption function $\mathrm{Enc}:\{0,1\}^n\times\{0,1\}^m\to\{0,1\}^{\ell}$ and a decryption function $\mathrm{Dec}:\{0,1\}^n\times\{0,1\}^{\ell}\to\{0,1\}^m$ such that $\mathrm{Dec}(k,\mathrm{Enc}(k,u))=u$ for every $k\in\{0,1\}^n$ and $u\in\{0,1\}^m$.

<a id="pdf-bf2ce5422088-p211-b001"></a>
<!-- pdf-source: page=211; block=1; confidence=0.99 -->
Let $K$ be a random variable taking values in $\{0,1\}^n$. We say that $(\mathrm{Enc},\mathrm{Dec})$ is (statistically) $\varepsilon$-secure with respect to $K$ if for every two messages $u,v\in\{0,1\}^m$, we have $\Delta(\mathrm{Enc}(K,u),\mathrm{Enc}(K,v))\le\varepsilon$. For a class $\mathcal C$ of sources on $\{0,1\}^n$, we say that the encryption scheme $(\mathrm{Enc},\mathrm{Dec})$ is $\varepsilon$-secure with respect to $\mathcal C$ if $\mathrm{Enc}$ is $\varepsilon$-secure with respect to every $K\in\mathcal C$. For example, the one-time pad, where $n=m=\ell$ and $\mathrm{Enc}(k,u)=k\oplus u=\mathrm{Dec}(k,u)$, is $0$-secure (a.k.a. perfectly secure) with respect to the uniform distribution $K=U_m$.

<a id="pdf-bf2ce5422088-p211-b002"></a>
<!-- pdf-source: page=211; block=2; confidence=0.99 -->
(1) Show that if there exists a deterministic $\varepsilon$-extractor $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ for $\mathcal C$, then there exists a $2\varepsilon$-secure encryption scheme with respect to $\mathcal C$. (2) Conversely, use the following steps to show that if there exists an $\varepsilon$-secure encryption scheme $(\mathrm{Enc},\mathrm{Dec})$ with respect to $\mathcal C$, where $\mathrm{Enc}:\{0,1\}^n\times\{0,1\}^m\to\{0,1\}^{\ell}$, then there exists a deterministic $2\varepsilon$-extractor $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^{m-2\log(1/\varepsilon)-O(1)}$ for $\mathcal C$, provided $m\ge\log n+2\log(1/\varepsilon)+O(1)$. (a) For each fixed key $k\in\{0,1\}^n$, define a source $X_k$ on $\{0,1\}^{\ell}$ by $X_k=\mathrm{Enc}(k,U_m)$, and let $\mathcal C'$ be the class of all these sources (i.e., $\mathcal C'=\{X_k:k\in\{0,1\}^n\}$). Show that there exists a deterministic $\varepsilon$-extractor $\mathrm{Ext}':\{0,1\}^{\ell}\to\{0,1\}^{m-2\log(1/\varepsilon)-O(1)}$ for $\mathcal C'$, provided $m\ge\log n+2\log(1/\varepsilon)+O(1)$. (b) Show that if $\mathrm{Ext}'$ is a deterministic $\varepsilon$-extractor for $\mathcal C'$ and $\mathrm{Enc}$ is $\varepsilon$-secure with respect to $\mathcal C$, then $\mathrm{Ext}(k)=\mathrm{Ext}'(\mathrm{Enc}(k,0^m))$ is a deterministic $2\varepsilon$-extractor for $\mathcal C$. Thus, a class of sources can be used for secure encryption iff it is deterministically extractable.

<a id="pdf-bf2ce5422088-p211-b003"></a>
<!-- pdf-source: page=211; block=3; confidence=0.95 -->
**Problem 6.11.** For ternary alphabet \(\Sigma=\{0,1,2\}\), construct explicitly an \(\varepsilon\)-extractor \(\operatorname{Ext}:\Sigma^n\to\{0,1\}^m\) for symbol-fixing sources of min-entropy at least \(k\), with \(m=\Omega(k)\) and \(\varepsilon=2^{-\Omega(k)}\). Hint: use a random walk on a consistently labelled 3-regular expander.

<a id="pdf-bf2ce5422088-p212-b001"></a>
<!-- pdf-source: page=212; block=1; confidence=1.00 -->
**6.5 Chapter Notes and References.**

<a id="pdf-bf2ce5422088-p212-b002"></a>
<!-- pdf-source: page=212; block=2; confidence=0.96 -->
The notes survey early extractor work: von Neumann's IID-bit extractor, Blum's finite-state Markov-chain extension, and the unpredictable-bit model of Santha and Vazirani, including impossibility for a single such source. Later results show BPP simulation from one unpredictable-bit source and from block sources, followed by simulations from sources with sufficiently high, constant, and polynomially small min-entropy rates.

<a id="pdf-bf2ce5422088-p212-b003"></a>
<!-- pdf-source: page=212; block=3; confidence=0.94 -->
Nisan and Zuckerman introduced the seeded-extractor model discussed in the chapter and gave an early polylogarithmic-seed construction. The notes trace the Leftover Hash Lemma from an entropy-based flat-distribution version to Theorem 6.18, whose proof is attributed to Rackoff.

<a id="pdf-bf2ce5422088-p213-b001"></a>
<!-- pdf-source: page=213; block=1; confidence=0.94 -->
The notes attribute the Leftover Hash Lemma/Johnson Bound connection and the equivalence of almost-universal hashing with minimum distance to prior work. Deterministic extraction remains motivated by cryptographic applications, including bit-fixing leakage; Problem 6.11's symbol-fixing extractor is attributed to [232], and Problem 6.10's encryption/extraction connection to Bosley and Dodis [77]. Other source models are discussed in Section 8.2.

<a id="pdf-bf2ce5422088-p213-b002"></a>
<!-- pdf-source: page=213; block=2; confidence=0.96 -->
Bipartite expanders for simulating randomized algorithms from weak sources are attributed to Cohen and Wigderson. The chapter's expander-based extractor (Theorem 6.22) is due to Goldreich and Wigderson; Trevisan initiated the extractor/list-decodable-code connection, later formulated in Proposition 6.23, and Corollary 6.24's extractor/averaging-sampler equivalence is attributed to Zuckerman.

<a id="pdf-bf2ce5422088-p213-b003"></a>
<!-- pdf-source: page=213; block=3; confidence=0.96 -->
Shannon introduced entropy in information theory; the convergence of Shannon entropy to min-entropy under independent sampling, up to vanishing statistical distance, is called the Asymptotic Equipartition Property. Rényi entropy and the family \(H_\alpha\), \(\alpha\in(0,\infty)\), are also referenced.

<a id="pdf-bf2ce5422088-p214-b001"></a>
<!-- pdf-source: page=214; block=1; confidence=1.00 -->
## 6.5 Chapter Notes and References

<a id="pdf-bf2ce5422088-p214-b002"></a>
<!-- pdf-source: page=214; block=2; confidence=0.99 -->
The notes attribute the convex decomposition of a $k$-source into flat $k$-sources (Lemma 6.10) to an implicit result in [96], with the proof used here due to Kalai [230]. Radhakrishnan and Ta-Shma [315] established optimal nonconstructive extractor parameters in Theorem 6.14 and matching seed-length and output-length bounds. They also trace block-source extraction (Lemmas 6.27–6.28), weak-source conversion, source partitioning, condensers, vertex expansion, the construction in Section 6.3.4, and the zig–zag product to the cited works. Problem 6.2, concerning exponentially small error in simulating BPP from a weak source, is attributed to [426].

<a id="pdf-bf2ce5422088-p215-b001"></a>
<!-- pdf-source: page=215; block=1; confidence=1.00 -->
# 7 Pseudorandom Generators

<a id="pdf-bf2ce5422088-p215-b002"></a>
<!-- pdf-source: page=215; block=2; confidence=1.00 -->
## 7.1 Motivation and Definition

<a id="pdf-bf2ce5422088-p215-b003"></a>
<!-- pdf-source: page=215; block=3; confidence=0.99 -->
Prior derandomization results address selected algorithms, explicit pseudorandom objects, reduced randomness for sampling and amplification, and BPP simulation from weak sources. The motivating question remains whether every randomized algorithm can be efficiently derandomized, equivalently whether $\mathrm{BPP}=\mathrm{P}$.

<a id="pdf-bf2ce5422088-p216-b001"></a>
<!-- pdf-source: page=216; block=1; confidence=1.00 -->
A proposed route to derandomization first reduces a BPP algorithm's randomness from $\operatorname{poly}(n)$ bits to $O(\log n)$ bits, then enumerates the seeds. A pseudorandom generator is sought as a function $G$ expanding a seed of $d=O(\log n)$ bits to $m=\operatorname{poly}(n)$ bits, with output usable in place of uniform random bits in BPP algorithms.

<a id="pdf-bf2ce5422088-p216-b002"></a>
<!-- pdf-source: page=216; block=2; confidence=1.00 -->
The text rejects entropy, statistical difference, and pairwise independence as general criteria: deterministic expansion cannot raise entropy from $O(\log n)$ to $\operatorname{poly}(n)$, and pairwise independence does not suffice for all algorithms. Kolmogorov complexity is also unsuitable because each computable generator output has description length at most the seed length $d=O(\log n)$. The proposed notion is computational indistinguishability: efficient algorithms should not distinguish $X$ from uniform.

<a id="pdf-bf2ce5422088-p216-b003"></a>
<!-- pdf-source: page=216; block=3; confidence=1.00 -->
**Definition.** For random variables $X,Y$, statistical difference is
\[
\Delta(X,Y)=\max_T\left|\Pr[X\in T]-\Pr[Y\in T]\right|.
\]

<a id="pdf-bf2ce5422088-p217-b001"></a>
<!-- pdf-source: page=217; block=1; confidence=0.99 -->
Computational indistinguishability restricts the distinguishing tests to efficient ones.

<a id="pdf-bf2ce5422088-p217-b002"></a>
<!-- pdf-source: page=217; block=2; confidence=0.99 -->
**Definition 7.1.** Random variables $X,Y$ on $\{0,1\}^m$ are $(t,\varepsilon)$-indistinguishable if every nonuniform algorithm $T$ of time at most $t$ satisfies $|\Pr[T(X)=1]-\Pr[T(Y)=1]|\leq\varepsilon$. This difference is the advantage of $T$.

<a id="pdf-bf2ce5422088-p217-b003"></a>
<!-- pdf-source: page=217; block=3; confidence=0.98 -->
A nonuniform algorithm may use hardwired advice of length at most its running time. Nonuniform time-$t$ computation is treated as Boolean circuits of size $t$, counting AND and OR gates but not inputs or negations; nonuniform Turing machines and circuit families simulate one another with size/time overhead $\widetilde O(\cdot)$. Fixing randomness nonuniformly lets a randomized distinguisher with advantage above $\varepsilon$ be replaced by a deterministic one with advantage above $\varepsilon$.

<a id="pdf-bf2ce5422088-p218-b001"></a>
<!-- pdf-source: page=218; block=1; confidence=1.00 -->
## 7.1 Motivation and Definition

<a id="pdf-bf2ce5422088-p218-b002"></a>
<!-- pdf-source: page=218; block=2; confidence=0.99 -->
Uniform computational indistinguishability and pseudorandomness are also of interest.

<a id="pdf-bf2ce5422088-p218-b003"></a>
<!-- pdf-source: page=218; block=3; confidence=0.99 -->
**Definition 7.2.** For sequences of random variables $X_m,Y_m$ on $\{0,1\}^m$ (or $\{0,1\}^{\mathrm{poly}(m)}$), functions $t:\mathbb N\to\mathbb N$ and $\varepsilon:\mathbb N\to[0,1]$, the sequences are $(t(m),\varepsilon(m))$-indistinguishable for uniform algorithms if every probabilistic algorithm $T$ running in time $t(m)$ has $|\Pr[T(X_m)=1]-\Pr[T(Y_m)=1]|\leq\varepsilon(m)$ for all sufficiently large $m$. Probabilities include the samples and $T$'s random coins.

<a id="pdf-bf2ce5422088-p218-b004"></a>
<!-- pdf-source: page=218; block=4; confidence=1.00 -->
The discussion primarily uses the nonuniform definition while also noting uniform results.

<a id="pdf-bf2ce5422088-p218-b005"></a>
<!-- pdf-source: page=218; block=5; confidence=1.00 -->
## 7.1.2 Pseudorandom Generators

<a id="pdf-bf2ce5422088-p218-b006"></a>
<!-- pdf-source: page=218; block=6; confidence=0.99 -->
**Definition 7.3.** A deterministic $G:\{0,1\}^d\to\{0,1\}^m$ is a $(t,\varepsilon)$-pseudorandom generator if $d<m$ and $G(U_d)$ is $(t,\varepsilon)$-indistinguishable from $U_m$. An analogous uniform version uses uniform computational indistinguishability.

<a id="pdf-bf2ce5422088-p218-b007"></a>
<!-- pdf-source: page=218; block=7; confidence=0.98 -->
Earlier generators were assessed against selected statistical tests, which did not ensure reliability in arbitrary applications; the discussion continues on page 219.

<a id="pdf-bf2ce5422088-p219-b001"></a>
<!-- pdf-source: page=219; block=1; confidence=0.98 -->
Some classical generators, including linear congruential generators used in standard C libraries, fail in applications. The definition aims to make generated bits as useful as uniform bits for all time-$t$ purposes; derandomization also requires efficient computation of the generator.

<a id="pdf-bf2ce5422088-p219-b002"></a>
<!-- pdf-source: page=219; block=2; confidence=0.99 -->
**Definition 7.4.** A family $\{G_m:\{0,1\}^{d(m)}\to\{0,1\}^m\}$ is computable in time $t(m)$ if a uniform deterministic algorithm $M$ computes $M(m,x)=G_m(x)$ within time $t(m)$ for every $m$ and valid seed $x$, and outputs $d(m)$ on input $m$ alone within time $t(m)$.

<a id="pdf-bf2ce5422088-p219-b003"></a>
<!-- pdf-source: page=219; block=3; confidence=0.99 -->
The pseudorandomness guarantee may concern nonuniform distinguishers even though generator efficiency is defined using a uniform algorithm. A single symbol $G$ implicitly denotes the family $\{G_m\}$.

<a id="pdf-bf2ce5422088-p219-b004"></a>
<!-- pdf-source: page=219; block=4; confidence=0.99 -->
**Theorem 7.5.** Suppose that for all $m$ there exists an $(m,1/8)$ pseudorandom generator $G:\{0,1\}^{d(m)}\to\{0,1\}^m$ computable in time $t(m)$. Then $\mathrm{BPP}\subseteq\bigcup_c\mathrm{DTIME}\bigl(2^{d(n^c)}\cdot(n^c+t(n^c))\bigr)$.

<a id="pdf-bf2ce5422088-p219-b005"></a>
<!-- pdf-source: page=219; block=5; confidence=0.94 -->
**Proof.** Let $A(x;r)$ be a BPP algorithm on inputs of length $n$, represented by Boolean circuits of size at most $n^c$ using random string $r$. Assume without loss of generality that $|r|=n^c$; the algorithm may read only a prefix, leaving time for computation.

<a id="pdf-bf2ce5422088-p220-b001"></a>
<!-- pdf-source: page=220; block=1; confidence=0.99 -->
The section motivates replacing an algorithm’s random bits with PRG output, then enumerating seeds to derandomize it.

<a id="pdf-bf2ce5422088-p220-b002"></a>
<!-- pdf-source: page=220; block=2; confidence=0.99 -->
**Claim 7.6.** For every $x$ of length $n$, $A(x;G(U_{d(n^c)}))$ errs with probability smaller than $1/2$.

<a id="pdf-bf2ce5422088-p220-b003"></a>
<!-- pdf-source: page=220; block=3; confidence=0.96 -->
**Proof.** If some $x$ has error probability at least $1/2$, then $T(\cdot)=A(x,\cdot)$ is a Boolean circuit of size at most $n^c$ distinguishing $G(U_{d(n^c)})$ from $U_{n^c}$ with advantage at least $1/2-1/3>1/8$. The input $x$ acts as nonuniform advice, so the PRG must fool nonuniform tests.

<a id="pdf-bf2ce5422088-p220-b004"></a>
<!-- pdf-source: page=220; block=4; confidence=0.99 -->
Enumerating all $2^{d(n^c)}$ seeds and taking a majority vote yields a deterministic simulation, running $G$ and $A$ for each seed.

<a id="pdf-bf2ce5422088-p220-b005"></a>
<!-- pdf-source: page=220; block=5; confidence=0.99 -->
**Definition 7.7.** For $G:\{0,1\}^{d(m)}\to\{0,1\}^m$, (1) $G$ is mildly explicit if computable in time $\operatorname{poly}(m,2^{d(m)})$; (2) $G$ is fully explicit if computable in time $\operatorname{poly}(m)$.

<a id="pdf-bf2ce5422088-p221-b001"></a>
<!-- pdf-source: page=221; block=1; confidence=0.98 -->
A mildly explicit generator’s truth table is constructible in time polynomial in its size $m2^{d(m)}$; a fully explicit generator can be evaluated in polynomial time in input and output lengths. Theorem 7.5 yields: (1) seed length $d(m)=m^\varepsilon$ for every constant $\varepsilon>0$ implies $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$, where $\mathrm{SUBEXP}=\bigcap_{\varepsilon>0}\mathrm{DTIME}(2^{n^\varepsilon})$; (2) $d(m)=\operatorname{polylog}(m)$ implies $\mathrm{BPP}\subseteq\widetilde{\mathrm P}$, where $\widetilde{\mathrm P}=\bigcup_c\mathrm{DTIME}(2^{(\log m)^c})$; (3) $d(m)=O(\log m)$ implies $\mathrm{BPP}=\mathrm P$.

<a id="pdf-bf2ce5422088-p221-b002"></a>
<!-- pdf-source: page=221; block=2; confidence=0.99 -->
**Proposition 7.8.** For every $m\in\mathbb N$ and $\varepsilon>0$, there exists a nonexplicit $(m,\varepsilon)$ pseudorandom generator $G:\{0,1\}^d\to\{0,1\}^m$ with seed length $d=O(\log m+\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p221-b003"></a>
<!-- pdf-source: page=221; block=3; confidence=0.98 -->
**Proof.** Choose $G$ uniformly at random. For a fixed time-$m$ algorithm $T$, a Chernoff bound gives probability at most $2^{-\Omega(2^d\varepsilon^2)}$ over the choice of $G$ that $T$ distinguishes $G(U_d)$ from $U_m$ with advantage $\varepsilon$. There are $2^{\operatorname{poly}(m)}$ nonuniform time-$m$ algorithms (circuits of size $m$); a union bound makes the probability that any $T$ breaks $G$ less than $1$ for $d=O(\log m+\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p222-b001"></a>
<!-- pdf-source: page=222; block=1; confidence=0.99 -->
The union-bound estimate is $2^{\operatorname{poly}(m)}2^{-\Omega(2^d\varepsilon^2)}<1$ for the stated seed length, so some choice of $G$ fools every such distinguisher.

<a id="pdf-bf2ce5422088-p222-b002"></a>
<!-- pdf-source: page=222; block=2; confidence=0.97 -->
Proposition 7.8 and Theorem 7.5 imply $\mathrm{BPP}\subseteq\mathrm P/\mathrm{poly}$: advice can encode the truth table of an $(n^c,1/8)$-PRG using $2^{d(n^c)}n^c=\operatorname{poly}(n)$ bits, which then derandomizes the BPP algorithm. This gives essentially the same construction as error reduction followed by fixing coin tosses.

<a id="pdf-bf2ce5422088-p222-b003"></a>
<!-- pdf-source: page=222; block=3; confidence=0.98 -->
Cryptographic PRGs should be efficient for honest users while resisting computationally more powerful adversaries; common theoretical parameters require fixed polynomial time for generation and arbitrary polynomial time for distinguishers.

<a id="pdf-bf2ce5422088-p222-b004"></a>
<!-- pdf-source: page=222; block=4; confidence=0.98 -->
**Definition 7.9.** A generator $G_m:\{0,1\}^{d(m)}\to\{0,1\}^m$ is a cryptographic pseudorandom generator if it is fully explicit: there is a constant $b$ such that $G_m$ is computable in time $m^b$.

<a id="pdf-bf2ce5422088-p223-b001"></a>
<!-- pdf-source: page=223; block=1; confidence=0.97 -->
A cryptographic PRG has parameters $(m^{\omega(1)},1/m^{\omega(1)})$: for each constant $c$, it is an $(m^c,1/m^c)$ pseudorandom generator for all sufficiently large $m$. Such generators imply $\mathrm{NP}\not\subseteq\mathrm{P/poly}$; their construction is therefore considered under assumptions, especially the existence of efficiently computable hard-to-invert functions.

<a id="pdf-bf2ce5422088-p223-b002"></a>
<!-- pdf-source: page=223; block=2; confidence=0.99 -->
**Definition 7.10.** A family $f_n:\{0,1\}^n\to\{0,1\}^n$ is one-way if (1) some constant $b$ gives an $n^b$-time algorithm computing $f_n$ for all sufficiently large $n$, and (2) for every constant $c$ and every nonuniform algorithm $A$ running in time $n^c$, \(\Pr[A(f_n(U_n))\in f_n^{-1}(f_n(U_n))]\le 1/n^c\) for all sufficiently large $n$.

<a id="pdf-bf2ce5422088-p223-b003"></a>
<!-- pdf-source: page=223; block=3; confidence=0.97 -->
One-wayness is an average-case assumption stronger in flavor than $\mathrm{NP}\not\subseteq\mathrm{P/poly}$. Integer multiplication of two $n/2$-bit integers is given as a candidate; inversion requires factoring.

<a id="pdf-bf2ce5422088-p224-b001"></a>
<!-- pdf-source: page=224; block=1; confidence=0.99 -->
**Theorem 7.11.** The following are equivalent: (1) one-way functions exist; (2) cryptographic PRGs exist with seed length $d(m)=m-1$; (3) for every constant $\varepsilon>0$, cryptographic PRGs exist with seed length $d(m)=m^\varepsilon$.

<a id="pdf-bf2ce5422088-p224-b002"></a>
<!-- pdf-source: page=224; block=2; confidence=0.99 -->
**Corollary 7.12.** If one-way functions exist, then $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$.

<a id="pdf-bf2ce5422088-p224-b003"></a>
<!-- pdf-source: page=224; block=3; confidence=0.98 -->
Given a one-way function $f_\ell:\{0,1\}^\ell\to\{0,1\}^\ell$, the construction produces a generator $G_m:\{0,1\}^{\mathrm{poly}(\ell)}\to\{0,1\}^m$. A distinguisher of time $t$ and advantage $\varepsilon$ yields an inverter of time $t'=t\cdot(m/\varepsilon)^{O(1)}$ that inverts $f_\ell$ with probability $1/2$. If $t'\leq\mathrm{poly}(\ell)$, this contradicts the one-wayness of $f_\ell$, and hence $G_m$ is a $(t,\varepsilon)$ pseudorandom generator.

<a id="pdf-bf2ce5422088-p224-b004"></a>
<!-- pdf-source: page=224; block=4; confidence=0.94 -->
If $f_\ell$ is hard to invert by algorithms running in time $s(\ell)$ and we take $m=1/\varepsilon=s(\ell)^{o(1)}$, then $t'\leq s(\ell)$ for every $t=\mathrm{poly}(m)$ and sufficiently large $\ell$. Thus, viewing the seed length $d$ of $G_m$ as a function of $m$, we have $d(m)=\mathrm{poly}(\ell)=\mathrm{poly}(s^{-1}(m^{\omega(1)}))$, where $m^{\omega(1)}$ denotes any superpolynomial function of $m$.

<a id="pdf-bf2ce5422088-p224-b005"></a>
<!-- pdf-source: page=224; block=5; confidence=0.96 -->
If $s(\ell)=\ell^{\omega(1)}$, the construction yields seed length $m^\varepsilon$ for any constant $\varepsilon>0$ and implies $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$.

<a id="pdf-bf2ce5422088-p225-b001"></a>
<!-- pdf-source: page=225; block=1; confidence=0.97 -->
If $s(\ell)=2^{\ell^{\omega(1)}}$, as is plausible for the factoring one-way function, then we get seed length $d(m)=\mathrm{poly}(\log m)$ and $\mathrm{BPP}\subseteq\widetilde{\mathrm P}$. Even for the maximum possible hardness $s(\ell)=2^{\Omega(\ell)}$, we get $d(m)=\mathrm{poly}(\log m)$. The text notes that a cryptographic PRG with seed length $O(\log m)$ meeting Definition 7.9 is impossible, but such a seed length for derandomization could follow if the construction achieved $d=O(\ell)$ instead of $d=\mathrm{poly}(\ell)$.

<a id="pdf-bf2ce5422088-p225-b002"></a>
<!-- pdf-source: page=225; block=2; confidence=0.99 -->
**Open Problem 7.13.** Given a one-way function $f:\{0,1\}^\ell\to\{0,1\}^\ell$ that is hard to invert by algorithms running in time $s=s(\ell)$, and a constant $c$, is it possible to construct a fully explicit $(t,\varepsilon)$ pseudorandom generator $G:\{0,1\}^d\to\{0,1\}^m$ with seed length $d=O(\ell)$ and pseudorandomness against time $t=s\cdot(\varepsilon/m)^{O(1)}$?

<a id="pdf-bf2ce5422088-p225-b003"></a>
<!-- pdf-source: page=225; block=3; confidence=0.99 -->
The best known seed length for such a generator is $d=\widetilde O(\ell^3\cdot\log(m/\varepsilon)/\log^2 s)$, which is $\widetilde O(\ell^2)$ for the case $s=2^{\Omega(\ell)}$ and $m=2^{\Omega(\ell)}$.

<a id="pdf-bf2ce5422088-p225-b004"></a>
<!-- pdf-source: page=225; block=4; confidence=0.98 -->
For a one-way permutation $f:\{0,1\}^\ell\to\{0,1\}^\ell$, define
\[
G_m(x,r)=\bigl(\langle x,r\rangle,\langle f(x),r\rangle,\langle f(f(x)),r\rangle,\ldots,\langle f^{(m-1)}(x),r\rangle\bigr),
\]
where $|r|=|x|=\ell$ and $\langle\cdot,\cdot\rangle$ denotes inner product modulo 2. Consider the sequence $(f^{(m-1)}(U_\ell),f^{(m-2)}(U_\ell),\ldots,f(U_\ell),U_\ell)$. The text argues that the $i+1$st component is infeasible to predict from the first $i$ components except with negligible probability.

<a id="pdf-bf2ce5422088-p226-b001"></a>
<!-- pdf-source: page=226; block=1; confidence=0.96 -->
A computational analogue of block-source extraction uses the strong extractor \(\operatorname{Ext}(x,r)=\langle x,r\rangle\); its proof is more involved and uses local list decoding for the Hadamard code (Problems 7.12–7.13; Section 7.6).

<a id="pdf-bf2ce5422088-p226-b002"></a>
<!-- pdf-source: page=226; block=2; confidence=1.00 -->
## Pseudorandom Functions

<a id="pdf-bf2ce5422088-p226-b003"></a>
<!-- pdf-source: page=226; block=3; confidence=0.98 -->
A pseudorandom function family \(\{f_s:\{0,1\}^d\to\{0,1\}\}_{s\in\{0,1\}^d}\) has polynomial-time evaluation given seed \(s\), while an oracle for \(f_s\), without the seed, is computationally indistinguishable from an oracle for a uniformly random function. Its truth table expands a \(d\)-bit seed into \(2^d\) pseudorandom bits.

<a id="pdf-bf2ce5422088-p226-b004"></a>
<!-- pdf-source: page=226; block=4; confidence=0.99 -->
Parties sharing seed \(s\) can encrypt a message \(m\) by choosing uniform \(r\in\{0,1\}^d\) and sending \((r,f_s(r)\oplus m)\); the receiver recovers \(m\) using \(s\), while the masked value appears random without it.

<a id="pdf-bf2ce5422088-p226-b005"></a>
<!-- pdf-source: page=226; block=5; confidence=0.99 -->
In learning theory, one is given examples of a function’s behavior, $(x_1,f(x_1)),(x_2,f(x_2)),\ldots,(x_k,f(x_k))$, where the $x_i$ are selected randomly from an underlying distribution, and the goal is to predict the function’s value at a new point $x_{k+1}$ from the same distribution.

<a id="pdf-bf2ce5422088-p227-b001"></a>
<!-- pdf-source: page=227; block=1; confidence=0.98 -->
Although small-description functions are information-theoretically learnable from few samples, predicting a PRF at a new point is computationally hard even after observing values at \(k\) points and making membership queries. PRFs therefore give efficiently computable functions that are hard to learn.

<a id="pdf-bf2ce5422088-p227-b002"></a>
<!-- pdf-source: page=227; block=2; confidence=0.95 -->
Proving $\mathrm P\ne\mathrm{NP}$ via circuit lower bounds would require showing that some $f\in\mathrm{NP}$ does not have polynomial-size circuits (equivalently, $\mathrm{NP}\not\subseteq\mathrm{P/poly}$). For general circuits, the best lower bound achieved for a problem in $\mathrm{NP}$ is $5n-O(n)$. The Natural Proofs barrier says that any sufficiently constructive proof of superpolynomial circuit lower bounds could distinguish a pseudorandom function from a random function in subexponential time and thus invert any one-way function in subexponential time.

<a id="pdf-bf2ce5422088-p227-b003"></a>
<!-- pdf-source: page=227; block=3; confidence=1.00 -->
## 7.3 Hybrid Arguments

<a id="pdf-bf2ce5422088-p227-b004"></a>
<!-- pdf-source: page=227; block=4; confidence=0.99 -->
Hybrid arguments establish that computational indistinguishability persists across multiple samples and that pseudorandomness is equivalent to next-bit unpredictability.

<a id="pdf-bf2ce5422088-p228-b001"></a>
<!-- pdf-source: page=228; block=1; confidence=1.00 -->
### 7.3.1 Indistinguishability of Multiple Samples

<a id="pdf-bf2ce5422088-p228-b002"></a>
<!-- pdf-source: page=228; block=2; confidence=0.98 -->
The proposition gives a computational analogue of the statistical-distance bound for independent repetitions: the distinguishing advantage grows by at most the number of copies.

<a id="pdf-bf2ce5422088-p228-b003"></a>
<!-- pdf-source: page=228; block=3; confidence=0.99 -->
**Proposition 7.14.** If random variables \(X\) and \(Y\) are \((t,\varepsilon)\)-indistinguishable, then for every \(k\in\mathbb N\), their respective distributions on \(k\) independent copies, \(X^k\) and \(Y^k\), are \((t,k\varepsilon)\)-indistinguishable.

<a id="pdf-bf2ce5422088-p228-b004"></a>
<!-- pdf-source: page=228; block=4; confidence=0.98 -->
**Proof.** Prove the contrapositive: from an efficient distinguisher \(T\) for \(X^k\) and \(Y^k\) with advantage greater than \(k\varepsilon\), construct an efficient distinguisher \(T'\) for \(X\) and \(Y\) with advantage greater than \(\varepsilon\). The reduction uses \(T\) as a subroutine.

<a id="pdf-bf2ce5422088-p228-b005"></a>
<!-- pdf-source: page=228; block=5; confidence=0.99 -->
Assume there is a nonuniform time-\(t\) algorithm \(T\) such that
\[
\left|\Pr[T(X^k)=1]-\Pr[T(Y^k)=1]\right|>k\varepsilon. \tag{7.1}
\]

<a id="pdf-bf2ce5422088-p228-b006"></a>
<!-- pdf-source: page=228; block=6; confidence=0.99 -->
Without loss of generality, drop the absolute value in (7.1), replacing \(T\) by its negation if necessary; negation is free in the circuit-size measure.

<a id="pdf-bf2ce5422088-p229-b001"></a>
<!-- pdf-source: page=229; block=1; confidence=0.97 -->
For hybrids \(H_i=X^{k-i}Y^i\), with \(H_0=X^k\) and \(H_k=Y^k\), the assumed distinguishing gap (7.1) is the telescoping sum \(\sum_{i=1}^k(\Pr[T(H_{i-1})=1]-\Pr[T(H_i)=1])>k\varepsilon\). Hence some adjacent pair has gap greater than \(\varepsilon\):
\[
\Pr[T(X^{k-i}XY^{i-1})=1]-\Pr[T(X^{k-i}YY^{i-1})=1]>\varepsilon.
\]
Averaging fixes the other coordinates so this gap still exceeds \(\varepsilon\). Hardwire them and \(i\) into a test \(T'\); its size remains bounded by \(t\), contradicting \((t,\varepsilon)\)-indistinguishability of \(X,Y\).

<a id="pdf-bf2ce5422088-p229-b002"></a>
<!-- pdf-source: page=229; block=2; confidence=0.99 -->
The argument increases nonuniform advice, and is uninformative for large \(k\), since a time-\(t\) algorithm cannot read more than \(t\) input bits.

<a id="pdf-bf2ce5422088-p229-b003"></a>
<!-- pdf-source: page=229; block=3; confidence=0.97 -->
For uniform tests, an analogous claim requires efficient samplability of \(X,Y\); a direct version without this condition is false. The continuation describes choosing a hybrid index and sampling the other coordinates.

<a id="pdf-bf2ce5422088-p230-b001"></a>
<!-- pdf-source: page=230; block=1; confidence=0.98 -->
Assuming efficient samplers for \(X,Y\), the uniform test can choose \(i\in[k]\) at random and sample the fixed coordinates from the corresponding distributions.

<a id="pdf-bf2ce5422088-p230-b002"></a>
<!-- pdf-source: page=230; block=2; confidence=1.00 -->
## 7.3.2 Next-Bit Unpredictability

<a id="pdf-bf2ce5422088-p230-b003"></a>
<!-- pdf-source: page=230; block=3; confidence=0.99 -->
For pseudorandomness analysis, use the equivalent viewpoint that an output prefix should not permit predicting its next bit substantially better than chance. Here \(X_i\) denotes bit \(i\) of \(X\).

<a id="pdf-bf2ce5422088-p230-b004"></a>
<!-- pdf-source: page=230; block=4; confidence=1.00 -->
**Definition 7.15.** For an \(m\)-bit random variable \(X\), say \(X\) is \((t,\varepsilon)\) next-bit unpredictable if every nonuniform probabilistic algorithm \(P\) of time \(t\) and every \(i\in[m]\) satisfy
\[
\Pr[P(X_1\cdots X_{i-1})=X_i]\le \tfrac12+\varepsilon,
\]
where probability is over \(X\) and \(P\)'s coins.

<a id="pdf-bf2ce5422088-p230-b005"></a>
<!-- pdf-source: page=230; block=5; confidence=0.99 -->
The uniform distribution \(U_m\) is \((t,0)\) next-bit unpredictable for every \(t\); pseudorandomness implies this property, and the converse is also asserted below.

<a id="pdf-bf2ce5422088-p230-b006"></a>
<!-- pdf-source: page=230; block=6; confidence=1.00 -->
**Proposition 7.16.** For \(X\in\{0,1\}^m\), if \(X\) is \((t,\varepsilon)\) pseudorandom, then it is \((t-O(1),\varepsilon)\) next-bit unpredictable. Conversely, if it is \((t,\varepsilon)\) next-bit unpredictable, then it is \((t,m\varepsilon)\) pseudorandom.

<a id="pdf-bf2ce5422088-p230-b007"></a>
<!-- pdf-source: page=230; block=7; confidence=0.99 -->
**Proof.** Let \(U\) be uniform on \(\{0,1\}^m\), and write \(U_i\) for its \(i\)-th bit. The proof establishes both implications by reduction.

<a id="pdf-bf2ce5422088-p231-b001"></a>
<!-- pdf-source: page=231; block=1; confidence=0.98 -->
Assume a predictor \(P\) on the first \(i-1\) bits predicts \(X_i\) with probability at least \(1/2+\varepsilon\), contrary to \((t-3,\varepsilon)\) next-bit unpredictability. Define a distinguisher \(T(x_1\cdots x_m)=1\) iff \(P(x_1\cdots x_{i-1})=x_i\). It uses the gates of \(P\) plus three gates for equality, so the prediction advantage distinguishes \(X\) from \(U_m\), contradicting pseudorandomness at the stated constant size loss.

<a id="pdf-bf2ce5422088-p231-b002"></a>
<!-- pdf-source: page=231; block=2; confidence=0.94 -->
Suppose a time-\(t\) test \(T\) has \(\Pr[T(X)=1]-\Pr[T(U_m)=1]>\varepsilon\), taking the positive sign without loss of generality. Set \(H_i=X_1\cdots X_iU_{i+1}\cdots U_m\), so \(H_0=U_m\), \(H_m=X\). Telescoping gives
\[
\sum_{i=1}^m\bigl(\Pr[T(H_i)=1]-\Pr[T(H_{i-1})=1]\bigr)>\varepsilon,
\]
so for some \(i\), the adjacent gap exceeds \(\varepsilon/m\). Since \(U_i\) is an independent uniform bit, this gap comes from the case where the bit substituted for \(X_i\) differs from \(X_i\); when they agree the two inputs coincide. The text begins a formal expansion of this observation at the page end.

<a id="pdf-bf2ce5422088-p232-b001"></a>
<!-- pdf-source: page=232; block=1; confidence=0.98 -->
Define the next-bit predictor $P(x_1x_2\cdots x_{i-1})$: choose random bits $u_i,\ldots,u_m\in\{0,1\}$; compute $b=T(x_1\cdots x_{i-1}u_i\cdots u_m)$; if $b=1$, output $u_i$, otherwise output $\overline{u_i}$. The displayed calculation gives $\Pr[P(X_1\cdots X_{i-1})=X_i]>\tfrac12+\tfrac{\varepsilon}{m}$. Fixing the coin tosses nonuniformly preserves its advantage. The resulting circuit runs $T$ on $x_1\cdots x_{i-1}$ concatenated with fixed bits and either outputs what $T$ does or its negation, contradicting next-bit unpredictability.

<a id="pdf-bf2ce5422088-p232-b002"></a>
<!-- pdf-source: page=232; block=2; confidence=0.96 -->
An analogous uniform result uses a predictor that samples \(i\leftarrow[m]\); its time bounds lose an additive \(O(m)\). This version does not require efficient samplability of \(X\).

<a id="pdf-bf2ce5422088-p233-b001"></a>
<!-- pdf-source: page=233; block=1; confidence=0.99 -->
## 7.4 Pseudorandom Generators from Average-Case Hardness

<a id="pdf-bf2ce5422088-p233-b002"></a>
<!-- pdf-source: page=233; block=2; confidence=0.90 -->
For derandomization, it suffices that \(G:\{0,1\}^{d(m)}\to\{0,1\}^m\) fool nonuniform distinguishers of time \(m\) and be computable in time \(\operatorname{poly}(m,2^{d(m)})\). Such a generator derandomizes BPP in time \(\operatorname{poly}(n)\,2^{d(\operatorname{poly}(n))}\). The section seeks constructions from average-case hardness of exponentially computable Boolean functions, before later weakening the assumption to worst-case hardness.

<a id="pdf-bf2ce5422088-p234-b001"></a>
<!-- pdf-source: page=234; block=1; confidence=0.99 -->
## 7.4.1 Average-Case Hardness

<a id="pdf-bf2ce5422088-p234-b002"></a>
<!-- pdf-source: page=234; block=2; confidence=0.99 -->
**Definition 7.17.** For $s\in\mathbb N$ and $\delta\in[0,1]$, a Boolean function $f:\{0,1\}^\ell\to\{0,1\}$ is $(s,\delta)$ average-case hard if for all nonuniform probabilistic algorithms $A$ running in time $s$,
\[
\Pr[A(X)=f(X)]\leq 1-\delta,
\]
where the probability is taken over $X$ and the coin tosses of $A$.

<a id="pdf-bf2ce5422088-p234-b003"></a>
<!-- pdf-source: page=234; block=3; confidence=0.88 -->
Any positive \(\delta\) gives worst-case hardness; the intended average-case regime has noticeably larger error, with this section using \(\delta=\tfrac12-\varepsilon\), \(\varepsilon=1/s\). The function is also assumed uniformly computable in time \(2^{O(n)}\); later results derive such average-case hardness from worst-case assumptions.

<a id="pdf-bf2ce5422088-p234-b004"></a>
<!-- pdf-source: page=234; block=4; confidence=0.96 -->
**Proposition 7.18.** If \(f:\{0,1\}^n\to\{0,1\}\) is \((t,\tfrac12-\varepsilon)\) average-case hard, then \(G(x)=x\circ f(x)\) is a \((t,\varepsilon)\) pseudorandom generator.

<a id="pdf-bf2ce5422088-p235-b001"></a>
<!-- pdf-source: page=235; block=1; confidence=0.95 -->
The proposition’s omitted proof follows from Problem 7.5(2) and Theorem 7.24 with the indicated parameters. This generator outputs its seed, which is possible under resource-bounded distinguishers but unsuitable for cryptographic PRGs.

<a id="pdf-bf2ce5422088-p235-b002"></a>
<!-- pdf-source: page=235; block=2; confidence=0.92 -->
Concatenating k independent copies of a pseudorandom distribution gives error kε by Proposition 7.14, but barely improves output-to-seed ratio; this argument uses nonuniform indistinguishability. A recursive composition using G’s first ℓ output bits as a new seed fails for G(x)=x f(x), since it yields x f(x) f(x).

<a id="pdf-bf2ce5422088-p235-b003"></a>
<!-- pdf-source: page=235; block=3; confidence=1.00 -->
Section heading: The Pseudorandom Generator.

<a id="pdf-bf2ce5422088-p235-b004"></a>
<!-- pdf-source: page=235; block=4; confidence=0.98 -->
**Theorem 7.19.** For $s:\mathbb{N}\to\mathbb{N}$, suppose that there is a function $f\in\mathrm{E}=\mathrm{DTIME}(2^{O(\ell)})^2$ such that for every input length $\ell\in\mathbb{N}$, $f$ is $(s(\ell),1/2-1/s(\ell))$ average-case hard, where $s(\ell)$ is computable in time $2^{O(\ell)}$. Then for every $m\in\mathbb{N}$, there is a mildly explicit $(m,1/m)$ pseudorandom generator $G:\{0,1\}^{d(m)}\to\{0,1\}^m$ with seed length $d(m)=O(s^{-1}(\mathrm{poly}(m))^2/\log m)$ that is computable in time $2^{O(d(m))}$.

<a id="pdf-bf2ce5422088-p236-b001"></a>
<!-- pdf-source: page=236; block=1; confidence=0.92 -->
The text notes stronger known seed-length bounds and derives P = BPP when hardness is exponential; it then states broader complexity consequences in Corollary 7.20.

<a id="pdf-bf2ce5422088-p236-b002"></a>
<!-- pdf-source: page=236; block=2; confidence=0.99 -->
**Corollary 7.20.** Suppose that $\mathrm{E}$ has an $(s(\ell),1/2-1/s(\ell))$ average-case hard function $f:\{0,1\}^\ell\to\{0,1\}$. (1) If $s(\ell)=2^{\Omega(\ell)}$, then $\mathrm{BPP}=\mathrm{P}$. (2) If $s(\ell)=2^{\ell^{\Omega(1)}}$, then $\mathrm{BPP}\subseteq\widetilde{\mathrm{P}}$. (3) If $s(\ell)=\ell^{\omega(1)}$, then $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$.

<a id="pdf-bf2ce5422088-p236-b003"></a>
<!-- pdf-source: page=236; block=3; confidence=0.97 -->
The generator applies f repeatedly to inputs with small pairwise overlap; each output bit uses a subset of seed coordinates.

<a id="pdf-bf2ce5422088-p236-b004"></a>
<!-- pdf-source: page=236; block=4; confidence=0.99 -->
**Definition 7.21.** Sets S₁,…,S_m ⊂ [d] form an (ℓ,a)-design if (1) |Sᵢ|=ℓ for every i, and (2) |Sᵢ ∩ Sⱼ|≤a whenever i≠j.

<a id="pdf-bf2ce5422088-p237-b001"></a>
<!-- pdf-source: page=237; block=1; confidence=0.95 -->
The text emphasizes logarithmic intersection bounds and a universe size at most quadratic in the set size (linear when m=2^{Ω(ℓ)}).

<a id="pdf-bf2ce5422088-p237-b002"></a>
<!-- pdf-source: page=237; block=2; confidence=0.99 -->
**Lemma 7.22.** For every constant $\gamma>0$ and every $\ell,m\in\mathbb{N}$, there exists an $(\ell,a)$-design $S_1,\ldots,S_m\subseteq[d]$ with $d=O(\ell^2/a)$ and $a=\gamma\cdot\log m$. Such a design can be constructed deterministically in time $\mathrm{poly}(m,d)$.

<a id="pdf-bf2ce5422088-p237-b003"></a>
<!-- pdf-source: page=237; block=3; confidence=0.97 -->
**Construction 7.23 (Nisan–Wigderson Generator).** Given f:{0,1}^ℓ→{0,1} and an (ℓ,a)-design S₁,…,S_m⊂[d], define G:{0,1}^d→{0,1}^m by G(x)=f(x|S₁)f(x|S₂)…f(x|S_m), where x|S is the length-|S| string formed from coordinates indexed by S.

<a id="pdf-bf2ce5422088-p237-b004"></a>
<!-- pdf-source: page=237; block=4; confidence=0.88 -->
**Theorem 7.24.** For the Nisan–Wigderson generator based on f:{0,1}^ℓ→{0,1} and an (ℓ,a)-design, if f is (s,1/2−ε/m) average-case hard, then G is a (t,ε) pseudorandom generator for t=s−m·a·2^a.

<a id="pdf-bf2ce5422088-p237-b005"></a>
<!-- pdf-source: page=237; block=5; confidence=0.99 -->
Theorem 7.19 follows from Theorem 7.24 by setting $\varepsilon=1/m$ and $a=\log m$, and observing that for $\ell=s^{-1}(m^3)$, then $t=s(\ell)-m\cdot a\cdot 2^a\ge m$, so we have an $(m,1/m)$ pseudorandom generator. The seed length is $d=O(\ell^2/\log m)=O(s^{-1}(\mathrm{poly}(m))^2/\log m)$.

<a id="pdf-bf2ce5422088-p237-b006"></a>
<!-- pdf-source: page=237; block=6; confidence=0.97 -->
**Proof.** If G is not a (t,ε)-PRG, Proposition 7.16 gives a nonuniform time-t next-bit predictor P and some i∈[m] such that Pr[P(f(X|S₁)…f(X|Sᵢ₋₁))=f(X|Sᵢ)]>1/2+ε/m (7.2). From P, construct A computing f with success probability greater than 1/2+ε/m.

<a id="pdf-bf2ce5422088-p238-b001"></a>
<!-- pdf-source: page=238; block=1; confidence=0.98 -->
Fix the bits outside the selected set so the predictor still succeeds with probability greater than $1/2+\varepsilon/m$. For each $j<i$, define $f_j(y)$ by completing $y$ with those fixed bits and evaluating $f$ on the positions indexed by $S_j$. Since $f_j$ depends on at most $a$ bits, it has a lookup circuit of size at most $a2^a$. Thus $A(y)=P(f_1(y),\ldots,f_{i-1}(y))$ runs in nonuniform time below $t+ma2^a=s$ and predicts $f(y)$ with error below $1/2-\varepsilon/m$, contradicting hardness. Hence $G$ is an $(m,\varepsilon)$-pseudorandom generator.

<a id="pdf-bf2ce5422088-p238-b002"></a>
<!-- pdf-source: page=238; block=2; confidence=0.94 -->
The construction applies to any average-case hard $f$; the assumption $f\in E$ is used only to obtain $G\in E$. The reduction also applies to nonuniform classes that efficiently compute functions on logarithmically many bits. Later constructions retain this black-box structure; improved parameters are noted but their output bits depend on the full truth table of $f$.

<a id="pdf-bf2ce5422088-p239-b001"></a>
<!-- pdf-source: page=239; block=1; confidence=0.93 -->
**Open Problem 7.25.** For every $\ell,s\in\mathbb N$, construct an explicit $H:\{0,1\}^{O(\ell)}\to(\{0,1\}^{\ell})^m$, with $m=s^{\Omega(1)}$, such that if $f$ is $(s,1/2-1/s)$-average-case hard and $G(x)=f(H_1(x))\cdots f(H_m(x))$, then $G$ is an $(m,1/m)$-pseudorandom generator. Here $H_i(x)$ is the $i$th component of $H(x)$.

<a id="pdf-bf2ce5422088-p239-b002"></a>
<!-- pdf-source: page=239; block=2; confidence=0.99 -->
## 7.4.3 Derandomizing Constant-depth Circuits

<a id="pdf-bf2ce5422088-p239-b003"></a>
<!-- pdf-source: page=239; block=3; confidence=0.98 -->
**Definition 7.26.** An unbounded fan-in circuit has input gates for variables, their negations, and constants $0,1$, and computation gates taking unbounded AND or OR. Its size is the number of computation gates; its depth is the maximum input-to-output path length. $AC^0$ consists of functions represented by a uniformly constructible sequence $(C_n)$ of such circuits, with size at most $n^c$ and depth at most constant $k$, computing the function on every $n$-bit input. Uniform constructibility means an efficient algorithm maps $1^n$ to $C_n$. $BPAC^0$ is defined similarly, allowing polynomially many random input bits and requiring output correctness probability at least $2/3$ for every input.

<a id="pdf-bf2ce5422088-p239-b004"></a>
<!-- pdf-source: page=239; block=4; confidence=0.99 -->
Internal NOT gates are unnecessary: De Morgan's laws move negations to inputs without increasing size or depth.

<a id="pdf-bf2ce5422088-p240-b001"></a>
<!-- pdf-source: page=240; block=1; confidence=0.97 -->
$AC^0$ admits superpolynomial lower bounds; parity supplies the average-case hardness used below.

<a id="pdf-bf2ce5422088-p240-b002"></a>
<!-- pdf-source: page=240; block=2; confidence=0.99 -->
**Theorem 7.27.** For all constant $k\in\mathbb{N}$ and every $\ell\in\mathbb{N}$, the function $\mathrm{PAR}_\ell:\{0,1\}^\ell\to\{0,1\}$ defined by $\mathrm{PAR}_\ell(x_1,\ldots,x_\ell)=\bigoplus_{i=1}^\ell x_i$ is $(s_k(\ell),1/2-1/s_k(\ell))$-average-case hard for nonuniform unbounded fan-in circuits of depth $k$ and size $s_k(\ell)=2^{2^{\Omega(\ell^{1/k})}}$.

<a id="pdf-bf2ce5422088-p240-b003"></a>
<!-- pdf-source: page=240; block=3; confidence=0.99 -->
The proof is omitted; the text points to the chapter notes and references.

<a id="pdf-bf2ce5422088-p240-b004"></a>
<!-- pdf-source: page=240; block=4; confidence=0.99 -->
The NW construction also requires that $AC^0$ compute arbitrary functions on logarithmically many bits.

<a id="pdf-bf2ce5422088-p240-b005"></a>
<!-- pdf-source: page=240; block=5; confidence=0.99 -->
**Lemma 7.28.** Every Boolean function $g:\{0,1\}^a\to\{0,1\}$ has a depth-2 circuit of size $2^a$.

<a id="pdf-bf2ce5422088-p240-b006"></a>
<!-- pdf-source: page=240; block=6; confidence=0.98 -->
The parity hardness and local computation fact yield a pseudorandom generator against constant-depth circuits.

<a id="pdf-bf2ce5422088-p240-b007"></a>
<!-- pdf-source: page=240; block=7; confidence=0.90 -->
**Theorem 7.29.** For every constant $k$ and every $m$, there is a polynomial-$m$-time computable $(m,1/m)$-pseudorandom generator $G_m:\{0,1\}^{\log^{O(k)}m}\to\{0,1\}^m$ fooling unbounded fan-in circuits of depth $k$ and size $m$.

<a id="pdf-bf2ce5422088-p240-b008"></a>
<!-- pdf-source: page=240; block=8; confidence=0.99 -->
**Proof.** This is proven similarly to Theorems 7.19 and 7.24, except that we take $f=\mathrm{PAR}_\ell$ rather than a hard function in $\mathrm{E}$, and we observe that the reduction can be implemented in a way that increases the depth by only an additive constant. Specifically, to obtain a pseudorandom generator fooling circuits of depth $k$ and size $m$, we use the hardness of $\mathrm{PAR}_\ell$ against unbounded fan-in circuits of depth $k'=k+2$ and size $m^2$, where $\ell=t_{k'}^{-1}(m^2)=O(\log^{k'}m)$. Then the seed length of $G$ is $O(\ell^2/a)<O(\ell^2)=\log^{O(k)}m$.

<a id="pdf-bf2ce5422088-p241-b001"></a>
<!-- pdf-source: page=241; block=1; confidence=0.99 -->
We now follow the steps of the proof of Theorem 7.19 to go from an adversary $T$ of depth $k$ violating the pseudorandomness of $G$ to a circuit $A$ of depth $k'$ calculating the parity function $\mathrm{PAR}_\ell$. If $T$ has depth $k$, then it can be verified that the next-bit predictor $P$ constructed in the proof of Proposition 7.16 also has depth $k$. Next, in the proof of Theorem 7.24, we obtain $A$ from $P$ by $A(y)=P(f_1(y)f_2(y)\cdots f_{i-1}(y))$ for some $i\in\{1,\ldots,m\}$, where each $f_j$ depends on at most $a$ bits of $y$. Applying Lemma 7.28 to each $f_j$, the size of $A$ is at most $(m-1)\cdot 2^a+m=m^2$ and the depth of $A$ is at most $k'=k+2$. This contradicts the hardness of $\mathrm{PAR}_\ell$.

<a id="pdf-bf2ce5422088-p241-b002"></a>
<!-- pdf-source: page=241; block=2; confidence=0.97 -->
**Corollary 7.30.** $\mathrm{BPAC}^0\subseteq\widetilde{\mathrm P}$.

<a id="pdf-bf2ce5422088-p241-b003"></a>
<!-- pdf-source: page=241; block=3; confidence=0.91 -->
With additional work, the inclusion can be strengthened to uniform constant-depth circuits of quasipolynomial size, using approximate majority. The generator also gives quasipolynomial-time derandomization for approximate DNF counting (Theorem 2.34); polynomial-time improvement is open.

<a id="pdf-bf2ce5422088-p241-b004"></a>
<!-- pdf-source: page=241; block=4; confidence=0.95 -->
**Open Problem 7.31.** Show that $\mathrm{BPAC}^0=\mathrm{AC}^0$, or even that $\mathrm{BPAC}^0\subseteq\mathrm P$.

<a id="pdf-bf2ce5422088-p241-b005"></a>
<!-- pdf-source: page=241; block=5; confidence=0.96 -->
**Open Problem 7.32 (Open Problem 2.36, restated).** Give a deterministic polynomial-time algorithm for approximately counting the satisfying assignments of a DNF formula.

<a id="pdf-bf2ce5422088-p242-b001"></a>
<!-- pdf-source: page=242; block=1; confidence=0.99 -->
## 7.5 Worst-Case/Average-Case Reductions and Locally Decodable Codes

<a id="pdf-bf2ce5422088-p242-b002"></a>
<!-- pdf-source: page=242; block=2; confidence=0.99 -->
There are known explicit functions $f:\{0,1\}^\ell\to\{0,1\}$ (e.g., Majority) for which every $\mathrm{AC}^0[2]$ circuit of depth $k$ computing $f$ has size at least $s_k(\ell)=2^{2^{\Omega(\ell^{1/k})}}$, but unfortunately the average-case hardness is much weaker than we need. These functions are only $(s_k(\ell),1/2-1/O(\ell))$-average-case hard, rather than $(s_k(\ell),1/2-1/s_k(\ell))$-average-case hard, so we can only obtain a small stretch using Theorem 7.24.

<a id="pdf-bf2ce5422088-p242-b003"></a>
<!-- pdf-source: page=242; block=3; confidence=0.99 -->
**Open Problem 7.33.** For every constant $k$ and every $m$, construct a mildly explicit $(m,1/4)$-pseudorandom generator $G_m:\{0,1\}^{m^{o(1)}}\to\{0,1\}^m$ fooling $\mathrm{AC}^0[2]$ circuits of depth $k$ (and size $m$).

<a id="pdf-bf2ce5422088-p242-b004"></a>
<!-- pdf-source: page=242; block=4; confidence=0.96 -->
The section shifts from constructions based on strong average-case hardness to constructions assuming worst-case hardness.

<a id="pdf-bf2ce5422088-p242-b005"></a>
<!-- pdf-source: page=242; block=5; confidence=0.98 -->
**Definition 7.34.** A Boolean function $f:\{0,1\}^n\to\{0,1\}$ is worst-case hard for time $t$ if every nonuniform probabilistic algorithm $A$ running in time $t$ has some input $x$ such that $\Pr[A(x)\ne f(x)]>1/3$, over $A$'s random coins.

<a id="pdf-bf2ce5422088-p242-b006"></a>
<!-- pdf-source: page=242; block=6; confidence=0.91 -->
For deterministic algorithms, the definition says that some input is computed incorrectly. (The discussion of the nonuniform probabilistic equivalence continues on the next page.)

<a id="pdf-bf2ce5422088-p243-b001"></a>
<!-- pdf-source: page=243; block=1; confidence=0.95 -->
More formally, given a function $f:\{0,1\}^\ell\to\{0,1\}$ that is worst-case hard for time $t=t(\ell)$, construct a function $\hat f:\{0,1\}^{O(\ell)}\to\{0,1\}$ such that $\hat f$ is average-case hard for time $t'=t^{\Omega(1)}$. Moreover, we would like $\hat f$ to be in $\mathrm{E}$ if $f$ is in $\mathrm{E}$. Whether we can obtain a similar result for $\mathrm{NP}$ is a major open problem.

<a id="pdf-bf2ce5422088-p243-b002"></a>
<!-- pdf-source: page=243; block=2; confidence=0.91 -->
Treat $f$ as a message of length $L=2^n$ and encode it by $\mathrm{Enc}:\{0,1\}^L\to\Sigma^{\hat L}$. Set $\hat f=\mathrm{Enc}(f)$, viewed as a function $\{0,1\}^{\hat n}\to\Sigma$ with $\hat n=\log\hat L$; the intended final alphabet is binary, though larger alphabets may be used in the development.

<a id="pdf-bf2ce5422088-p243-b003"></a>
<!-- pdf-source: page=243; block=3; confidence=0.93 -->
Assume an efficient algorithm $A$ agrees with $\hat f$ on a random coordinate with probability greater than $1-\delta$. Fixing its coins makes $A$ a received word with $d_H(A,\hat f)<\delta$. If $\mathrm{Dec}$ is an efficient $\delta$-decoder for $\mathrm{Enc}$, then $\mathrm{Dec}(A)=f$, yielding an efficient everywhere-computation algorithm for $f$ and contradicting its worst-case hardness, provided decoding fits the assumed time bound.

<a id="pdf-bf2ce5422088-p243-b004"></a>
<!-- pdf-source: page=243; block=4; confidence=0.93 -->
Standard decoding reads all $2^{\hat n}$ received symbols and outputs all $2^n$ message bits; the source continues beyond this page.

<a id="pdf-bf2ce5422088-p244-b001"></a>
<!-- pdf-source: page=244; block=1; confidence=0.98 -->
Section 7.5 introduces local decoding to turn worst-case hardness into average-case hardness with reduced computation.

<a id="pdf-bf2ce5422088-p244-b002"></a>
<!-- pdf-source: page=244; block=2; confidence=0.99 -->
**Definition 7.35.** For an encoding \(\mathrm{Enc}:\{0,1\}^L\to\Sigma^{\hat L}\), a probabilistic oracle algorithm \(\mathrm{Dec}\) locally \(\delta\)-decodes if, for every message \(f:[L]\to\{0,1\}\), its codeword \(\hat f=\mathrm{Enc}(f)\), and every \(g:[\hat L]\to\Sigma\) with \(d_H(g,\hat f)<\delta\), each coordinate \(x\in[L]\) satisfies \(\Pr[\mathrm{Dec}^g(x)=f(x)]\ge 2/3\), over the decoder's randomness.

<a id="pdf-bf2ce5422088-p244-b003"></a>
<!-- pdf-source: page=244; block=3; confidence=0.96 -->
The decoder uses oracle access to the received word to recover a requested message bit without reading the full input; the success probability can be amplified.

<a id="pdf-bf2ce5422088-p244-b004"></a>
<!-- pdf-source: page=244; block=4; confidence=0.99 -->
**Proposition 7.36.** If \(\mathrm{Enc}\) has a local \(\delta\)-decoding algorithm \(\mathrm{Dec}\) of nonuniform time at most \(t_{\mathrm{Dec}}\) (a Boolean circuit of that size with oracle gates), and \(f\) is worst-case hard for nonuniform time \(t\), then \(\hat f=\mathrm{Enc}(f)\) is \((t',\delta)\) average-case hard, where \(t'=t/t_{\mathrm{Dec}}\).

<a id="pdf-bf2ce5422088-p245-b001"></a>
<!-- pdf-source: page=245; block=1; confidence=0.98 -->
**Proof.** Apply the previous reduction with the oracle decoder \(\mathrm{Dec}^A\) in place of \(\mathrm{Dec}(A)\). Replacing each oracle gate of the decoder circuit by circuit \(A\) gives running time at most \(\mathrm{Time}(\mathrm{Dec})\cdot\mathrm{Time}(A)\). To obtain the uniform probabilistic version, choose and fix the coins of \(A\) randomly; by Markov's inequality, with high probability this increases its error by at most a constant factor. The text gives the resulting hardness as \((t',\delta/3)\).

<a id="pdf-bf2ce5422088-p245-b002"></a>
<!-- pdf-source: page=245; block=2; confidence=0.99 -->
Specifically, we would like the following parameters. (1) We want $\hat\ell=O(\ell)$, or equivalently $\hat L=\mathrm{poly}(L)$. This is because we measure hardness as a function of input length (which in turn translates to the relationship between output length and seed length of pseudorandom generators obtained via Theorem 7.19). In particular, when $t=2^{\Omega(\ell)}$, we'd like to achieve $t'=2^{\Omega(\hat\ell)}$. Since $t'<t$ in Proposition 7.36, this is only possible if $\hat\ell=O(\ell)$. (2) We would like $\mathrm{Enc}$ to be computable in time $2^{O(\hat\ell)}=\mathrm{poly}(\hat L)$, which is $\mathrm{poly}(L)$ if we satisfy the requirement $\hat L=\mathrm{poly}(L)$. This is because we want $f\in\mathrm{E}$ to imply $\hat f\in\mathrm{E}$. (3) We would like $\Sigma=\{0,1\}$ so that $\hat f$ is a Boolean function, and $\delta=1/2-\varepsilon$ so that $\hat f$ has sufficient average-case hardness for the pseudorandom generator construction of Theorem 7.24. (4) Since $\hat f$ will be average-case hard against time $t'=t/t_{\mathrm{Dec}}$, we would want the running time of $\mathrm{Dec}$ to be $t_{\mathrm{Dec}}=\mathrm{poly}(\ell,1/\varepsilon)$ so that we can take $\varepsilon=t^{\Omega(1)}$ and still have $t'=t^{\Omega(1)}/\mathrm{poly}(\ell)$.

<a id="pdf-bf2ce5422088-p245-b003"></a>
<!-- pdf-source: page=245; block=3; confidence=0.97 -->
The text notes that unique local decoding cannot attain radius \(1/2-\varepsilon\); the next section first targets a fixed constant radius, then introduces local list decoding to reach \(1/2-\varepsilon\).

<a id="pdf-bf2ce5422088-p246-b001"></a>
<!-- pdf-source: page=246; block=1; confidence=0.96 -->
The constructions are phrased as recovering codeword coordinates, yielding the definition of locally correctible codes.

<a id="pdf-bf2ce5422088-p246-b002"></a>
<!-- pdf-source: page=246; block=2; confidence=0.99 -->
**Definition 7.37.** For a code \(C\subseteq\Sigma^{\hat L}\), a probabilistic oracle algorithm \(\mathrm{Dec}\) locally \(\delta\)-corrects if for every \(\hat f\in C\) and every \(g:[\hat L]\to\Sigma\) with \(d_H(g,\hat f)<\delta\), each \(x\in[\hat L]\) satisfies \(\Pr[\mathrm{Dec}^g(x)=\hat f(x)]\ge 2/3\), over the decoder's coins.

<a id="pdf-bf2ce5422088-p246-b003"></a>
<!-- pdf-source: page=246; block=3; confidence=0.95 -->
Local correction implies standard local decoding when message symbols occur explicitly at designated codeword coordinates.

<a id="pdf-bf2ce5422088-p246-b004"></a>
<!-- pdf-source: page=246; block=4; confidence=0.99 -->
**Definition 7.38.** An encoding \(\mathrm{Enc}:\{0,1\}^L\to C\), for \(C\subseteq\Sigma^{\hat L}\), is systematic if a polynomial-time computable map \(I:[L]\to[\hat L]\) satisfies \(\hat f=\mathrm{Enc}(f)\) and \(\hat f(I(x))=f(x)\) for every message \(f\) and coordinate \(x\in[L]\), interpreting \(0,1\) canonically in \(\Sigma\).

<a id="pdf-bf2ce5422088-p246-b005"></a>
<!-- pdf-source: page=246; block=5; confidence=0.99 -->
**Lemma 7.39.** If \(\mathrm{Enc}:\{0,1\}^L\to C\) is systematic and \(C\) has a local \(\delta\)-corrector of time \(t\), then \(\mathrm{Enc}\) has a standard local \(\delta\)-decoder of time \(t+\mathrm{poly}(\log L)\).

<a id="pdf-bf2ce5422088-p246-b006"></a>
<!-- pdf-source: page=246; block=6; confidence=0.98 -->
**Proof.** Given corrector \(\mathrm{Dec}_1\) and systematic index map \(I\), decode message coordinate \(x\) by running \(\mathrm{Dec}_1^g(I(x))\).

<a id="pdf-bf2ce5422088-p246-b007"></a>
<!-- pdf-source: page=246; block=7; confidence=0.93 -->
The text notes that locally correctible codes are often called self-correctible codes.

<a id="pdf-bf2ce5422088-p247-b001"></a>
<!-- pdf-source: page=247; block=1; confidence=1.00 -->
## 7.5.1 Local Decoding Algorithms

<a id="pdf-bf2ce5422088-p247-b002"></a>
<!-- pdf-source: page=247; block=2; confidence=0.99 -->
The Hadamard code of message length $m$ comprises truth tables of all linear maps $c:\{0,1\}^m\to\{0,1\}$ over $\mathbb Z_2$.

<a id="pdf-bf2ce5422088-p247-b003"></a>
<!-- pdf-source: page=247; block=3; confidence=0.98 -->
**Proposition 7.40.** The Hadamard code $C\subseteq\{0,1\}^{2^m}$ of message length $m$ has a local $(1/4-\varepsilon)$-correcting algorithm with running time $\operatorname{poly}(m,1/\varepsilon)$.

<a id="pdf-bf2ce5422088-p247-b004"></a>
<!-- pdf-source: page=247; block=4; confidence=0.97 -->
**Proof.** Given oracle access to $g:\{0,1\}^m\to\{0,1\}$ with distance $d_H(g,c)<1/4-\varepsilon$ from an unknown linear $c$, recover $c(x)$ using $c(x)=c(x\oplus r)\oplus c(r)$. For uniform $r$, both queried points are uniform, so by a union bound the pair of oracle answers yields $c(x)$ with probability greater than $1/2+2\varepsilon$. Repetition and majority amplify success.

<a id="pdf-bf2ce5422088-p247-b005"></a>
<!-- pdf-source: page=247; block=5; confidence=0.98 -->
**Algorithm 7.41 (Local Corrector for Hadamard Code).** Input oracle $g:\{0,1\}^m\to\{0,1\}$, $x\in\{0,1\}^m$, and $\varepsilon>0$. Choose independent uniform $r_1,\ldots,r_t\in\{0,1\}^m$ for $t=O(1/\varepsilon^2)$; query $g(r_i)$ and $g(r_i\oplus x)$ for each $i$; output $\operatorname{maj}_{1\le i\le t}\{g(r_i)\oplus g(r_i\oplus x)\}$. If $d_H(g,c)<1/4-\varepsilon$, it returns $c(x)$ with probability at least $2/3$.

<a id="pdf-bf2ce5422088-p247-b006"></a>
<!-- pdf-source: page=247; block=6; confidence=0.95 -->
The decoder achieves correction radius arbitrarily close to $1/4$ with running time logarithmic in block length, but the code rate is exponentially small.

<a id="pdf-bf2ce5422088-p248-b001"></a>
<!-- pdf-source: page=248; block=1; confidence=0.99 -->
The $q$-ary Reed–Muller code of degree $d$ and dimension $m$ consists of polynomials $p:\mathbb F_q^m\to\mathbb F_q$ of total degree at most $d$ and has minimum distance $\delta=1-d/q$. It generalizes Hadamard and Reed–Solomon codes; the goal is to combine efficient local decoding with good rate.

<a id="pdf-bf2ce5422088-p248-b002"></a>
<!-- pdf-source: page=248; block=2; confidence=0.99 -->
**Theorem 7.42.** If $d\le q/9$ and $q\ge36$, the $q$-ary Reed–Muller code of degree $d$ and dimension $m$ has a local $1/12$-correcting algorithm running in time $\operatorname{poly}(m,q)$.

<a id="pdf-bf2ce5422088-p248-b003"></a>
<!-- pdf-source: page=248; block=3; confidence=0.98 -->
The running time is roughly the $m$th root of block length $\widehat L=q^m$; for $m=1$ decoding may inspect the whole word, while for sufficiently large $m$ it accesses only a small fraction. The proof strategy restricts to random lines, where codewords become univariate degree-$d$ Reed–Solomon codewords that can be globally decoded.

<a id="pdf-bf2ce5422088-p248-b004"></a>
<!-- pdf-source: page=248; block=4; confidence=0.94 -->
For $x,y\in\mathbb F^m$, define $\ell_{x,y}:\mathbb F\to\mathbb F^m$ by $\ell_{x,y}(t)=x+ty$. For $a\in\mathbb F$ and $b\in\mathbb F\setminus\{0\}$, $\ell_{x+ay,by}$ has the same image as $\ell_{x,y}$; that image is called an unparameterized line. If $y=0$, the parameterized line consists only of $x$.

<a id="pdf-bf2ce5422088-p249-b001"></a>
<!-- pdf-source: page=249; block=1; confidence=0.99 -->
For a function $g:\mathbb F^m\to\mathbb F$ and line $\ell:\mathbb F\to\mathbb F^m$, $g|_\ell=g\circ\ell$. If $p$ has total degree at most $d$, then $p|_\ell$ has univariate degree at most $d$.

<a id="pdf-bf2ce5422088-p249-b002"></a>
<!-- pdf-source: page=249; block=2; confidence=0.96 -->
To recover $p(x)$ from $g$ at distance less than $\delta$, choose a random line through $x$. Each point other than $x$ is uniform over $\mathbb F^m$ under this choice, so oracle values there are likely correct. When the error rate is sufficiently small relative to degree, for example $\delta=1/(3(d+1))$, interpolate from $d+1$ nonzero line parameters to recover the value at parameter $0$.

<a id="pdf-bf2ce5422088-p249-b003"></a>
<!-- pdf-source: page=249; block=3; confidence=0.98 -->
**Algorithm 7.43 (Local Corrector for Reed–Muller Code I).** Input oracle $g:\mathbb F^m\to\mathbb F$, point $x\in\mathbb F^m$, and degree $d$. Choose uniform $y\in\mathbb F^m$ and set $\ell=\ell_{x,y}$. For fixed $\alpha_0,\ldots,\alpha_d\in\mathbb F\setminus\{0\}$, query $\beta_i=g|_\ell(\alpha_i)=g(\ell(\alpha_i))$. Find the unique polynomial $q$ of degree at most $d$ with $q(\alpha_i)=\beta_i$ for all $i$, and output $q(0)$.

<a id="pdf-bf2ce5422088-p249-b004"></a>
<!-- pdf-source: page=249; block=4; confidence=0.98 -->
**Claim 7.44.** If $g$ has distance less than $\delta=1/(3(d+1))$ from a polynomial $p$ of degree at most $d$, then Algorithm 7.43 outputs $p(x)$ with probability greater than $2/3$.

<a id="pdf-bf2ce5422088-p249-b005"></a>
<!-- pdf-source: page=249; block=5; confidence=0.99 -->
**Proof of Claim:** Observe that for all $x\in\mathbb F^m$ and $\alpha_i\in\mathbb F\setminus\{0\}$, $\ell_{x,y}(\alpha_i)$ is uniformly random in $\mathbb F^m$ over the choice of $y\mathrel{\stackrel{R}{\leftarrow}}\mathbb F^m$. This

<a id="pdf-bf2ce5422088-p250-b001"></a>
<!-- pdf-source: page=250; block=1; confidence=0.99 -->
implies that for each $i$, $\Pr_\ell[g|_\ell(\alpha_i)\ne p|_\ell(\alpha_i)]<\delta=\frac{1}{3(d+1)}$. By a union bound, $\Pr_\ell[\exists i,\ g|_\ell(\alpha_i)\ne p|_\ell(\alpha_i)]<(d+1)\cdot\delta=\frac13$. Thus, with probability greater than $2/3$, we have $\forall i,\ g|_\ell(\alpha_i)=p|_\ell(\alpha_i)$ and hence $q(0)=p(x)$. The running time of the algorithm is $\operatorname{poly}(m,q)$.

<a id="pdf-bf2ce5422088-p250-b002"></a>
<!-- pdf-source: page=250; block=2; confidence=0.99 -->
To tolerate distance \(1/12\), the algorithm queries the entire line and uses Reed–Solomon decoding in place of interpolation.

<a id="pdf-bf2ce5422088-p250-b003"></a>
<!-- pdf-source: page=250; block=3; confidence=0.95 -->
**Algorithm 7.45.** Input an oracle \(g:\mathbb F^m\to\mathbb F\), point \(x\in\mathbb F^m\), and degree \(d\), with \(q=|\mathbb F|\ge36\) and \(d\le q/9\). Choose uniform \(y\in\mathbb F^m\) and let \(\ell=\ell_{x,y}:\mathbb F\to\mathbb F^m\) be the line through \(x\) in direction \(y\). Query \(g\) on all of \(\ell\), obtaining \(g|_\ell\). Use a \(1/3\)-decoder for the degree-\(d\), \(q\)-ary Reed–Solomon code to find the unique polynomial \(r\) at distance below \(1/3\) from \(g|_\ell\), if one exists, and output \(r(0)\). The cited decoder is obtained from list decoding up to radius \(1-2d/q\); uniqueness follows because \(1/3\) is below half the minimum distance \(1-d/q\).

<a id="pdf-bf2ce5422088-p251-b001"></a>
<!-- pdf-source: page=251; block=1; confidence=0.99 -->
**Claim 7.46.** If \(g\) is at distance less than \(\delta=1/12\) from a polynomial \(p\) of degree at most \(d\), and \(q=|\mathbb F|\ge36\), \(d\le q/9\), then Algorithm 7.45 outputs \(p(x)\) with probability greater than \(2/3\).

<a id="pdf-bf2ce5422088-p251-b002"></a>
<!-- pdf-source: page=251; block=2; confidence=0.99 -->
**Proof of Claim:** The expected distance (between $g|_\ell$ and $p|_\ell$) is small: $\mathbb E_\ell[d_H(g|_\ell,p|_\ell)]<\frac1q+\delta=\frac1{36}+\frac1{12}=\frac19$, where the term $1/q$ is due to the fact that the point $x$ is not random. Therefore, by Markov’s Inequality, $\Pr[d_H(g|_\ell,p|_\ell)\ge1/3]\le1/3$. Thus, with probability at least $2/3$, $p|_\ell$ is the unique polynomial of degree at most $d$ at distance less than $1/3$ from $g|_\ell$ and thus the decoder outputs $p|_\ell$.

<a id="pdf-bf2ce5422088-p251-b003"></a>
<!-- pdf-source: page=251; block=3; confidence=1.00 -->
## 7.5.2 Low-Degree Extensions

<a id="pdf-bf2ce5422088-p251-b004"></a>
<!-- pdf-source: page=251; block=4; confidence=0.98 -->
Recall that to obtain locally decodable codes from locally correctible codes, we need to exhibit systematic encoding: given $f:[L]\to\{0,1\}$, we want to encode it as a Reed–Muller codeword $\hat f:[\hat L]\to\Sigma$ such that: the encoding time is $2^{O(\ell)}=\operatorname{poly}(L)$; $\hat\ell=O(\ell)$, or equivalently $\hat L=\operatorname{poly}(L)$; and the code is systematic. The usual coefficient encoding is not systematic. Instead, the message should correspond to evaluations of the polynomial at certain points; once those points are chosen, the task is to interpolate their values to a low-degree polynomial defined everywhere. The simplest approach is to use the Boolean hypercube as the set of evaluation points.

<a id="pdf-bf2ce5422088-p252-b001"></a>
<!-- pdf-source: page=252; block=1; confidence=0.98 -->
**Lemma 7.47 (multilinear extension).** For every \(f:\{0,1\}^n\to\{0,1\}\) and finite field \(\mathbb F\), there is a unique polynomial \(\hat f:\mathbb F^n\to\mathbb F\) whose restriction to \(\{0,1\}^n\) equals \(f\), with degree at most one in each variable and total degree at most \(n\).

<a id="pdf-bf2ce5422088-p252-b002"></a>
<!-- pdf-source: page=252; block=2; confidence=0.99 -->
**Proof.** Define \(\hat f(x)=\sum_{\alpha\in\{0,1\}^n} f(\alpha)\delta_\alpha(x)\), where \(\delta_\alpha(x)=\prod_{i:\alpha_i=1}x_i\prod_{i:\alpha_i=0}(1-x_i)\). On Boolean inputs, \(\delta_\alpha(x)=1\) exactly when \(\alpha=x\), so the extension agrees with \(f\). Each variable has degree at most one; uniqueness is omitted in the source.

<a id="pdf-bf2ce5422088-p252-b003"></a>
<!-- pdf-source: page=252; block=3; confidence=0.99 -->
Since the total degree of the multilinear extension can be as large as $\ell$, we need $q\ge9\ell$ for the local corrector of Theorem 7.42 to apply. The encoding time is $2^{O(\ell)}$, as computing a single point of $\hat f$ requires summing over $2^\ell$ elements, and we have $2^\ell$ points on which to compute $\hat f$. The input length is $\hat\ell=\ell\log q=\Theta(\ell\log\ell)$, which is slightly larger than the target $\hat\ell=O(\ell)$. To solve this, we reduce the dimension of the polynomial $\hat f$ by changing the embedding of the domain of $f$: instead of interpreting $\{0,1\}^\ell\subseteq\mathbb F^\ell$ as an embedding in $\mathbb F^\ell$, we map $\{0,1\}^\ell$ to $H^m$ for some subset $H\subseteq\mathbb F$, and embed it in $\mathbb F^m$.

<a id="pdf-bf2ce5422088-p253-b001"></a>
<!-- pdf-source: page=253; block=1; confidence=0.99 -->
More precisely, we fix a subset $H\subseteq\mathbb F$ of size $|H|=\lceil\sqrt q\rceil$. Choose $m=\lceil\ell/\log|H|\rceil$, and fix some efficient one-to-one mapping from $\{0,1\}^\ell$ into $H^m$. With this mapping, view $f$ as a function $f:H^m\to\mathbb F$.

<a id="pdf-bf2ce5422088-p253-b002"></a>
<!-- pdf-source: page=253; block=2; confidence=0.98 -->
**Lemma 7.48.** For a finite field $F$, subset $H\subseteq F$, integer $m\in\mathbb N$, and function $f:H^m\to F$, there is a unique extension $\hat f:F^m\to F$ agreeing with $f$ on $H^m$ and having degree at most $|H|-1$ in each variable; hence total degree at most $m(|H|-1)$.

<a id="pdf-bf2ce5422088-p253-b003"></a>
<!-- pdf-source: page=253; block=3; confidence=0.99 -->
Using $|H|=\lceil\sqrt q\rceil$, the total degree of $\hat f$ is at most $d=\ell\sqrt q$. So we can apply the local corrector of Theorem 7.42, as long as $q\ge81\ell^2$ (so that $d\le q/9$). The input length is $\hat\ell=m\cdot\log q=O(\ell)$, as desired. The code is systematic as long as our mapping from $\{0,1\}^\ell$ to $H^m$ is efficient. The image is only a subcode of the Reed–Muller code; this is not a problem, because any subcode of a locally correctible code is also locally correctible, and the rate loss is acceptable.

<a id="pdf-bf2ce5422088-p253-b004"></a>
<!-- pdf-source: page=253; block=4; confidence=0.99 -->
Combining Theorem 7.42 with Lemmas 7.48 and 7.39 yields a locally decodable code.

<a id="pdf-bf2ce5422088-p253-b005"></a>
<!-- pdf-source: page=253; block=5; confidence=0.99 -->
**Proposition 7.49.** For every $L\in\mathbb N$, there is an explicit code $\mathrm{Enc}:\{0,1\}^L\to\Sigma^{\hat L}$ with $\hat L=\operatorname{poly}(L)$ and $|\Sigma|=\operatorname{poly}(\log L)$, admitting a local $(1/12)$-decoder running in time $\operatorname{poly}(\log L)$.

<a id="pdf-bf2ce5422088-p254-b001"></a>
<!-- pdf-source: page=254; block=1; confidence=0.99 -->
Proposition 7.36 gives the following conversion from worst-case hardness to average-case hardness.

<a id="pdf-bf2ce5422088-p254-b002"></a>
<!-- pdf-source: page=254; block=2; confidence=0.91 -->
**Proposition 7.50.** If some $f:\{0,1\}^L\to\{0,1\}$ in $E$ is worst-case hard against nonuniform time $t(L)$, then some $\hat f:\{0,1\}^{O(L)}\to\{0,1\}^{O(\log L)}$ in $E$ is $(t'(L),1/12)$ average-case hard, where $t'(L)=t(L)/\operatorname{poly}(L)$.

<a id="pdf-bf2ce5422088-p254-b003"></a>
<!-- pdf-source: page=254; block=3; confidence=0.94 -->
Concatenate the code from Proposition 7.49 with a Hadamard code to obtain Boolean codewords; since the intermediate alphabet has size $\operatorname{polylog}(L)$, brute-force unique decoding takes $\operatorname{polylog}(L)$ time.

<a id="pdf-bf2ce5422088-p254-b004"></a>
<!-- pdf-source: page=254; block=4; confidence=0.99 -->
**Theorem 7.51.** For every $L\in\mathbb N$, there is an explicit code $\mathrm{Enc}:\{0,1\}^L\to\{0,1\}^{\hat L}$ with $\hat L=\operatorname{poly}(L)$ and a local $(1/48)$-decoder running in time $\operatorname{poly}(\log L)$.

<a id="pdf-bf2ce5422088-p254-b005"></a>
<!-- pdf-source: page=254; block=5; confidence=0.96 -->
**Theorem 7.52.** If some $f:\{0,1\}^L\to\{0,1\}$ in $E$ is worst-case hard against time $t(L)$, then some $\hat f:\{0,1\}^{O(L)}\to\{0,1\}$ in $E$ is $(t'(L),1/48)$ average-case hard, where $t'(L)=t(L)/\operatorname{poly}(L)$.

<a id="pdf-bf2ce5422088-p254-b006"></a>
<!-- pdf-source: page=254; block=6; confidence=0.89 -->
Theorem 7.51's decoder makes $\operatorname{poly}(\log L)$ queries. Constant-degree Reed–Muller codes yield constant-query locally decodable codes with blocklength $\hat L=\exp(L^{1/(q-1)})$; a newer result gives $\exp(L^{o(1)})$, while polynomial blocklength remains open.

<a id="pdf-bf2ce5422088-p254-b007"></a>
<!-- pdf-source: page=254; block=7; confidence=0.95 -->
The Hadamard concatenation resembles the Goldreich–Levin hardcore predicate, but brute-force unique decoding suffices for these parameters.

<a id="pdf-bf2ce5422088-p255-b001"></a>
<!-- pdf-source: page=255; block=1; confidence=0.99 -->
**Open Problem 7.53.** Do binary codes exist with constant query complexity, constant decoding distance $\delta>0$, and blocklength polynomial in message length?

<a id="pdf-bf2ce5422088-p255-b002"></a>
<!-- pdf-source: page=255; block=2; confidence=0.98 -->
Locally decodable codes connect to private information retrieval and program self-correction.

<a id="pdf-bf2ce5422088-p255-b003"></a>
<!-- pdf-source: page=255; block=3; confidence=0.97 -->
If a function's program is a codeword (for example, a determinant polynomial as a Reed–Muller codeword), a local decoder can correct a program that errs on a small fraction of inputs and recover correct answers on all inputs with high probability.

<a id="pdf-bf2ce5422088-p255-b004"></a>
<!-- pdf-source: page=255; block=4; confidence=0.96 -->
Section 7.6 turns worst-case hardness into pseudorandom generators using local list decoding.

<a id="pdf-bf2ce5422088-p255-b005"></a>
<!-- pdf-source: page=255; block=5; confidence=0.98 -->
The prior section obtains constant average-case hardness (Theorem 7.52); this section aims to amplify it, for example to $1/2-\varepsilon$.

<a id="pdf-bf2ce5422088-p255-b006"></a>
<!-- pdf-source: page=255; block=6; confidence=0.98 -->
Define $f'(x_1,\ldots,x_k)=(\hat f(x_1),\ldots,\hat f(x_k))$ by evaluating $\hat f$ on $k$ independent inputs.

<a id="pdf-bf2ce5422088-p256-b001"></a>
<!-- pdf-source: page=256; block=1; confidence=0.84 -->
Independent products and XOR can amplify average-case hardness, but increase input length by a factor of the repetition parameter. The section instead pursues local list-decoding to obtain a function that is $?](1/2-\varepsilon)$?]-hard while keeping input length linear; hardness amplification also has coding-theoretic applications.

<a id="pdf-bf2ce5422088-p256-b002"></a>
<!-- pdf-source: page=256; block=2; confidence=0.99 -->
## 7.6.2 Definition

<a id="pdf-bf2ce5422088-p256-b003"></a>
<!-- pdf-source: page=256; block=3; confidence=0.94 -->
A coordinate-wise set of candidate symbols can be uninformative when the alphabet is small relative to the list. Instead, the decoder first produces labels for nearby codewords, then decodes a requested coordinate using a chosen label.

<a id="pdf-bf2ce5422088-p257-b001"></a>
<!-- pdf-source: page=257; block=1; confidence=0.98 -->
The first randomized oracle algorithm \(\mathrm{Dec}_1\) outputs advice labels \(a_1,\ldots,a_s\) from oracle access to received word \(g\) and code parameters. The second, \(\mathrm{Dec}_2\), uses \(g\), a coordinate \(x\), and a selected label \(a_i\) to return the corresponding decoded value.

<a id="pdf-bf2ce5422088-p257-b002"></a>
<!-- pdf-source: page=257; block=2; confidence=0.98 -->
**Definition 7.54.** A local \(\delta\)-list-decoding algorithm for \(\mathrm{Enc}\) consists of probabilistic oracle algorithms \((\mathrm{Dec}_1,\mathrm{Dec}_2)\) such that for every received word \(g\) and every codeword \(\widehat f=\mathrm{Enc}(f)\) with \(d_H(\widehat f,g)<\delta\), with probability at least \(2/3\) over \((a_1,\ldots,a_s)\leftarrow \mathrm{Dec}_1^g\), there is an \(i\in[s]\) for which
\[
\forall x,\quad \Pr[\mathrm{Dec}_2^g(x,a_i)=f(x)]\ge 2/3.
\]
No separate list-size bound is imposed; \(s\) is bounded by the running time of \(\mathrm{Dec}_1\).

<a id="pdf-bf2ce5422088-p257-b003"></a>
<!-- pdf-source: page=257; block=3; confidence=0.96 -->
For local list correction, the second phase recovers symbols of the codeword rather than the message; candidate outputs need not themselves be codewords or lie near \(g\), so some labels may be junk.

<a id="pdf-bf2ce5422088-p258-b001"></a>
<!-- pdf-source: page=258; block=1; confidence=0.94 -->
As in Lemma 7.39, local \(\delta\)-list correction implies local \(\delta\)-list decoding for systematic codes. The next proposition converts worst-case hardness into average-case hardness using local list decoding.

<a id="pdf-bf2ce5422088-p258-b002"></a>
<!-- pdf-source: page=258; block=2; confidence=0.98 -->
**Proposition 7.55.** Let \(\mathrm{Enc}\) be an error-correcting code with local \(\delta\)-list-decoding algorithm \((\mathrm{Dec}_1,\mathrm{Dec}_2)\), where \(\mathrm{Dec}_2\) runs in time at most \(t_{\mathrm{Dec}}\). If \(f\) is worst-case hard for non-uniform time \(t\), then \(\widehat f=\mathrm{Enc}(f)\) is \((t',\delta)\)-average-case hard, where \(t'=t/t_{\mathrm{Dec}}\).

<a id="pdf-bf2ce5422088-p258-b003"></a>
<!-- pdf-source: page=258; block=3; confidence=0.95 -->
**Proof.** Assume for contradiction that a non-uniform algorithm \(A\) of time \(t'\) computes \(\widehat f\) with error probability less than \(\delta\). Applying the local list decoder with \(A\) as its received-word oracle, some output label \(a_i\) yields \(\mathrm{Dec}_2^A(\cdot,a_i)=f(\cdot)\) everywhere. Hardwiring \(a_i\) gives a non-uniform algorithm of time at most \(\mathrm{time}(A)\,\mathrm{time}(\mathrm{Dec}_2)\le t\), contradicting worst-case hardness.

<a id="pdf-bf2ce5422088-p258-b004"></a>
<!-- pdf-source: page=258; block=4; confidence=0.94 -->
The reduction uses non-uniform advice to select the correct decoding from the list. For black-box constructions this is essential; uniform amplification results can instead use structural information about the hard function to identify it.

<a id="pdf-bf2ce5422088-p258-b005"></a>
<!-- pdf-source: page=258; block=5; confidence=0.99 -->
## 7.6.3 Local List-Decoding Reed–Muller Codes

<a id="pdf-bf2ce5422088-p258-b006"></a>
<!-- pdf-source: page=258; block=6; confidence=0.99 -->
**Theorem 7.56.** There is a universal constant $c$ such that the $q$-ary Reed–Muller code of degree $d$ and dimension $m$ over $\mathbb F_q$ can be locally $(1-\varepsilon)$-list-corrected in time $\operatorname{poly}(q,m)$ for $\varepsilon=c\sqrt{d/q}$.

<a id="pdf-bf2ce5422088-p259-b001"></a>
<!-- pdf-source: page=259; block=1; confidence=0.99 -->
Note that the distance at which list decoding can be done approaches $1$ as $q/d\to\infty$. It matches the bound for list-decoding Reed–Solomon codes up to the constant $c$. Moreover, as the dimension $m$ increases, the running time of the decoder ($\operatorname{poly}(q,m)$) becomes much smaller than the block length $q^m\cdot\log q$, at the price of a reduced rate $\binom{m+d}{m}/q^m$.

<a id="pdf-bf2ce5422088-p259-b002"></a>
<!-- pdf-source: page=259; block=2; confidence=0.99 -->
**Proof.** Given g:F^m→F that is (1−ε)-close to an unknown degree-at-most-d polynomial p and a target x∈F^m, use a first-stage algorithm to select a random y∈F^m and output all advice pairs (y,z), z∈F. The second stage uses advice (y,p(y)) to recover p(x) from g restricted to the line through x and y, by Reed–Solomon list decoding and selection using the value at y.

<a id="pdf-bf2ce5422088-p259-b003"></a>
<!-- pdf-source: page=259; block=3; confidence=0.99 -->
**Algorithm 7.57.** Input: oracle g:F^m→F and degree parameter d. Choose y uniformly at random from F^m; output {(y,z): z∈F}.

<a id="pdf-bf2ce5422088-p259-b004"></a>
<!-- pdf-source: page=259; block=4; confidence=0.98 -->
This simple first stage ignores g; using g could improve its running time and output-list size, but those improvements are not needed here.

<a id="pdf-bf2ce5422088-p259-b005"></a>
<!-- pdf-source: page=259; block=5; confidence=0.98 -->
On the line through x and y, list-decode the restriction of g. If exactly one listed polynomial agrees with the advice value p(y) at y, return its value at x; correctness follows when that polynomial is p restricted to the line.

<a id="pdf-bf2ce5422088-p259-b006"></a>
<!-- pdf-source: page=259; block=6; confidence=0.99 -->
**Algorithm 7.58.** Input: oracle g:F^m→F, target x∈F^m, advice (y,z)∈F^m×F, and degree parameter d. (The steps continue on page 260.)

<a id="pdf-bf2ce5422088-p260-b001"></a>
<!-- pdf-source: page=260; block=1; confidence=0.99 -->
**Algorithm 7.58.** Define ℓ(t)=x+t(y−x), so ℓ(0)=x and ℓ(1)=y. Apply the (1−ε/2)-list decoder for Reed–Solomon codes (Theorem 5.19) to g restricted to ℓ, obtaining all univariate polynomials q_i agreeing with that restriction on more than an ε/2 fraction of points. If there is a unique i with q_i(1)=z, output q_i(0); otherwise fail.

<a id="pdf-bf2ce5422088-p260-b002"></a>
<!-- pdf-source: page=260; block=2; confidence=0.98 -->
**Proof.** It is enough to compute p(x) correctly for more than 11/12 of targets x, after which Theorem 7.42’s unique local correcting algorithm applies. The required probability guarantee is stated in Claim 7.59.

<a id="pdf-bf2ce5422088-p260-b003"></a>
<!-- pdf-source: page=260; block=3; confidence=0.99 -->
**Claim 7.59.** Suppose g:F^m→F agrees with a degree-at-most-d polynomial p on more than an ε fraction of inputs. For at least half of y∈F^m, more than 11/12 of lines ℓ through y satisfy: (1) agr(g|_ℓ,p|_ℓ)>ε/2; (2) no degree-at-most-d univariate polynomial q other than p|_ℓ has agr(g|_ℓ,q)>ε/2 and q(y)=p(y).

<a id="pdf-bf2ce5422088-p260-b004"></a>
<!-- pdf-source: page=260; block=4; confidence=0.99 -->
**Proof.** It suffices to show each condition in Claim 7.59 fails with probability below 0.01 for a uniformly random point y and random line ℓ through y; Markov’s inequality then yields the stated conclusion. For (1), the q points on a random line are pairwise independent uniform samples from F^m, so expected agreement equals agr(g,p)>ε. The pairwise-independent tail inequality (Proposition 3.28) bounds the probability that the line agreement is at most ε/2.

<a id="pdf-bf2ce5422088-p261-b001"></a>
<!-- pdf-source: page=261; block=1; confidence=0.97 -->
For a random line ℓ, Proposition 3.28 gives Pr[agr(g|_ℓ,p|_ℓ)≤ε/2] < 1/[q(ε/2)^2]. With ε=c√(d/q), this is below 0.01 for sufficiently large constant c.

<a id="pdf-bf2ce5422088-p261-b002"></a>
<!-- pdf-source: page=261; block=2; confidence=0.99 -->
To prove Item 7.59, imagine first choosing the line $\ell$ uniformly at random from all lines in $\mathbb F^m$, and then choosing $y$ uniformly at random from the points on $\ell$, reparameterizing $\ell$ so that $\ell(1)=y$. Let $q_1,\ldots,q_t$ be all polynomials of degree at most $d$, other than $p|_\ell$, that have agreement greater than $\varepsilon/2$ with $g|_\ell$. By Reed–Solomon list-decodability, $t=O(\sqrt{q/d})$. Since two distinct polynomials can agree in at most $d$ points, $\Pr_y[\exists i:q_i(1)=p(1)]\le t\cdot d/q=O(\sqrt{d/q})$. This can be made smaller than $0.01$ for a large enough choice of $c$ in $\varepsilon=c\sqrt{d/q}$.

<a id="pdf-bf2ce5422088-p261-b003"></a>
<!-- pdf-source: page=261; block=3; confidence=0.99 -->
## 7.6.4 Putting it Together

<a id="pdf-bf2ce5422088-p261-b004"></a>
<!-- pdf-source: page=261; block=4; confidence=0.99 -->
To obtain a locally list-decodable code, use the low-degree extension (Lemma 7.48) to obtain a systematic encoding. For messages of length $\ell=\log L$, apply Lemma 7.48 with $|H|=\lceil\sqrt q\rceil$ and $m=\lceil\ell/\log|H|\rceil$, giving total degree $d\le\sqrt q\,\ell$. To decode from a $1-\varepsilon$ fraction of errors using Theorem 7.56, we need $c\sqrt{d/q}\le\varepsilon$, which follows if $q\ge c^2\ell^2/\varepsilon^4$.

<a id="pdf-bf2ce5422088-p262-b001"></a>
<!-- pdf-source: page=262; block=1; confidence=0.99 -->
## 7.6 Local List Decoding and PRGs from Worst-Case Hardness

<a id="pdf-bf2ce5422088-p262-b002"></a>
<!-- pdf-source: page=262; block=2; confidence=0.99 -->
**Theorem 7.60.** For every \(L\in\mathbb N\) and \(\varepsilon>0\), there is an explicit code \(\mathrm{Enc}:\{0,1\}^L\to\widehat\Sigma^{\widehat L}\), with \(\widehat L=\operatorname{poly}(L,1/\varepsilon)\) and \(|\widehat\Sigma|=\operatorname{poly}(\log L,1/\varepsilon)\), admitting a local \((1-\varepsilon)\)-list decoder running in time \(\operatorname{poly}(\log L,1/\varepsilon)\).

<a id="pdf-bf2ce5422088-p262-b003"></a>
<!-- pdf-source: page=262; block=3; confidence=0.98 -->
Concatenation with a Hadamard code yields a binary version of the locally list-decodable code.

<a id="pdf-bf2ce5422088-p262-b004"></a>
<!-- pdf-source: page=262; block=4; confidence=0.99 -->
**Theorem 7.61.** For every \(L\in\mathbb N\) and \(\varepsilon>0\), there is an explicit binary code \(\mathrm{Enc}:\{0,1\}^L\to\{0,1\}^{\widehat L}\), with \(\widehat L=\operatorname{poly}(L,1/\varepsilon)\), having a local \((1/2-\varepsilon)\)-list decoder running in time \(\operatorname{poly}(\log L,1/\varepsilon)\).

<a id="pdf-bf2ce5422088-p262-b005"></a>
<!-- pdf-source: page=262; block=5; confidence=0.98 -->
Applying Proposition 7.55 gives the following worst-case to average-case hardness amplification.

<a id="pdf-bf2ce5422088-p262-b006"></a>
<!-- pdf-source: page=262; block=6; confidence=0.97 -->
**Theorem 7.62.** For \(s:\mathbb N\to\mathbb N\), suppose that there is a function \(f:\{0,1\}^{\ell}\to\{0,1\}\) in \(\mathbf E\) that is worst-case hard against nonuniform time \(s(\ell)\), where \(s(\ell)\) is computable in time \(2^{O(\ell)}\). Then there exists \(\widehat f:\{0,1\}^{O(\ell)}\to\{0,1\}\) in \(\mathbf E\) that is \((1/2-1/s'(\ell))\) average-case hard against (nonuniform) time \(s'(\ell)=t(\ell)^{\Omega(1)}/\operatorname{poly}(\ell)\).

<a id="pdf-bf2ce5422088-p262-b007"></a>
<!-- pdf-source: page=262; block=7; confidence=0.98 -->
Combining the preceding hardness result with Theorem 7.19 and Corollary 7.20 gives a worst-case hardness based PRG construction.

<a id="pdf-bf2ce5422088-p262-b008"></a>
<!-- pdf-source: page=262; block=8; confidence=0.97 -->
**Theorem 7.63.** Suppose \(s:\mathbb N\to\mathbb N\) and \(f\in E\) is worst-case hard for nonuniform time \(s(\ell)\) at every input length \(\ell\), where \(s(\ell)\) is computable in time \(2^{O(\ell)}\). For every \(m\in\mathbb N\), there is a mildly explicit \((m,1/m)\)-pseudorandom generator \(G:\{0,1\}^{d(m)}\to\{0,1\}^m\) with \(d(m)=O\!\left(s^{-1}(\operatorname{poly}(m))^2/\log m\right)\).

<a id="pdf-bf2ce5422088-p262-b009"></a>
<!-- pdf-source: page=262; block=9; confidence=0.99 -->
**Corollary 7.64.** Suppose \(s:\mathbb N\to\mathbb N\) and \(f\in E=\mathrm{DTIME}(2^{O(\ell)})\) is worst-case hard for nonuniform time \(s(\ell)\) at every input length \(\ell\). The corollary's three consequences continue on page 263.

<a id="pdf-bf2ce5422088-p263-b001"></a>
<!-- pdf-source: page=263; block=1; confidence=0.94 -->
**Corollary 7.64.** Under the stated hardness hypothesis: (1) if \(s(\ell)=2^{\Omega(\ell)}\), then \(\mathrm{BPP}=\mathrm P\); (2) if \(s(\ell)=2^{\ell^{\Omega(1)}}\), then \(\mathrm{BPP}\subseteq\widetilde{\mathrm P}\); (3) if \(s(\ell)=\ell^{\omega(1)}\), then \(\mathrm{BPP}\subseteq\mathrm{SUBEXP}\).

<a id="pdf-bf2ce5422088-p263-b002"></a>
<!-- pdf-source: page=263; block=2; confidence=0.97 -->
These hypotheses posit functions in \(E\) with high circuit complexity; the text notes that SAT is in \(E\) and is conjectured to require circuits of size \(2^{\Omega(\ell)}\). The resulting alternative is full BPP derandomization or substantially faster nonuniform algorithms for SAT.

<a id="pdf-bf2ce5422088-p263-b003"></a>
<!-- pdf-source: page=263; block=3; confidence=0.98 -->
Problem 7.1 gives a converse from PRGs to circuit lower bounds. Theorem 7.63 is close to this converse, except its seed length has an extra factor \(1/\log m\) relative to \(O(s^{-1}(\operatorname{poly}(m)))\); a different, more algebraic construction is known to remove the gap. For Corollary 7.64, only a partial converse is known (Section 8.2.2).

<a id="pdf-bf2ce5422088-p263-b004"></a>
<!-- pdf-source: page=263; block=4; confidence=0.99 -->
## Technical Comment

<a id="pdf-bf2ce5422088-p263-b005"></a>
<!-- pdf-source: page=263; block=5; confidence=0.96 -->
The superpolynomial circuit lower bound in Corollary 7.64(3) is stronger than \(E\not\subseteq\mathrm{P/poly}\): the latter only gives a function and a superpolynomial lower bound at infinitely many lengths, while Theorem 7.63 and Corollary 7.64 require hardness at every length (equivalently, exclusion from \(i.o.\text{-}\mathrm{P/poly}\)). This stronger hypothesis supports PRGs for every output length and hence derandomization correct at every length.

<a id="pdf-bf2ce5422088-p264-b001"></a>
<!-- pdf-source: page=264; block=1; confidence=0.95 -->
Moving the infinitely-often qualification from the hypothesis to the conclusion yields variants such as \(E\not\subseteq\mathrm{P/poly}\Rightarrow\mathrm{BPP}\subseteq i.o.\text{-}\mathrm{SUBEXP}\). The text regards input-length oscillations that would distinguish these outcomes as implausible.

<a id="pdf-bf2ce5422088-p264-b002"></a>
<!-- pdf-source: page=264; block=2; confidence=0.99 -->
## 7.7 Connections to Other Pseudorandom Objects

<a id="pdf-bf2ce5422088-p264-b003"></a>
<!-- pdf-source: page=264; block=3; confidence=0.99 -->
### 7.7.1 Black-Box Constructions

<a id="pdf-bf2ce5422088-p264-b004"></a>
<!-- pdf-source: page=264; block=4; confidence=0.96 -->
The preceding construction uses any \(f:\{0,1\}^{\ell}\to\{0,1\}\) as an oracle to define \(G_f:\{0,1\}^d\to\{0,1\}^m\); membership of \(f\) in \(E\) is used to infer that \(G_f\) is computable in \(E\). A distinguisher \(T\) for \(G_f(U_d)\) versus \(U_m\) is used as an oracle to construct an efficient nonuniform algorithm \(\mathrm{Red}^T\) computing \(f\); efficiency of \(T\) ensures efficiency of the reduction, contradicting worst-case hardness.

<a id="pdf-bf2ce5422088-p264-b005"></a>
<!-- pdf-source: page=264; block=5; confidence=0.98 -->
**Definition 7.65.** Let \(G^f:[D]\to[M]\) be a deterministic algorithm that is defined for every oracle \(f:[L]\to\{0,1\}\), let \(t,k\) be positive integers such that \(k\le t\), and let \(\varepsilon>0\). We say that \(G\) is a \((t,k,\varepsilon)\) black-box PRG construction if there is a randomized oracle algorithm \(\mathrm{Red}\), running in time \(t\), such that for every \(f:[L]\to\{0,1\}\) and \(T:[M]\to\{0,1\}\) such that
\[
\Pr[T(G^f(U_{[D]}))=1]-\Pr[T(U_{[M]})=1]>\varepsilon,
\]
then there is an advice string \(z\in[K]\) such that
\[
\forall x\in[L]\quad \Pr[\mathrm{Red}^T(x,z)=f(x)]\ge 2/3,
\]
where the probability is taken over the coin tosses of \(\mathrm{Red}\), and \(K=2^k\).

<a id="pdf-bf2ce5422088-p265-b001"></a>
<!-- pdf-source: page=265; block=1; confidence=0.91 -->
**Definition 7.65.** For integers $k\le t$ and $\varepsilon>0$, $G$ is a $(t,k,\varepsilon)$ black-box PRG construction if a randomized oracle algorithm $\mathrm{Red}$ runs in time $t$ and, for every $f:[L]\to\{0,1\}$ and $T:[M]\to\{0,1\}$, whenever $\Pr[T(G_f(U_{[D]}))=1]-\Pr[T(U_{[M]})=1]>\varepsilon$, there is advice $z\in[K]$ such that for all $x\in[L]$, $\Pr[\mathrm{Red}^T(x,z)=f(x)]\ge 2/3$, with probability over Red's coins.

<a id="pdf-bf2ce5422088-p265-b002"></a>
<!-- pdf-source: page=265; block=2; confidence=0.84 -->
The definition separates reduction time $t$ from advice length $k$ (with $k\le t$); advice may optionally depend on reduction randomness, at a cost of increasing its length through repetition.

<a id="pdf-bf2ce5422088-p265-b003"></a>
<!-- pdf-source: page=265; block=3; confidence=0.94 -->
A black-box construction applied to a sufficiently hard function yields an ordinary pseudorandom generator.

<a id="pdf-bf2ce5422088-p265-b004"></a>
<!-- pdf-source: page=265; block=4; confidence=0.99 -->
**Proposition 7.66.** If \(G\) is a \((t,k,\varepsilon)\) black-box PRG construction and \(f\) has nonuniform worst-case hardness at least \(s\), then \(G^f\) is an \((s/\widetilde O(t),\varepsilon)\) pseudorandom generator.

<a id="pdf-bf2ce5422088-p266-b001"></a>
<!-- pdf-source: page=266; block=1; confidence=0.99 -->
## 7.7 Connections to Other Pseudorandom Objects

<a id="pdf-bf2ce5422088-p266-b002"></a>
<!-- pdf-source: page=266; block=2; confidence=0.96 -->
The next result presents Theorem 7.63 as a black-box construction with explicit parameters.

<a id="pdf-bf2ce5422088-p266-b003"></a>
<!-- pdf-source: page=266; block=3; confidence=0.99 -->
**Theorem 7.67.** For every constant \(\gamma>0\), and every \(\ell,m\in\mathbb N\), and every \(\varepsilon>0\), there is a \((t,k,\varepsilon)\) black-box PRG construction \(G^f:\{0,1\}^d\to\{0,1\}^m\) that is defined for every oracle \(f:\{0,1\}^{\ell}\to\{0,1\}\), with the following properties:

1. (Mild) Explicitness: \(G^f\) is computable in uniform time \(\operatorname{poly}(m,2^{\ell})\) given an oracle for \(f\).
2. Seed length: \(d=O((\ell+\log(1/\varepsilon))^2/\log m)\).
3. Reduction running time: \(t=\operatorname{poly}(m,1/\varepsilon)\).
4. Reduction advice length: \(k=m^{1+\gamma}+O(\ell+\log(m/\varepsilon))\).

<a id="pdf-bf2ce5422088-p266-b004"></a>
<!-- pdf-source: page=266; block=4; confidence=0.83 -->
**Proof sketch.** Encode $f$ using the locally list-decodable code of Theorem 7.61 at distance $1/2-\varepsilon'$ with $\varepsilon'=\varepsilon/m$, obtaining $\widehat f:\{0,1\}^{\widehat\ell}\to\{0,1\}$ where $\widehat\ell=O(\ell+\log(1/\varepsilon))$. Apply the Nisan–Wigderson generator (Construction 7.23) using a $(\widehat\ell,\gamma\log m)$ design. The design and code parameters give seed length and mild explicitness; the cited reductions give time and advice bounds. Assume $m>\ell$, since otherwise no stretch is needed.

<a id="pdf-bf2ce5422088-p266-b005"></a>
<!-- pdf-source: page=266; block=5; confidence=0.85 -->
The code-decoding advice is a pair $(y,z)\in F^v\times F$, where $|F|=q=\operatorname{poly}(\ell,1/\varepsilon)$ and $v\log|F|=\widehat\ell=O(\ell+\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p267-b001"></a>
<!-- pdf-source: page=267; block=1; confidence=0.86 -->
The Nisan–Wigderson reduction uses $\log m$ bits to choose the predictor index $i$, $m-i-1$ bits to hardwire other distinguisher inputs, and at most $(i-1)m^\gamma$ bits for truth tables of the functions $f_j$ on intersections of design sets. Thus advice is at most $O(\ell+\log(1/\varepsilon))+m-i-1+(i-1)m^\gamma=m^{1+\gamma}+O(\ell+\log(1/\varepsilon))$.

<a id="pdf-bf2ce5422088-p267-b002"></a>
<!-- pdf-source: page=267; block=2; confidence=0.95 -->
Black-box constructions transfer higher computational complexity of the hard function to the generator, and higher test complexity to the resulting indistinguishability guarantee.

<a id="pdf-bf2ce5422088-p267-b003"></a>
<!-- pdf-source: page=267; block=3; confidence=0.95 -->
A nondeterministic version follows, using hardness against nonuniform algorithms with an NP oracle.

<a id="pdf-bf2ce5422088-p267-b004"></a>
<!-- pdf-source: page=267; block=4; confidence=0.98 -->
**Theorem 7.68.** For \(s:\mathbb N\to\mathbb N\), suppose there is a function \(f\in\mathbf{NE}\cap\mathrm{co\mbox{-}NE}\) such that for every input length \(\ell\in\mathbb N\), \(f\) is worst-case hard for nonuniform algorithms running in time \(s(\ell)\) with an \(\mathbf{NP}\) oracle (equivalently, Boolean circuits with SAT gates), where \(s(\ell)\) is computable in time \(2^{O(\ell)}\). Then for every \(m\in\mathbb N\), there is a pseudorandom generator \(G:\{0,1\}^{d(m)}\to\{0,1\}^m\) with seed length \(d(m)=O(s^{-1}(\operatorname{poly}(m))^2/\log m)\) such that \(G\) is \((m,1/m)\)-pseudorandom against nonuniform algorithms with an \(\mathbf{NP}\) oracle, and \(G\) is computable in nondeterministic time \(2^{O(d(m))}\) (meaning that there is a nondeterministic algorithm that on input \(x\) outputs \(G(x)\) on at least one computation path and outputs either \(G(x)\) or “fail” on all computation paths).

<a id="pdf-bf2ce5422088-p268-b001"></a>
<!-- pdf-source: page=268; block=1; confidence=0.98 -->
Section 7.7 discusses applications and lower-complexity versions of pseudorandom-generator constructions.

<a id="pdf-bf2ce5422088-p268-b002"></a>
<!-- pdf-source: page=268; block=2; confidence=0.99 -->
**Definition 7.69.** A language $L$ is in AM if there are a probabilistic polynomial-time verifier $V$ and polynomials $m,p$ such that, for every $n$-bit input $x$,

- if $x\in L$, then $\Pr_{r\leftarrow\{0,1\}^{m(n)}}[\exists y\in\{0,1\}^{p(n)}:V(x,r,y)=1]\ge 2/3$;
- if $x\notin L$, then the same probability is at most $1/3$.

<a id="pdf-bf2ce5422088-p268-b003"></a>
<!-- pdf-source: page=268; block=3; confidence=0.98 -->
AM is also characterized by constant-round interactive proofs with polynomial communication between an unbounded prover and a probabilistic polynomial-time verifier. Graph Nonisomorphism is in AM but is not known to be in NP.

<a id="pdf-bf2ce5422088-p268-b004"></a>
<!-- pdf-source: page=268; block=4; confidence=0.99 -->
**Corollary 7.70.** If there is a function \(f\in\mathbf{NE}\cap\mathrm{co\mbox{-}NE}\) that, on inputs of length \(\ell\), is worst-case hard for nonuniform algorithms running in time \(2^{\Omega(\ell)}\) with an \(\mathbf{NP}\) oracle, then \(\mathbf{AM} = \mathbf{NP}\).

<a id="pdf-bf2ce5422088-p268-b005"></a>
<!-- pdf-source: page=268; block=5; confidence=0.87 -->
The stated hardness assumption is asserted to be weaker than $\mathrm{E}=\mathrm{DTIME}(2^{O(n)})\not\subseteq\bigcap_{\epsilon>0}\mathrm{DSPACE}(2^{\epsilon n})$. Black-box constructions may also apply to lower complexity classes when the generator or reduction is computable there (for example, in $\mathrm{AC}^0$).

<a id="pdf-bf2ce5422088-p269-b001"></a>
<!-- pdf-source: page=269; block=1; confidence=0.99 -->
The subsection relates computational pseudorandom generators to information-theoretic pseudorandom objects through black-box constructions.

<a id="pdf-bf2ce5422088-p269-b002"></a>
<!-- pdf-source: page=269; block=2; confidence=0.95 -->
Theorem 7.67 is unconditional; black-box constructions can be interpreted information-theoretically and placed in the list-decoding framework of Section 5.3.

<a id="pdf-bf2ce5422088-p269-b003"></a>
<!-- pdf-source: page=269; block=3; confidence=0.95 -->
**Construction 7.71.** Given an oracle algorithm $G^f:[D]\to[M]$ defined for every Boolean function $f:[n]\to\{0,1\}$, set $N=2^n$ and define $\Gamma:[N]\times[D]\to[M]$ by $\Gamma(f,y)=G^f(y)$, identifying each truth table of $f$ with an element of $[N]\cong\{0,1\}^n$.

<a id="pdf-bf2ce5422088-p269-b004"></a>
<!-- pdf-source: page=269; block=4; confidence=0.96 -->
**Proposition 7.72.** For $G^f$ and $\Gamma$ as in Construction 7.71, $G^f$ is an $(\infty,k,\epsilon)$ black-box PRG construction if and only if, for every $T\subseteq[M]$,
\[
|\mathrm{LIST}_{\Gamma}(T,\mu(T)+\epsilon)|\le K,
\qquad K=2^k.
\]

<a id="pdf-bf2ce5422088-p269-b005"></a>
<!-- pdf-source: page=269; block=5; confidence=0.98 -->
\(\Rightarrow.\) Suppose \(G^f\) is an \((\infty,k,\varepsilon)\) black-box PRG construction. Then \(f\) is in \(\operatorname{LIST}_{\Gamma}(T,\mu(T)+\varepsilon)\) iff \(T\) distinguishes \(G^f(U_{[D]})\) from \(U_{[M]}\) with advantage greater than \(\varepsilon\).

<a id="pdf-bf2ce5422088-p270-b001"></a>
<!-- pdf-source: page=270; block=1; confidence=0.99 -->
The number of functions \(f\) in \(\operatorname{LIST}_{\Gamma}(T,\mu(T)+\varepsilon)\) is at most \(K\): each such function has an advice string \(z\in[K]\) such that \(\mathrm{Red}^{T}(x,z)\) computes \(f\) everywhere. Conversely, suppose that for every \(T\subseteq[M]\), \(L=|\operatorname{LIST}_{\Gamma}(T,\mu(T)+\varepsilon)|\le K\). Then we can define \(\mathrm{Red}^{T}(x,z)=f_z(x)\), where \(f_1,\ldots,f_L\) are any fixed enumeration of the elements of \(\operatorname{LIST}_{\Gamma}(T,\mu(T)+\varepsilon)\).

<a id="pdf-bf2ce5422088-p270-b002"></a>
<!-- pdf-source: page=270; block=2; confidence=0.94 -->
This list-size characterization matches those for averaging samplers and randomness extractors. Theorem 7.67 consequently yields a sampler and extractor with the stated parameters.

<a id="pdf-bf2ce5422088-p270-b003"></a>
<!-- pdf-source: page=270; block=3; confidence=0.91 -->
**Theorem 7.73.** For every constant $\gamma>0$, $n\in\mathbb N$, $k\in[0,n]$, and $\epsilon>0$, there is an explicit $(k,\epsilon)$ extractor $\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with seed length
\[
d=O\!\left(\frac{\log^2(n/\epsilon)}{\log k}\right)
\]
and output length $m\ge k^{1-\gamma}$.

<a id="pdf-bf2ce5422088-p270-b004"></a>
<!-- pdf-source: page=270; block=4; confidence=0.97 -->
**Proof Sketch.** Without loss of generality, assume that \(n\) is a power of 2, namely \(n=2^{\ell}=L\). Let \(G^f(y):\{0,1\}^d\to\{0,1\}^m\) be the \((t,k_0,\varepsilon_0)\) black-box PRG construction of Theorem 7.67, which takes a function \(f:\{0,1\}^{\ell}\to\{0,1\}\) and has \(k_0=m^{1+\gamma}+O(\ell+\log(m/\varepsilon_0))\), and let \(\operatorname{Ext}(f,y)=\Gamma(f,y)=G^f(y)\). By Propositions 7.72 and 6.23, \(\operatorname{Ext}\) is a \((k_0+\log(1/\varepsilon_0),2\varepsilon_0)\) extractor. Setting \(\varepsilon=2\varepsilon_0\) and \(k=k_0+\log(1/\varepsilon_0)\), we have output length
\[
m=(k-O(\ell+\log(m/\varepsilon)))^{1-\gamma}\ge k^{1-\gamma}-O(\ell+\log(m/\varepsilon)).
\]
We can increase the output length to \(k^{1-\gamma}\) by increasing the seed length by \(O(\ell+\log(m/\varepsilon))\). The total seed length is then
\[
d=O\left(\frac{(\ell+\log(1/\varepsilon))^2}{\log m}+\ell+\log(m/\varepsilon)\right)=O\left(\frac{\log^2(n/\varepsilon)}{\log k}\right).
\]

<a id="pdf-bf2ce5422088-p270-b005"></a>
<!-- pdf-source: page=270; block=5; confidence=0.96 -->
The text begins comparing Theorem 7.73 with Theorem 6.36 and Corollary 6.39, noting its output-length parameters are weaker; the comparison continues beyond the supplied pages.

<a id="pdf-bf2ce5422088-p271-b001"></a>
<!-- pdf-source: page=271; block=1; confidence=0.98 -->
The construction has seed length $O(\log n)$ when $k=n^{\Omega(1)}$. It sets $\operatorname{Ext}(f,y)=(\widehat f(y|_{S_1}),\ldots,\widehat f(y|_{S_m}))$, where $\widehat f$ encodes $f$ in a locally list-decodable code and $S_1,\ldots,S_m$ form a design. Using a $(1/2-\varepsilon/(2m),\operatorname{poly}(m/\varepsilon))$ list-decodable code requires only $O(\log(m/\varepsilon))$ advice bits to index a decoding; a Reed–Solomon code concatenated with a Hadamard code is one option.

<a id="pdf-bf2ce5422088-p271-b002"></a>
<!-- pdf-source: page=271; block=2; confidence=0.98 -->
A black-box PRG can be viewed as an extractor by supplying a function sampled from a high-min-entropy source: the source makes the function information-theoretically hard, allowing statistical uniformity of the output. Specifically, if $f\leftarrow F$ and $H_\infty(F)\ge k+\log(1/\varepsilon)$, then for every fixed interpreter $A$, the probability that some $k$-bit string $z$ makes $A(\cdot,z)$ compute $f$ everywhere is at most $\varepsilon$.

<a id="pdf-bf2ce5422088-p271-b003"></a>
<!-- pdf-source: page=271; block=3; confidence=1.00 -->
The text begins to introduce black-box conversion of worst-case hardness to average-case hardness; the definition continues on the next page.

<a id="pdf-bf2ce5422088-p272-b001"></a>
<!-- pdf-source: page=272; block=1; confidence=0.98 -->
**Definition 7.74.** For deterministic $\operatorname{Amp}_f:[D]\to[q]$ defined for every oracle $f:[n]\to\{0,1\}$, call $\operatorname{Amp}$ a $(t,k,\varepsilon)$ black-box worst-case-to-average-case hardness amplifier if a probabilistic oracle reduction $\operatorname{Red}$ runs in time $t$ and, for every $g:[D]\to[q]$ satisfying $\Pr[g(U_{[D]})=\operatorname{Amp}_f(U_{[D]})]>1/q+\varepsilon$, there exists advice $z\in[K]$, where $K=2^k$, such that for all $x\in[n]$, $\Pr[\operatorname{Red}^g(x,z)=f(x)]\ge 2/3$. The latter probability is over the coins of $\operatorname{Red}$.

<a id="pdf-bf2ce5422088-p272-b002"></a>
<!-- pdf-source: page=272; block=2; confidence=0.97 -->
This parallels local $(1-1/q-\varepsilon)$ list decoding with $\operatorname{Amp}_f$ as the encoding and $\operatorname{Red}^g$ as the local decoder. The amplifier definition omits an efficient first-phase procedure for generating candidate advice. Without a running-time bound on $\operatorname{Red}$, the condition is ordinary $(1-1/q-\varepsilon,K)$ list decoding; bounded-time black-box PRGs can likewise be viewed as extractors or averaging samplers with efficient local decoding given advice.

<a id="pdf-bf2ce5422088-p272-b003"></a>
<!-- pdf-source: page=272; block=3; confidence=0.95 -->
**Theorem.** A black-box PRG $G^f:\{0,1\}^d\to\{0,1\}^m$ must have a reduction using at least $k\ge m-d-\log(1/\varepsilon)-1$ advice bits. Otherwise, Propositions 7.72 and 6.23 imply a $(k,2\varepsilon)$ extractor producing $m$ almost-uniform bits from a source of min-entropy below $k-d-1$, impossible when $\varepsilon<1/4$.

<a id="pdf-bf2ce5422088-p273-b001"></a>
<!-- pdf-source: page=273; block=1; confidence=1.00 -->
Indeed, notions of black-box reduction have been used in other settings as well, most notably to produce a very fine understanding of the relations between different cryptographic primitives, meaning which ones can be constructed from each other via black-box constructions.

<a id="pdf-bf2ce5422088-p273-b002"></a>
<!-- pdf-source: page=273; block=2; confidence=1.00 -->
## 7.8 Exercises

<a id="pdf-bf2ce5422088-p273-b003"></a>
<!-- pdf-source: page=273; block=3; confidence=0.79 -->
**Problem 7.1 (PRGs imply hard functions).** Assume that for every $m$ there is an $(m,1/m)$ pseudorandom generator $G_m:\{0,1\}^{d(m)}\to\{0,1\}^m$. Show that E contains a function $f:\{0,1\}^{\ell}\to\{0,1\}$ with nonuniform worst-case hardness $t(\ell)=\Omega(d^{-1}(\ell-1))$. In particular, if $d(m)=O(\log m)$, show $t(\ell)=2^{\Omega(\ell)}$. Hint: consider a prefix of the generator's output.

<a id="pdf-bf2ce5422088-p273-b004"></a>
<!-- pdf-source: page=273; block=4; confidence=0.72 -->
**Problem 7.2 (Equivalence of lower bounds for EXP and E).** Prove that E contains a function $f:\{0,1\}^{\ell}\to\{0,1\}$ of circuit complexity $\ell^{\omega(1)}$ iff EXP does. The hint considers $f'(x_1\cdots x_\ell)=f(x_1\cdots x_{\ell'})$. Determine whether the same argument works when the lower bound is replaced by $2^{\ell^{\Omega(1)}}$ (the exponent notation in the extracted text is partly corrupted).

<a id="pdf-bf2ce5422088-p273-b005"></a>
<!-- pdf-source: page=273; block=5; confidence=0.92 -->
**Problem 7.3 (Limitations of cryptographic generators).** (1) Prove a cryptographic pseudorandom generator cannot have seed length $d(m)=O(\log m)$. (2) Prove that cryptographic PRGs, even with seed length $d(m)=m-1$, imply $\mathrm{NP}\not\subseteq\mathrm{P/poly}$. (3) Identify where the proofs fail if one assumes only an $(m^c,1/m^c)$ PRG for a fixed constant $c$.

<a id="pdf-bf2ce5422088-p273-b006"></a>
<!-- pdf-source: page=273; block=6; confidence=0.98 -->
**Problem 7.4 (Deterministic approximate counting).** Using the PRG for constant-depth circuits in Theorem 7.29, give deterministic quasipolynomial-time algorithms for the listed problems; the list continues beyond the supplied text.

<a id="pdf-bf2ce5422088-p274-b001"></a>
<!-- pdf-source: page=274; block=1; confidence=0.99 -->
## Section 7.8: Exercises

<a id="pdf-bf2ce5422088-p274-b002"></a>
<!-- pdf-source: page=274; block=2; confidence=1.00 -->
(1) Given a constant-depth circuit $C$ and $\varepsilon>0$, approximate the fraction of inputs $x$ such that $C(x)=1$ to within an additive error of $\varepsilon$. (2) Given a DNF formula $\varphi$ and $\varepsilon>0$, approximate the number of assignments $x$ such that $\varphi(x)=1$ to within a multiplicative fraction of $(1+\varepsilon)$. You may restrict your attention to $\varphi$ in which all clauses contain the same number of literals. (Hint: Study the randomized DNF counting algorithm of Theorem 2.34.) Note that these are not decision problems, whereas classes such as BPP and BPAC$_0$ are classes of decision problems. One of the points of this problem is to show how derandomization can be used for other types of problems.

<a id="pdf-bf2ce5422088-p274-b003"></a>
<!-- pdf-source: page=274; block=3; confidence=1.00 -->
**Problem 7.5 (Strong Pseudorandom Generators).** By analogy with strong extractors, call a function $G:\{0,1\}^d\to\{0,1\}^m$ a $(t,\varepsilon)$ strong pseudorandom generator iff the function $G'(x)=(x,G(x))$ is a $(t,\varepsilon)$ pseudorandom generator. (1) Show that there do not exist strong cryptographic pseudorandom generators. (2) Show that the Nisan–Wigderson generator (Theorem 7.24) is a strong pseudorandom generator. (3) Suppose that for all constants $\alpha>0$, there is a strong and fully explicit $(m,\varepsilon(m))$ pseudorandom generator $G:\{0,1\}^{m^\alpha}\to\{0,1\}^m$. Show that for every language $L\in\mathrm{BPP}$, there is a deterministic polynomial-time algorithm $A$ such that for all $n$, $\Pr_{x\sim_R\{0,1\}^n}[A(x)\ne\chi_L(x)]\le 1/2^n+\varepsilon(\operatorname{poly}(n))$.

<a id="pdf-bf2ce5422088-p274-b004"></a>
<!-- pdf-source: page=274; block=4; confidence=0.90 -->
The exercise’s preceding instruction requires algorithms to run in time $2^{\mathrm{poly}(\log n,\log(1/\varepsilon))}$, where $n$ is the circuit or formula size and $\varepsilon$ is the accuracy parameter.

<a id="pdf-bf2ce5422088-p275-b001"></a>
<!-- pdf-source: page=275; block=1; confidence=0.95 -->
**Problem 7.5(4).** Prove that every $L\in\mathrm{BPAC}^0$ has an $\mathrm{AC}^0$ algorithm $A$ such that $\Pr_{x\sim\{0,1\}^n}[A(x)\ne\chi_L(x)]\le 1/n$. The source cautions that error reduction requires care.

<a id="pdf-bf2ce5422088-p275-b002"></a>
<!-- pdf-source: page=275; block=2; confidence=0.99 -->
## Problem 7.6: Private information retrieval

<a id="pdf-bf2ce5422088-p275-b003"></a>
<!-- pdf-source: page=275; block=3; confidence=0.97 -->
**Definition (q-server PIR scheme).** A database $D\in\{0,1\}^n$ is replicated at $q$ noncommunicating servers. On index $i\in[n]$, the user samples coins $r$ and sends queries $(x_1,\ldots,x_q)=U(i,r)$; server $j$ replies $y_j=S_j(x_j,D)$, and the user outputs $U(i,r,x_1,\ldots,x_q)$, which must equal $D_i$. Privacy requires that for each server, the distribution of its query $x_j$ over $r$ be independent of $i$.

<a id="pdf-bf2ce5422088-p275-b004"></a>
<!-- pdf-source: page=275; block=4; confidence=0.98 -->
**Definition (q-query smooth code).** A code $\mathrm{Enc}:\{0,1\}^n\to\widehat{\Sigma}^{\widehat n}$ is $q$-query smooth if a probabilistic oracle decoder satisfies, for every message $x$ and index $i\in[n]$, $\Pr[\mathrm{Dec}^{\mathrm{Enc}(x)}(i)=x_i]=1$, makes $q$ nonadaptive queries, and each query is uniformly distributed in $[\widehat n]$. The oracle in this definition is an uncorrupted codeword.

<a id="pdf-bf2ce5422088-p275-b005"></a>
<!-- pdf-source: page=275; block=5; confidence=0.92 -->
The exercises use smooth codes to derive locally decodable codes and PIR schemes; converses are also known under slight relaxations of the definitions. A footnote mentions computational security as an alternative privacy notion, requiring that learning the requested entry be computationally infeasible for the database holder.

<a id="pdf-bf2ce5422088-p276-b001"></a>
<!-- pdf-source: page=276; block=1; confidence=0.99 -->
## Section 7.8: Exercises

<a id="pdf-bf2ce5422088-p276-b002"></a>
<!-- pdf-source: page=276; block=2; confidence=0.94 -->
(1) Show that a decoder for a $q$-query smooth code is a local $(1/(3q))$-decoder for $\mathrm{Enc}$. (2) Show that each such code $\mathrm{Enc}:\{0,1\}^n\to\widehat{\Sigma}^{\widehat n}$ yields a $q$-server PIR scheme with communication at most $q(\log\widehat n+\log|\Sigma|)$ bits per requested entry. (3) Using Reed–Muller codes, construct a $\mathrm{polylog}(n)$-server PIR scheme with $\mathrm{polylog}(n)$ communication per entry for $n$-bit databases. For constant $q$, an optimal systematic Reed–Muller encoding as in Problem 5.4 gives communication $O(n^{1/(q-1)})$.

<a id="pdf-bf2ce5422088-p276-b003"></a>
<!-- pdf-source: page=276; block=3; confidence=0.98 -->
**Problem 7.7.** For each constant $\varepsilon>0$, show there is a constant $\gamma>0$ such that the degree-$d$, dimension-$m$ $q$-ary Reed–Muller code has a local $(1/2-\varepsilon)$-decoding algorithm whenever $d\le\gamma q$. This is unique decoding, not list decoding; the decoder should run in $\mathrm{poly}(m,q)$ time.

<a id="pdf-bf2ce5422088-p276-b004"></a>
<!-- pdf-source: page=276; block=4; confidence=0.98 -->
**Definition ( $(t,\varepsilon)$ hitting set).** A set $H_m\subseteq\{0,1\}^m$ is a $(t,\varepsilon)$ hitting set if every nonuniform algorithm $T$ running in time $t$ that accepts more than an $\varepsilon$ fraction of $m$-bit strings accepts at least one element of $H_m$.

<a id="pdf-bf2ce5422088-p276-b005"></a>
<!-- pdf-source: page=276; block=5; confidence=1.00 -->
Show that if, for every $m$, we can construct an $(m,1/2)$ hitting set $H_m$ in time $s(m)\ge m$, then $\mathrm{RP}\subseteq\bigcup_c\mathrm{DTIME}(s(n^c))$. In particular, if $s(m)=\operatorname{poly}(m)$, then $\mathrm{RP}=\mathrm{P}$.

<a id="pdf-bf2ce5422088-p276-b006"></a>
<!-- pdf-source: page=276; block=6; confidence=0.97 -->
**Problem 7.8(2).** Show that a $(t,\varepsilon)$ pseudorandom generator $G_m:\{0,1\}^d\to\{0,1\}^m$ computable in time $s$ yields a constructible $(t,\varepsilon)$ hitting set $H_m$ in time $2^d s$.

<a id="pdf-bf2ce5422088-p277-b001"></a>
<!-- pdf-source: page=277; block=1; confidence=1.00 -->
(3) Show that if, for every $m$, we can construct an $(m,1/2)$ hitting set $H_m$ in time $s(m)=\operatorname{poly}(m)$, then $\mathrm{BPP}=\mathrm{P}$. (Hint: this can be proven in two ways. One uses Problem 3.1 and the other uses a variant of Problem 7.1 together with Corollary 7.64. How do the parameters for general $s(m)$ compare?) (4) Define the notion of a $(t,k,\varepsilon)$ black-box construction of hitting-set generators, and show that, when $t=\infty$, such constructions are equivalent to constructions of dispersers (Definition 6.19).

<a id="pdf-bf2ce5422088-p277-b002"></a>
<!-- pdf-source: page=277; block=2; confidence=0.98 -->
**Definition.** For functions t: ℕ → ℕ and ε: ℕ → [0,1], a sequence G_m: {0,1}^{d(m)} → {0,1}^m is a (t(m), ε(m)) pseudorandom generator against uniform algorithms when the ensembles G(U_{d(m)}) and U_m are uniformly computationally indistinguishable (Definition 7.2).

<a id="pdf-bf2ce5422088-p277-b003"></a>
<!-- pdf-source: page=277; block=3; confidence=1.00 -->
Suppose that we have a mildly explicit $(m,1/m)$ pseudorandom generator against uniform algorithms that has seed length $d(m)$. Show that for every language $L\in\mathrm{BPP}$, there exists a deterministic algorithm $A$ running in time $2^{d(\operatorname{poly}(n))}\cdot\operatorname{poly}(n)$ on inputs of length $n$ such that: (1) $\Pr[A(X_n)=L(X_n)]\ge 1-1/n^2$, where $X_n\sim_R\{0,1\}^n$ and $L(\cdot)$ is the characteristic function of $L$. (The exponent of $2$ in $n^2$ is arbitrary, and can be replaced by any constant.) (2) $\Pr[A(X_n)=L(X_n)]\ge 1-1/n^2$, for any random variable $X_n$ distributed on $\{0,1\}^n$ that is samplable in time $n^2$.

<a id="pdf-bf2ce5422088-p277-b004"></a>
<!-- pdf-source: page=277; block=4; confidence=1.00 -->
Call a function $G:\{0,1\}^d\to\{0,1\}^m$ a $(t,\ell,\varepsilon)$ pseudorandom generator against bounded-nonuniformity algorithms iff for every probabilistic algorithm $T$ that has a program of length at most $\ell$ and that runs in time at most $t$ on inputs of length $n$, we have $\left|\Pr[T(G(U_d))=1]-\Pr[T(U_m)=1]\right|\le\varepsilon$.

<a id="pdf-bf2ce5422088-p278-b001"></a>
<!-- pdf-source: page=278; block=1; confidence=1.00 -->
Consider the promise problem $\Pi$ whose YES instances are truth tables of functions $G:\{0,1\}^d\to\{0,1\}^m$ that are $(m,\log m,1/m)$ pseudorandom generators against bounded-nonuniformity algorithms, and whose NO instances are truth tables of functions that are not $(m,\log m,2/m)$ pseudorandom generators against bounded-nonuniformity algorithms. (Here $m$ and $d$ are parameters determined by the input instance $G.) Show that $\Pi$ is in $\mathrm{prBPP}$. (2) Using Problem 2.11, show that if $\mathrm{prBPP}=\mathrm{prP}$, then there is a mildly explicit $(m,1/m)$ pseudorandom generator against uniform algorithms with seed length $O(\log m)$.

<a id="pdf-bf2ce5422088-p278-b002"></a>
<!-- pdf-source: page=278; block=2; confidence=0.77 -->
The exercise treats constant t, with generalizations to growing t = t(ℓ) noted.

<a id="pdf-bf2ce5422088-p278-b003"></a>
<!-- pdf-source: page=278; block=3; confidence=1.00 -->
**Problem 7.11 (Composition).** For simplicity in this problem, only consider constant $t$ in this problem (although the results do have generalizations to growing $t=t(\ell)$). (1) Show that if $f:\{0,1\}^{\ell}\to\{0,1\}^{\ell}$ is a one-way permutation, then for any constant $t$, $f^{(t)}$ is a one-way permutation, where $f^{(t)}(x)\stackrel{\mathrm{def}}{=}f(f(\cdots f(x)))$ with $t$ iterations. (2) Show that the above fails for one-way functions. That is, assuming that there exists a one-way function $g$, construct a one-way function $f$ which doesn't remain one-way under composition. (Hint: for $|x|=|y|=\ell/2$, set $f(x,y)=1^{|g(y)|}g(y)$ unless $x\in\{0^\ell,1^\ell\}.)

<a id="pdf-bf2ce5422088-p279-b001"></a>
<!-- pdf-source: page=279; block=1; confidence=0.95 -->
**Theorem.** Show that if G is a cryptographic PRG with seed length d(m) = m^{Ω(1)}, then every constant iterate G^{(t)} is a cryptographic PRG. Identify where the argument fails for fully explicit PRGs against time m^c for fixed c.

<a id="pdf-bf2ce5422088-p279-b002"></a>
<!-- pdf-source: page=279; block=2; confidence=0.91 -->
**Definition.** A parameterized subspace of 𝔽₂^m is x + V, where V: 𝔽₂^d → 𝔽₂^m is linear and x ∈ 𝔽₂^m; V need not have full rank, and V also denotes 0 + V. For f: 𝔽₂^m → 𝔽₂, define f|_{x+V}(y) = f(x + V(y)), giving a function 𝔽₂^d → 𝔽₂.

<a id="pdf-bf2ce5422088-p279-b003"></a>
<!-- pdf-source: page=279; block=3; confidence=0.95 -->
**Theorem.** Let c: 𝔽₂^m → 𝔽₂ be a Hadamard codeword (a linear function), r: 𝔽₂^m → 𝔽₂ a received word, and x + V a parameterized d-dimensional subspace. If d_H(r|_{x+V}, c|_{x+V}) < 1/2, show c(x) can be computed from x, V, c|_V, and oracle access to r in time poly(m, 2^d), using 2^d − 1 queries to r.

<a id="pdf-bf2ce5422088-p279-b004"></a>
<!-- pdf-source: page=279; block=4; confidence=0.95 -->
**Theorem.** For every m and ε > 0, show that the dimension-m Hadamard code has a (1/2 − ε) local list-decoding algorithm (Dec₁, Dec₂), both running in poly(m, 1/ε) time, with Dec₁ output list size O(1/ε²). The hint selects a random parameterized subspace of dimension 2 log(1/ε) + O(1) and counts possible restrictions c|_V.

<a id="pdf-bf2ce5422088-p279-b005"></a>
<!-- pdf-source: page=279; block=5; confidence=0.99 -->
**Theorem.** Show Dec₂ can be made deterministic with running time O(m).

<a id="pdf-bf2ce5422088-p279-b006"></a>
<!-- pdf-source: page=279; block=6; confidence=1.00 -->
A hardcore predicate for a one-way function $f:\{0,1\}^{\ell}\to\{0,1\}^{\ell}$ is a $\operatorname{poly}(\ell)$-time computable function $b:\{0,1\}^{\ell}\to\{0,1\}$ such that for every constant $c$, every nonuniform algorithm $A$ running in time $\ell^c$, we have $\Pr[A(f(U_\ell))=b(U_\ell)]\le\frac12+\frac1{\ell^c}$, for all sufficiently large $\ell$.

<a id="pdf-bf2ce5422088-p280-b001"></a>
<!-- pdf-source: page=280; block=1; confidence=1.00 -->
## 7.8 Exercises

<a id="pdf-bf2ce5422088-p280-b002"></a>
<!-- pdf-source: page=280; block=2; confidence=0.98 -->
A hardcore predicate is a specific input bit that no polynomial-time predictor can guess with advantage larger than negligible: success is at most $1/2+1/\ell^c$ for every constant $c$, eventually.

<a id="pdf-bf2ce5422088-p280-b003"></a>
<!-- pdf-source: page=280; block=3; confidence=0.99 -->
Let $\operatorname{Enc}:\{0,1\}^{\ell}\to\{0,1\}^{\widehat L}$ be a code such that given $x\in\{0,1\}^{\ell}$ and $y\in[\widehat L]$, $\operatorname{Enc}(x)_y$ can be computed in time $\operatorname{poly}(\ell)$. Suppose that for every constant $c$ and all sufficiently large $\ell$, $\operatorname{Enc}$ has a $(1/2-1/\ell^c)$ local list-decoding algorithm $(\operatorname{Dec}_1,\operatorname{Dec}_2)$ in which both $\operatorname{Dec}_1$ and $\operatorname{Dec}_2$ run in time $\operatorname{poly}(\ell)$. Prove that if $f:\{0,1\}^{\ell}\to\{0,1\}^{\ell}$ is a one-way function, then $b(x,y)=\operatorname{Enc}(x)_y$ is a hardcore predicate for the one-way function $f'(x,y)=(f(x),y)$.

<a id="pdf-bf2ce5422088-p280-b004"></a>
<!-- pdf-source: page=280; block=4; confidence=0.99 -->
Show that if $b$ is hardcore for a one-way permutation $f$, then for every polynomially bounded $m$, $G(x)=(b(x),b(f(x)),\ldots,b(f^{m-1}(x)))$ is a cryptographic pseudorandom generator. Hint: prove previous-bit unpredictability.

<a id="pdf-bf2ce5422088-p280-b005"></a>
<!-- pdf-source: page=280; block=5; confidence=1.00 -->
Using Problem 7.12, deduce that if $f:\{0,1\}^{\ell}\to\{0,1\}^{\ell}$ is a one-way permutation, then for every $m=\operatorname{poly}(\ell)$, the following is a cryptographic pseudorandom generator: $G_m(x,r)=(\langle x,r\rangle,\langle f(x),r\rangle,\langle f(f(x)),r\rangle,\ldots,\langle f^{(m-1)}(x),r\rangle)$.

<a id="pdf-bf2ce5422088-p280-b006"></a>
<!-- pdf-source: page=280; block=6; confidence=0.99 -->
**Definition.** A random variable $X$ has $(t,\varepsilon)$-pseudoentropy at least $k$ if it is $(t,\varepsilon)$-indistinguishable from some random variable of min-entropy at least $k$.

<a id="pdf-bf2ce5422088-p281-b001"></a>
<!-- pdf-source: page=281; block=1; confidence=0.99 -->
If $X$ has $(t,\varepsilon)$-pseudoentropy at least $k$ and $\operatorname{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a $(k,\varepsilon')$-extractor computable in time $t'$, show that $\operatorname{Ext}(X,U_d)$ is $(t-t',\varepsilon+\varepsilon')$-indistinguishable from $U_m$.

<a id="pdf-bf2ce5422088-p281-b002"></a>
<!-- pdf-source: page=281; block=2; confidence=1.00 -->
Let $f:\{0,1\}^{\ell}\to\{0,1\}^{\ell'}$ be a one-to-one one-way function (not necessarily length-preserving) and $b:\{0,1\}^{\ell}\to\{0,1\}$ a hardcore predicate for $f$ (see Problem 7.13). Show that for every constant $c$ and all sufficiently large $\ell$, the random variable $f(U_\ell)b(U_\ell)$ has $(\ell^c,1/\ell^c)$ pseudoentropy at least $\ell+1$.

<a id="pdf-bf2ce5422088-p281-b003"></a>
<!-- pdf-source: page=281; block=3; confidence=0.99 -->
(*) Construct a cryptographic pseudorandom generator from any one-to-one one-way function; any seed length $\ell(m)<m$ is acceptable.

<a id="pdf-bf2ce5422088-p281-b004"></a>
<!-- pdf-source: page=281; block=4; confidence=1.00 -->
## 7.9 Chapter Notes and References

<a id="pdf-bf2ce5422088-p281-b005"></a>
<!-- pdf-source: page=281; block=5; confidence=0.98 -->
The notes cite surveys, classical generators and their cryptographic failures, and practical standards. They recount the development from one-way functions through next-bit unpredictability and computational indistinguishability, including constructions from one-way permutations and general one-way functions.

<a id="pdf-bf2ce5422088-p282-b001"></a>
<!-- pdf-source: page=282; block=1; confidence=0.97 -->
The chapter notes attribute the arbitrary one-way-function PRG construction to Håstad, Impagliazzo, Levin, and Luby, and mention later more efficient constructions. They also summarize pseudorandom functions and applications, plus derandomization consequences: cryptographic PRGs imply $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$, while stronger assumptions yield a stronger containment; Nisan–Wigderson generators arise from average-case hardness of $E$.

<a id="pdf-bf2ce5422088-p282-b002"></a>
<!-- pdf-source: page=282; block=2; confidence=0.98 -->
The parity-based Nisan–Wigderson construction fooling constant-depth circuits is attributed to Nisan; the cited average-case hardness of parity against such circuits is attributed to Boppana and Håstad.

<a id="pdf-bf2ce5422088-p283-b001"></a>
<!-- pdf-source: page=283; block=1; confidence=0.99 -->
Ajtai and Wigderson gave a pseudorandom generator against constant-depth circuits with seed length $\ell(m)=m^\epsilon$, compared with the polylogarithmic seed length of Nisan’s generator. Braverman proved that any polylog$(m)$-wise independent distribution fools $\mathrm{AC}^0$, resolving a conjecture of Linial and Nisan. The notion of strong pseudorandom generators (also called seed-extending pseudorandom generators) and average-case derandomization of $\mathrm{AC}^0$ are also cited. Superpolynomial circuit lower bounds for $\mathrm{AC}^0[2]$ are cited, as are Viola’s generators with superpolynomial stretch for $\mathrm{AC}^0[2]$ circuits restricted to a logarithmic number of parity gates.

<a id="pdf-bf2ce5422088-p283-b002"></a>
<!-- pdf-source: page=283; block=2; confidence=0.98 -->
The discussion traces locally decodable codes to Hadamard-code local list decoding implicit in Goldreich–Levin, Reed–Muller decoding used in instance-hiding, and self-correctors for group homomorphisms, yielding a local corrector for the Hadamard code. Self-correction upgrades a program correct on most inputs to one correct everywhere.

<a id="pdf-bf2ce5422088-p283-b003"></a>
<!-- pdf-source: page=283; block=3; confidence=0.99 -->
A self-tester checks whether a program is mostly correct; combined with self-correction it gives a program checker. Self-testing work motivated locally testable codes and property testing, with connections to probabilistically checkable proofs.

<a id="pdf-bf2ce5422088-p284-b001"></a>
<!-- pdf-source: page=284; block=1; confidence=0.98 -->
Multivariate-polynomial self-correction can be viewed as Reed–Muller local correction and applied to hard functions via multilinear extension. These methods contributed to pseudorandom generators from worst-case EXP (or E) hardness and subexponential or quasipolynomial BPP simulations under suitable assumptions. Random self-reducibility links worst-case and average-case complexity; the corresponding question for NP remains an active research area.

<a id="pdf-bf2ce5422088-p284-b002"></a>
<!-- pdf-source: page=284; block=2; confidence=0.97 -->
Polynomial self-correctors handle either a constant error fraction or error approaching $1/2$. These results were recast as efficient local decoding and testing. Katz–Trevisan established that rate, distance, and query complexity cannot all remain constant with message length; the notes also cite subexponential-blocklength 3-query codes, private information retrieval, smooth codes, and their connections.

<a id="pdf-bf2ce5422088-p285-b001"></a>
<!-- pdf-source: page=285; block=1; confidence=0.98 -->
A construction is noted for locally decodable codes with sublinear-time decoding and rate above $1/2$. The Direct Product Theorem and XOR Lemma are attributed to Yao; Reed–Muller local list decoding and general locally list-decodable codes are also surveyed, including results stated as Theorems 7.56 and 7.60–7.62.

<a id="pdf-bf2ce5422088-p285-b002"></a>
<!-- pdf-source: page=285; block=2; confidence=0.99 -->
Impagliazzo and Wigderson showed that $\mathrm{BPP}=\mathrm{P}$ if $\mathrm{E}$ has a function of nonuniform worst-case hardness $s(\ell)=2^{\Omega(\ell)}$ (Corollary 7.64, Part 1). They used derandomized versions of the XOR Lemma to obtain sufficient average-case hardness for the Nisan–Wigderson pseudorandom generator. Shaltiel and Umans gave an optimal construction of pseudorandom generators from worst-case hard functions, with seed length $d(m)=O(s^{-1}(\operatorname{poly}(m)))$.

<a id="pdf-bf2ce5422088-p285-b003"></a>
<!-- pdf-source: page=285; block=3; confidence=0.99 -->
Arvind and Köbler gave the first evidence that $\mathrm{AM}=\mathrm{NP}$, showing that one can use the Nisan–Wigderson generator with a function that is $(2^{\Omega(\ell)},1/2-1/2^{\Omega(\ell)})$-hard for nondeterministic circuits. Klivans and van Melkebeek observed that the Impagliazzo–Wigderson pseudorandom generator construction is “black box” and used this to show that $\mathrm{AM}$ can be derandomized using functions that are worst-case hard for circuits with an $\mathrm{NP}$ oracle. Subsequent work showed that worst-case hardness against a nonuniform analogue of $\mathrm{NP}\cap\mathrm{coNP}$ suffices.

<a id="pdf-bf2ce5422088-p285-b004"></a>
<!-- pdf-source: page=285; block=4; confidence=0.99 -->
Black-box pseudorandom generator constructions yield randomness extractors; this connection produced the extractor construction cited as Theorem 7.73.

<a id="pdf-bf2ce5422088-p286-b001"></a>
<!-- pdf-source: page=286; block=1; confidence=0.99 -->
### 7.9 Chapter Notes and References

<a id="pdf-bf2ce5422088-p286-b002"></a>
<!-- pdf-source: page=286; block=2; confidence=0.98 -->
The notes attribute results and problems on hardness amplification, PRGs, approximate counting, hitting-set generators, derandomization, one-way functions, Kolmogorov complexity, circuit-size bounds, and indistinguishability to the cited works.

<a id="pdf-bf2ce5422088-p287-b001"></a>
<!-- pdf-source: page=287; block=1; confidence=0.99 -->
# 8 Conclusions

<a id="pdf-bf2ce5422088-p287-b002"></a>
<!-- pdf-source: page=287; block=2; confidence=0.99 -->
## 8.1 A Unified Theory of Pseudorandomness

<a id="pdf-bf2ce5422088-p287-b003"></a>
<!-- pdf-source: page=287; block=3; confidence=0.98 -->
The survey relates list-decodable codes, averaging samplers, expander graphs, randomness extractors, black-box PRG constructions, and hardness amplifiers; examples include extractor-based samplers, Parvaresh–Vardy constructions of bipartite expanders and lossless condensers, and Nisan–Wigderson-based extractors.

<a id="pdf-bf2ce5422088-p287-b004"></a>
<!-- pdf-source: page=287; block=4; confidence=0.90 -->
The objects are represented as functions $\Gamma:[N]\times[D]\to[M]$. Their properties are expressed by bounds on $\mathrm{LIST}_{\Gamma}(T,\alpha)=\{x:\Pr_y[\Gamma(x,y)\in T]>\alpha\}$ for $T\subseteq[M]$. The source says the convention changes when $\alpha=1$, but the continuation is on the next page and is not recoverable here.

<a id="pdf-bf2ce5422088-p288-b001"></a>
<!-- pdf-source: page=288; block=1; confidence=0.87 -->
**Table 8.1. Capturing Pseudorandom Objects.** The table compares pseudorandom objects through bounds on $|\mathrm{LIST}_{\Gamma}(T,\alpha)|$ for $T\subseteq[M]$, where $\Gamma:[N]\times[D]\to[M]$. The parameter $\gamma$ denotes an arbitrary small positive constant. As usual, $N=2^n$, $M=2^m$, $D=2^d$, and $K=2^k$.

<a id="pdf-bf2ce5422088-p289-b001"></a>
<!-- pdf-source: page=289; block=1; confidence=0.98 -->
The framework captures several objects but their parameter ranges, tested sets, and construction goals differ; techniques can still transfer between them.

<a id="pdf-bf2ce5422088-p289-b002"></a>
<!-- pdf-source: page=289; block=2; confidence=0.99 -->
**Definition 8.1 (tails of binomial distributions).** For $t\in\mathbb N$ and $\mu,\alpha\in(0,1)$, define
\[
\operatorname{Bin}(t,\mu,\alpha)=\Pr\left[\frac1t\sum_{i=1}^t X_i>\alpha\right],
\]
where the $X_i$ are iid $\{0,1\}$-valued random variables such that $\Pr[X_i=1]=\mu$. Also define
\[
\operatorname{Bin}(t,\mu,1)=\Pr\left[\frac1t\sum_{i=1}^t X_i=1\right]=\mu^t.
\]

<a id="pdf-bf2ce5422088-p290-b001"></a>
<!-- pdf-source: page=290; block=1; confidence=0.92 -->
**Definition 8.1 (continued).** For the same iid Bernoulli variables, \(\operatorname{Bin}(t,\mu,1)=\Pr[\frac1t\sum_{i=1}^tX_i=1]=\mu^t\).

<a id="pdf-bf2ce5422088-p290-b002"></a>
<!-- pdf-source: page=290; block=2; confidence=0.99 -->
**Theorem 8.2 (nonconstructive unified pseudorandom object).** For every $N,M,D\in\mathbb N$, there exists a function $\Gamma:[N]\times[D]\to[M]$ such that for every $T\subseteq[M]$ and every $\alpha\in(0,1]$,
\[
|\mathrm{LIST}_{\Gamma}(T,\alpha)|\le \min\left\{K\in\mathbb N: \binom{N}{K}\binom{M}{|T|}\operatorname{Bin}(D,\mu(T),\alpha)^K\le \frac{1}{4K^2|T|^2}\right\}.
\]

<a id="pdf-bf2ce5422088-p290-b003"></a>
<!-- pdf-source: page=290; block=3; confidence=0.97 -->
The text leaves the theorem’s proof as an exercise and illustrates parameter choices that recover known nonconstructive bounds.

<a id="pdf-bf2ce5422088-p290-b004"></a>
<!-- pdf-source: page=290; block=4; confidence=0.78 -->
Set \(M=N\), \(\alpha=1\), and \(K=|T|/(D-2)\), ignoring rounding. Using \(\binom nk\le (en/k)^k\) and \(\operatorname{Bin}(D,\mu,1)=\mu^D\), the theorem’s condition follows when \(\mu\) is sufficiently small. Proposition 5.33 then gives a \((\gamma N,D-2)\) vertex expander for sufficiently small \(\gamma\).

<a id="pdf-bf2ce5422088-p291-b001"></a>
<!-- pdf-source: page=291; block=1; confidence=0.83 -->
For constants \(\gamma,A,D>0\) and sufficiently large \(N=M\), the construction gives a \((\gamma N,A)\) expander if
\[
D>\frac{H(\gamma)+H(\gamma A)}{\gamma\log(1/\gamma A)},
\]
where \(H(x)=x\log(1/x)+(1-x)\log(1/(1-x))\). The argument uses \(\binom{N}{\beta N}=2^{(H(\beta)+o(1))N}\). A footnote compares this threshold with a stronger one for a different random-graph model.

<a id="pdf-bf2ce5422088-p291-b002"></a>
<!-- pdf-source: page=291; block=2; confidence=0.86 -->
For the nonconstructive extractor and averaging-sampler bounds (Theorem 6.14), take \(\alpha=\mu(T)+\varepsilon\) and apply Chernoff: \(\operatorname{Bin}(D,\mu(T),\mu(T)+\varepsilon)\le \exp(-\Omega(D\varepsilon^2))\). The condition of Theorem 8.2 holds when \(D\ge(c/\varepsilon^2)\log(N/K)\) and \(M\le \varepsilon^2KD/c\), for a sufficiently large constant \(c\).

<a id="pdf-bf2ce5422088-p291-b003"></a>
<!-- pdf-source: page=291; block=3; confidence=0.97 -->
Strong objects of the form \(\Gamma(x,y)=(y,\Gamma'(x,y))\) require tail bounds for sums of independent Bernoulli variables with potentially different distributions.

<a id="pdf-bf2ce5422088-p291-b004"></a>
<!-- pdf-source: page=291; block=4; confidence=0.99 -->
**Definition 8.3 (tails of Poisson binomial distributions).** For $t,N,\mu,\alpha\in(0,1)$, define
\[
\operatorname{PBin}(t,\mu,\alpha,\eta)=\sup_{(Y_1,\ldots,Y_t)}\Pr\left[\frac1t\sum_{i=1}^tY_i>\alpha\right],
\]
and
\[
\operatorname{PBin}(t,\mu,1,\eta)=\sup_{(Y_1,\ldots,Y_t)}\Pr\left[\frac1t\sum_{i=1}^tY_i=1\right]=\operatorname{Bin}(t,\mu,1),
\]
where the suprema are over all sequences of independent Bernoulli random variables $Y_1,\ldots,Y_t$ such that $\frac1t\sum_{i=1}^t\mathbb E[Y_i]\le\mu$, and additionally $\mathbb E[Y_i]$ is an integer multiple of $\eta$ for every $i$.

<a id="pdf-bf2ce5422088-p292-b001"></a>
<!-- pdf-source: page=292; block=1; confidence=0.99 -->
**Theorem 8.4 (nonconstructive unified pseudorandom object).** For every $N,q,D\in\mathbb N$, there exists a function $\Gamma':[N]\times[D]\to[q]$ such that, defining $\Gamma(x,y)=(y,\Gamma'(x,y))$, for every $T\subseteq[D]\times[q]$ and every $\alpha\in(0,1]$,
\[
|\mathrm{LIST}_{\Gamma}(T,\alpha)|\le \min\left\{K\in\mathbb N: \binom{N}{K}\binom{Dq}{|T|}\operatorname{PBin}(D,\mu(T),\alpha,1/q)^K\le \frac{1}{4K^2|T|^2}\right\}.
\]

<a id="pdf-bf2ce5422088-p292-b002"></a>
<!-- pdf-source: page=292; block=2; confidence=0.76 -->
Strong vertex expanders, hitting samplers, and lossless condensers inherit the corresponding non-strong bounds from \(P_{\rm Bin}(n,\mu,1,\eta)\le \operatorname{Bin}(n,\mu,1)\). For independent Bernoulli variables \(Y_i\) with means \(\mu_i\), the probability all equal 1 is \(\prod_i\mu_i\le (\frac1t\sum_i\mu_i)^t\le\mu^t\), using AM–GM. Strong extractors and averaging samplers use the Chernoff bound (Theorem 2.21), which also holds for nonidentical variables: \(P_{\rm Bin}(D,\mu(T),\mu(T)+\varepsilon,\eta)\le \exp(-\Omega(D\varepsilon^2))\) for \(\eta>0\). List-decodable codes (Theorem 5.8) arise by taking \(T\) to be the graph of a received word; the associated tail probability is evaluated on the following page.

<a id="pdf-bf2ce5422088-p293-b001"></a>
<!-- pdf-source: page=293; block=1; confidence=0.91 -->
For $T'=\{(i,j):i\in[D],\ j\le m_i\}$, the probability that $G(R)\cap T'=S$ is at most $(1/q)^{|S|}(1-1/q)^{D-|S|}$; it is zero unless the pairs in $S$ have distinct first coordinates. Thus
\[
\Pr\left[\sum_iY_i>(1-\delta)D\right]\le \sum_{s>(1-\delta)D}\binom Ds(1/q)^s(1-1/q)^{D-s}\le \frac1{q^D}\sum_{s>(1-\delta)D}\binom Ds(q-1)^s=\frac{q^{H_q(\delta,D)D}}{q^D}.
\]

<a id="pdf-bf2ce5422088-p293-b002"></a>
<!-- pdf-source: page=293; block=2; confidence=0.98 -->
Using this bound and Proposition 5.29, Theorem 8.4 gives a $(\delta,K)$ list-decodable code $\operatorname{Enc}:[N]\to[q]^D$ provided that
\[
\binom NK\binom{Dq}{D}\left(\frac{q^{H_q(\delta,D)D}}{q^D}\right)^K\le\frac1{4K^2D^2}.
\]
Using $\binom NK\le N^K$ and $\binom{Dq}{D}\le(eq)^D$, the text concludes that the rate $\rho=\log N/(D\log q)$ is smaller than $H_q(\delta,D)-O(1/K)-O(\log(KD)/(KD\log q)$.

<a id="pdf-bf2ce5422088-p293-b003"></a>
<!-- pdf-source: page=293; block=3; confidence=0.97 -->
**Open Problem 8.5.** Can one explicitly construct functions \(\Gamma\) that nearly attain the bounds of Theorems 8.2 and 8.4, with efficient local list-decoding algorithms?

<a id="pdf-bf2ce5422088-p293-b004"></a>
<!-- pdf-source: page=293; block=4; confidence=0.99 -->
## 8.2 Other Topics in Pseudorandomness

<a id="pdf-bf2ce5422088-p293-b005"></a>
<!-- pdf-source: page=293; block=5; confidence=0.98 -->
The section surveys additional pseudorandomness topics; cryptographic pseudorandomness was covered in Sections 7.2 and 7.9.

<a id="pdf-bf2ce5422088-p294-b001"></a>
<!-- pdf-source: page=294; block=1; confidence=0.99 -->
### 8.2.1 Pseudorandomness for Space-Bounded Computation

<a id="pdf-bf2ce5422088-p294-b002"></a>
<!-- pdf-source: page=294; block=2; confidence=0.96 -->
Nontrivial derandomizations are known for \(\mathrm{RL}\) and \(\mathrm{BPL}\), unlike \(\mathrm{BPP}\) and \(\mathrm{RP}\). They use generators \(G:\{0,1\}^d\to\{0,1\}^m\) that fool randomized \(O(\log m)\)-space distinguishers. Correctness on every input requires fooling nonuniform space-bounded algorithms. Since such algorithms consume random bits sequentially, it suffices to consider oblivious read-once branching programs.

<a id="pdf-bf2ce5422088-p294-b003"></a>
<!-- pdf-source: page=294; block=3; confidence=0.88 -->
**Definition.** An oblivious read-once branching program has states \(s_i\in[w]\) after \(i\) input bits and updates \(s_i\mapsto s_{i+1}\) as a function of the current state and next input bit. Its width is \(w\), corresponding to \(\log w\) space. A generator \(G:\{0,1\}^{d(m)}\to\{0,1\}^m\), computable in space \(O(d(m))\), that fools width-\(m\) programs implies \(\mathrm{BPL}\subseteq\mathrm{DSPACE}(O(d(\operatorname{poly}(m))))\).

<a id="pdf-bf2ce5422088-p294-b004"></a>
<!-- pdf-source: page=294; block=4; confidence=0.99 -->
The fact that pseudorandom generators imply lower bounds (Problem 7.1) applies to this context too, but fortunately we do know exponential width lower bounds for oblivious, read-once branching programs (e.g., computing the inner-product modulo 2 of two \(\ell\)-bit strings requires width \(2^{\Omega(\ell)}\)). On the other hand, we cannot simply plug such lower bounds into the Nisan–Wigderson generator construction (Theorem 7.24), because the reductions used do not preserve the read-once property (and we do not know superpolynomial lower bounds for branching programs that can read each input bit many times).

<a id="pdf-bf2ce5422088-p294-b005"></a>
<!-- pdf-source: page=294; block=5; confidence=0.96 -->
A sequence of works beginning with Ajtai, Komlós, and Szemerédi established unconditional pseudorandom generators for space-bounded computation; the discussion continues beyond the supplied text.

<a id="pdf-bf2ce5422088-p295-b001"></a>
<!-- pdf-source: page=295; block=1; confidence=0.98 -->
Nisan’s generator uses an $O(\log^2 m)$-bit seed to fool width-$m$ oblivious read-once branching programs; its refinements yield stronger space bounds for $\mathrm{RL}$. Nisan–Zuckerman give a generator with seed length $O(\log m)$ and stretch $\log^k m$.

<a id="pdf-bf2ce5422088-p295-b002"></a>
<!-- pdf-source: page=295; block=2; confidence=0.98 -->
Generators or hitting sets with seed length about $\log m$ and output length $m$ are known for combinatorial rectangles, width-2 and width-3 programs, and constant-width regular or permutation branching programs.

<a id="pdf-bf2ce5422088-p295-b003"></a>
<!-- pdf-source: page=295; block=3; confidence=0.99 -->
**Open Problem 8.6.** Does there exist an explicit generator $G:\{0,1\}^{o(\log^2 m)}\to\{0,1\}^m$ whose output distribution fools oblivious read-once branching programs of width $4$?

<a id="pdf-bf2ce5422088-p295-b004"></a>
<!-- pdf-source: page=295; block=4; confidence=1.00 -->
## 8.2.2 Derandomization vs. Lower Bounds

<a id="pdf-bf2ce5422088-p295-b005"></a>
<!-- pdf-source: page=295; block=5; confidence=0.99 -->
The section begins by seeking pseudorandom generators based only on uniform hardness assumptions, rather than the nonuniform circuit lower bounds used in Theorem 7.63.

<a id="pdf-bf2ce5422088-p296-b001"></a>
<!-- pdf-source: page=296; block=1; confidence=0.99 -->
The Karp–Lipton Theorems in complexity theory show that certain strong uniform lower bounds imply nonuniform lower bounds. For example, if an EXP-complete problem cannot be solved by a uniform algorithm in the second level of the polynomial-time hierarchy, then it also cannot be solved by polynomial-sized circuits. Subsequent strengthenings of the Karp–Lipton Theorem show that if \(\mathrm{EXP} \ne \mathrm{MA}\), then \(\mathrm{EXP} \not\subseteq \mathrm{P/poly}\); consequently one gets pseudorandom generators with arbitrary polynomial stretch (secure for infinitely many input lengths) under the assumption \(\mathrm{EXP} \ne \mathrm{MA}\). Assuming the Karp–Lipton Theorem cannot be further improved (e.g., to show \(\mathrm{EXP} \not\subseteq \mathrm{P/poly} \iff \mathrm{EXP} \ne \mathrm{BPP}\)), from a uniform assumption such as \(\mathrm{EXP} \ne \mathrm{BPP}\), we can only hope to construct pseudorandom generators that are secure against uniform distinguishers.

<a id="pdf-bf2ce5422088-p296-b002"></a>
<!-- pdf-source: page=296; block=2; confidence=0.99 -->
Cryptographic PRGs secure against uniform distinguishers exist exactly when one-way functions resist inversion by uniform algorithms (Theorem 7.11 analogy).

<a id="pdf-bf2ce5422088-p296-b003"></a>
<!-- pdf-source: page=296; block=3; confidence=0.98 -->
For noncryptographic mildly explicit generators, black-box reductions (Definition 7.65) use nonuniform advice, obstructing uniform-hardness constructions. The analogous obstacle does not apply to cryptographic generators because their reductions may query the efficiently computable one-way function as well as the distinguisher.

<a id="pdf-bf2ce5422088-p297-b001"></a>
<!-- pdf-source: page=297; block=1; confidence=0.98 -->
Non-black-box methods can exploit descriptions of the hard function and distinguisher. Impagliazzo and Wigderson show that $\mathrm{EXP}\ne\mathrm{BPP}$ gives mildly explicit polynomial-stretch PRGs secure against uniform probabilistic distinguishers for infinitely many input lengths; consequently, BPP has subexponential-time average-case derandomizations (Problem 7.9). This is the uniform counterpart of Corollary 7.64(3); counterparts of its high-end cases remain open.

<a id="pdf-bf2ce5422088-p297-b002"></a>
<!-- pdf-source: page=297; block=2; confidence=0.99 -->
**Open Problem 8.7.** Does \(\mathrm{EXP} \not\subseteq \mathrm{BPSUBEXP}\) imply mildly explicit generators \(G : \{0,1\}^{\mathrm{polylog}(m)} \to \{0,1\}^m\) whose input is pseudorandom to every uniform probabilistic algorithm running in time \(m\) (for infinitely many \(m\))?

<a id="pdf-bf2ce5422088-p297-b003"></a>
<!-- pdf-source: page=297; block=3; confidence=0.98 -->
The analogous generator result is known with PSPACE replacing EXP. For derandomizing AM, both high-end and low-end uniform results are known; these use hard functions in E, whereas the cited nonuniform results need hardness in $\mathrm{NE}\cap\mathrm{coNE}$ (Theorem 7.68).

<a id="pdf-bf2ce5422088-p297-b004"></a>
<!-- pdf-source: page=297; block=4; confidence=1.00 -->
## Derandomization Implies Circuit Lower Bounds

<a id="pdf-bf2ce5422088-p297-b005"></a>
<!-- pdf-source: page=297; block=5; confidence=0.99 -->
A result of this type was first given implicitly by Buhrman, Fortnow, and Thierauf [86] and then explicitly and in stronger form by Impagliazzo, Kabanets, and Wigderson [212].

<a id="pdf-bf2ce5422088-p298-b001"></a>
<!-- pdf-source: page=298; block=1; confidence=0.99 -->
Specifically, these results show that if \(\mathrm{MA}\) can be derandomized (e.g., \(\mathrm{MA} = \mathrm{NP}\) or even \(\mathrm{MA} \subseteq \mathrm{NSUBEXP}\)), then \(\mathrm{NEXP} \not\subseteq \mathrm{P/poly}\). Derandomization of \(\mathrm{prBPP}\) implies derandomization of \(\mathrm{MA}\), so this also implies that if \(\mathrm{prBPP} = \mathrm{prP}\) or even \(\mathrm{prBPP} \subseteq \mathrm{prSUBEXP}\), then \(\mathrm{NEXP} \not\subseteq \mathrm{P/poly}\).

<a id="pdf-bf2ce5422088-p298-b002"></a>
<!-- pdf-source: page=298; block=2; confidence=0.99 -->
**Open Problem 8.8.** Does \(\mathrm{prBPP}=\mathrm{prP}\) imply \(\mathrm{E}\not\subseteq\mathrm{P/poly}\) (equivalently, \(\mathrm{EXP}\not\subseteq\mathrm{P/poly}\), by Problem 7.2)?

<a id="pdf-bf2ce5422088-p298-b003"></a>
<!-- pdf-source: page=298; block=3; confidence=0.99 -->
**Open Problem 8.9.** Does \(\mathrm{prBPP} = \mathrm{prP}\) imply that \(\mathrm{NEXP}\) has a problem requiring nonuniform Boolean circuits of size \(2^{\ell^{\Omega(1)}}\) on inputs of length \(\ell\)?

<a id="pdf-bf2ce5422088-p298-b004"></a>
<!-- pdf-source: page=298; block=4; confidence=0.65 -->
A deterministic polynomial-time algorithm for the prBPP-complete \([+\varepsilon]\)-Approx Circuit Average problem would imply superpolynomial circuit lower bounds for NEXP. The precise symbol in the problem name is corrupted in the extraction.

<a id="pdf-bf2ce5422088-p298-b005"></a>
<!-- pdf-source: page=298; block=5; confidence=0.99 -->
A deterministic polynomial-time algorithm for Polynomial Identity Testing would imply either \(\mathrm{NEXP}\not\subseteq\mathrm{P/poly}\) or that the Permanent has no polynomial-size arithmetic circuits. The sentence continues on page 299.

<a id="pdf-bf2ce5422088-p299-b001"></a>
<!-- pdf-source: page=299; block=1; confidence=0.99 -->
Polynomial Identity Testing belongs to co-RP by Theorem 2.12, but is not known complete for a randomized complexity class.

<a id="pdf-bf2ce5422088-p299-b002"></a>
<!-- pdf-source: page=299; block=2; confidence=0.99 -->
**Open Problem 8.10.** Find combinatorial or algebraic complete problems for randomized complexity classes such as prBPP, prRP, prAM, BPP, RP, or ZPP.

<a id="pdf-bf2ce5422088-p299-b003"></a>
<!-- pdf-source: page=299; block=3; confidence=0.96 -->
Derandomizing prAM can imply circuit lower bounds stronger than those from the cited prBPP results, including exponential-size bounds or lower bounds for nondeterministic circuits. Such results suggest that when derandomization is possible, pseudorandom generators may provide a canonical implementation, since circuit lower bounds imply generators by Theorem 7.63. Goldreich gives direct equivalences between forms of prBPP derandomization and pseudorandom generators.

<a id="pdf-bf2ce5422088-p299-b004"></a>
<!-- pdf-source: page=299; block=4; confidence=0.98 -->
Derandomization has contributed to lower bounds including \(\mathrm{MAEXP}\not\subseteq\mathrm{P/poly}\) and \(\mathrm{NEXP}\not\subseteq\mathrm{ACC}\). Here ACC extends AC\(^0\) with unbounded-fan-in gates testing whether the input sum is zero modulo a constant \(m\). The Kabanets–Impagliazzo result also motivated work on derandomizing Polynomial Identity Testing for low-depth arithmetic circuits; the discussion continues on page 300.

<a id="pdf-bf2ce5422088-p300-b001"></a>
<!-- pdf-source: page=300; block=1; confidence=0.99 -->
## 8.2.3 Hardness Amplification

<a id="pdf-bf2ce5422088-p300-b002"></a>
<!-- pdf-source: page=300; block=2; confidence=0.99 -->
Hardness amplification transforms a problem that is mildly hard on average into one that is much harder on average. Yao proposed a direct-product construction and an XOR lemma as tools for deriving pseudorandom generators from weak one-way permutations.

<a id="pdf-bf2ce5422088-p300-b003"></a>
<!-- pdf-source: page=300; block=3; confidence=0.99 -->
Specifically, he suggested the “Direct Product” construction \(f'(x_1,\ldots,x_k) = (f(x_1),\ldots,f(x_k))\) to convert a weak one-way function \(f\) (one that is mildly hard to invert) into a standard “strong” one-way function \(f'\) (satisfying Definition 7.10), and an “XOR Lemma” showing that if a Boolean function \(f\) is mildly hard to compute, then \(f'(x_1,\ldots,x_k) = f(x_1) \oplus f(x_2) \oplus \cdots \oplus f(x_k)\) is very hard on average to compute.

<a id="pdf-bf2ce5422088-p300-b004"></a>
<!-- pdf-source: page=300; block=4; confidence=0.99 -->
### Quantitative Bounds

<a id="pdf-bf2ce5422088-p300-b005"></a>
<!-- pdf-source: page=300; block=5; confidence=0.98 -->
For a function \(f\) that is \(\delta\)-average-case-hard, the direct product is expected to be about \(1-(1-\delta)^k\)-average-case-hard. If \(f\) is \((1-\delta)/2\)-average-case-hard, the XOR product is expected to be about \((1-\delta^k)/2\)-average-case-hard. Levin proved a tight XOR-lemma bound, with techniques also extending to direct products.

<a id="pdf-bf2ce5422088-p300-b006"></a>
<!-- pdf-source: page=300; block=6; confidence=0.99 -->
### Derandomization

<a id="pdf-bf2ce5422088-p300-b007"></a>
<!-- pdf-source: page=300; block=7; confidence=0.97 -->
Goldreich, Impagliazzo, Levin, Venkatesan, and Zuckerman give derandomized amplification from weak one-way permutations and weak regular one-way functions to strong ones. The inputs \(x_i\) are generated pseudorandomly from a short seed rather than independently; the sentence is truncated at the page boundary.

<a id="pdf-bf2ce5422088-p301-b001"></a>
<!-- pdf-source: page=301; block=1; confidence=0.97 -->
Impagliazzo and Wigderson gave derandomized XOR and Direct Product Lemmas for hard Boolean functions, yielding a proof that exponential circuit lower bounds for E imply P = BPP. A later approach instead uses locally list-decodable codes for worst-case-to-average-case amplification. Hardness amplification from mild average-case hardness can run in polynomial time with oracle access to f; black-box worst-case-to-average-case amplification (Definition 7.74) cannot be implemented in the polynomial-time hierarchy, according to Viola.

<a id="pdf-bf2ce5422088-p301-b002"></a>
<!-- pdf-source: page=301; block=2; confidence=0.99 -->
## Hardness Amplification in NP

<a id="pdf-bf2ce5422088-p301-b003"></a>
<!-- pdf-source: page=301; block=3; confidence=0.99 -->
He characterizes the amplification properties of \(C\) in terms of its “noise stability,” thereby connecting the study of hardness amplification with the analysis of Boolean functions. He uses this connection to find monotone functions \(C\) with nearly optimal amplification properties, namely ones that will ensure that the function \(f'\) is roughly \((1/2 - O(1/\sqrt{k}))\)-hard if it is obtained by combining \(k\) evaluations of \(f\). Contrast this bound with the XOR Lemma, where \(C\) is the parity function and ensures that \(f'\) is \((1/2 - 1/2^{\Omega(k)})\)-hard.

<a id="pdf-bf2ce5422088-p302-b001"></a>
<!-- pdf-source: page=302; block=1; confidence=0.99 -->
## 8.2 Other Topics in Pseudorandomness

<a id="pdf-bf2ce5422088-p302-b002"></a>
<!-- pdf-source: page=302; block=2; confidence=0.99 -->
As a result, assuming that \(f\) is mildly hard for nonuniform algorithms running in time \(2^{\Omega(n)}\) (the “high end”), they obtain \(f' \in \mathrm{NP}\) that is \((1/2 - 1/2^{(n')^{1/2}})\)-hard, where \(n'\) is the input length of \(f'\). A quantitative improvement was given by [273, 179], replacing \(2^{(n')^{1/2}}\) with \(2^{n'/\mathrm{polylog}(n')}\), but it remains open to achieve the optimal bound of \(2^{\Omega(n')}\).

<a id="pdf-bf2ce5422088-p302-b003"></a>
<!-- pdf-source: page=302; block=3; confidence=0.99 -->
## Uniform Reductions

<a id="pdf-bf2ce5422088-p302-b004"></a>
<!-- pdf-source: page=302; block=4; confidence=0.94 -->
Uniform amplification is studied in analogy with derandomization from uniform assumptions. In noncryptographic settings, black-box amplification corresponds to decoding codes from large distances (for binary codes, around 1/2 − ε), where unique decoding fails and list decoding plus advice is needed to select the right candidate. For mild average-case hardness, decoding need only recover a string close to the original message, but natural parameter regimes still require list decoding. Since candidate lists can be small, uniform algorithms may output possible decodings, as in locally list-decodable codes (Definition 7.54).

<a id="pdf-bf2ce5422088-p303-b001"></a>
<!-- pdf-source: page=303; block=1; confidence=0.93 -->
For functions in classes such as NP or E, non-black-box checkability of the initial function can select a correct decoding from a list, enabling fully uniform amplification. Uniform local list-decoding for Reed–Muller codes supported worst-case-to-average-case results for E and other classes. Later work gave uniform mild-hardness amplification and nearly optimal uniform Direct Product Theorems and XOR Lemmas.

<a id="pdf-bf2ce5422088-p303-b002"></a>
<!-- pdf-source: page=303; block=2; confidence=0.95 -->
Uniform results still fall short of nonuniform results in two ways: the optimal high-end conversion from mild hardness against time 2^{Ω(n)} on n-bit inputs to hardness 1/2 − 1/2^{Ω(n)} on O(n)-bit inputs against the same time bound is unknown; and NP amplification from hardness against time t reaches 1/2 − 1/(log t)^{Ω(1)}, rather than 1/2 − 1/t^{Ω(1)}. A coding-theoretic approach to the latter gap is cited.

<a id="pdf-bf2ce5422088-p303-b003"></a>
<!-- pdf-source: page=303; block=3; confidence=0.99 -->
## Other Cryptographic Primitives

<a id="pdf-bf2ce5422088-p303-b004"></a>
<!-- pdf-source: page=303; block=4; confidence=0.97 -->
Security amplification has also been studied for other cryptographic primitives and interactive protocols, where adversarial goals are more complex than computing or inverting a function; this survey refers readers to further sources.

<a id="pdf-bf2ce5422088-p303-b005"></a>
<!-- pdf-source: page=303; block=5; confidence=0.99 -->
A key component of many hardness amplification results mentioned above is the Hardcore Theorem of Impagliazzo [208] and variants. In its basic form, this theorem states that if a function \(f\) is mildly hard

<a id="pdf-bf2ce5422088-p304-b001"></a>
<!-- pdf-source: page=304; block=1; confidence=0.98 -->
The Hardcore Theorem supports hardness amplification and has connections to boosting, dense model theorems, computational entropy, and regularity lemmas. Its black-box proofs require substantial nonuniform advice; Holenstein’s uniform variant uses efficient sampling of random pairs \((x,f(x))\) and has applications to cryptographic pseudorandom generators.

<a id="pdf-bf2ce5422088-p304-b002"></a>
<!-- pdf-source: page=304; block=2; confidence=1.00 -->
## 8.2.4 Deterministic Extractors

<a id="pdf-bf2ce5422088-p304-b003"></a>
<!-- pdf-source: page=304; block=3; confidence=0.99 -->
Deterministic extractors remain useful when applications need high-quality randomness from physical sources, so seeded-extractor seed enumeration is unavailable, or when extractors for particular source classes have independent applications.

<a id="pdf-bf2ce5422088-p305-b001"></a>
<!-- pdf-source: page=305; block=1; confidence=0.98 -->
A disperser for two independent \(k\)-sources of length \(n\) is equivalent to a bipartite Ramsey graph with \(N=2^n\) vertices per side and no \(K\times K\) bipartite clique or independent set, where \(K=2^k\). Explicitly approaching the probabilistic bound \(K=O(\log N)\) is an open problem.

<a id="pdf-bf2ce5422088-p305-b002"></a>
<!-- pdf-source: page=305; block=2; confidence=0.98 -->
Chor and Goldreich constructed extractors for two independent \(k\)-sources when \(k>n/2\), including inner product modulo two. Barak, Impagliazzo, and Wigderson later obtained extractors for a constant number of independent sources with \(k=\delta n\) for any constant \(\delta>0\), using the finite-field Sum–Product Theorem: for prime \(p\), a subset \(A\subset\mathbb F_p\) not too close in size to \(p\) has either \(|A+A|\) or \(|A\cdot A|\) significantly larger than \(|A|\).

<a id="pdf-bf2ce5422088-p305-b003"></a>
<!-- pdf-source: page=305; block=3; confidence=0.97 -->
Subsequent methods yielded explicit extractors for three sources with min-entropy \(k=\delta n\), for a constant number of sources with \(k=n^\delta\), and dispersers for two sources with min-entropy \(k=n^{o(1)}\).

<a id="pdf-bf2ce5422088-p306-b001"></a>
<!-- pdf-source: page=306; block=1; confidence=0.99 -->
The previous best explicit construction of Ramsey graphs avoided cliques and independent sets of size \(K=2^{\sqrt{n}}\) and applied only to the nonbipartite case.

<a id="pdf-bf2ce5422088-p306-b002"></a>
<!-- pdf-source: page=306; block=2; confidence=0.99 -->
**Open Problem 8.11.** For every constant \(\delta>0\), construct an explicit function \(\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}\) such that for every two independent \(\delta n\)-sources \(X,Y\), \(\mathrm{Ext}(X,Y)\) is \(\varepsilon\)-close to uniform on \(\{0,1\}\).

<a id="pdf-bf2ce5422088-p306-b003"></a>
<!-- pdf-source: page=306; block=3; confidence=0.99 -->
Explicit extractors are known for several space-bounded source models. One construction deterministically extracts \(\Omega(n)\) bits from min-entropy \(k=\Omega(n)\) sources generated by a nonuniform \(O(n)\)-space algorithm. Under strong complexity assumptions, another runs in time \(\operatorname{poly}(s)\) and extracts from sources of min-entropy \(k=(1-\Omega(1))n\) generated by size-\(s\) circuits, with error \(\varepsilon=1/s\).

<a id="pdf-bf2ce5422088-p306-b004"></a>
<!-- pdf-source: page=306; block=4; confidence=0.99 -->
**Open Problem 8.12.** Under plausible complexity assumptions, determine whether a deterministic extractor computable in time \(\operatorname{poly}(s)\) can extract from size-\(s\) circuit sources with min-entropy \(k\le n/2\) and/or error \(\varepsilon=s^{-\omega(1)}\), or give evidence against such an extractor.

<a id="pdf-bf2ce5422088-p306-b005"></a>
<!-- pdf-source: page=306; block=5; confidence=0.98 -->
For condensers, it may not be necessary for the extractor’s computational complexity to exceed that of the source.

<a id="pdf-bf2ce5422088-p307-b001"></a>
<!-- pdf-source: page=307; block=1; confidence=0.98 -->
Recent unconditional extractors handle restricted circuit classes such as NC⁰ and AC⁰, including sources with sublinear min-entropy. This approach connects extractor construction to finding distributions that are hard for the circuit class to sample.

<a id="pdf-bf2ce5422088-p307-b002"></a>
<!-- pdf-source: page=307; block=2; confidence=0.99 -->
An affine source over a finite field $F$ is uniform on an affine subspace of $F^n$. If that subspace has dimension $k$, its min-entropy is $k\log |F|$.

<a id="pdf-bf2ce5422088-p307-b003"></a>
<!-- pdf-source: page=307; block=3; confidence=0.97 -->
For $F=\mathbb Z_2$, explicit extractors are known for affine sources with sublinear dimension $k=O(n)$, and dispersers for dimension $k=n^{o(1)}$. For fields of polynomial size, extractors are known for every subspace dimension $k\ge1$. Related work treats distributions generated by low-degree polynomial maps and zero sets of low-degree polynomials.

<a id="pdf-bf2ce5422088-p307-b004"></a>
<!-- pdf-source: page=307; block=4; confidence=0.98 -->
Some leading constructions for independent and affine sources use complex compositions or arithmetic-combinatorics tools; finding simpler constructions remains of interest, with progress in both settings.

<a id="pdf-bf2ce5422088-p307-b005"></a>
<!-- pdf-source: page=307; block=5; confidence=1.00 -->
## 8.2.5 Algebraic Pseudorandomness

<a id="pdf-bf2ce5422088-p307-b006"></a>
<!-- pdf-source: page=307; block=6; confidence=1.00 -->
### Algebraic Measures of Pseudorandomness

<a id="pdf-bf2ce5422088-p308-b001"></a>
<!-- pdf-source: page=308; block=1; confidence=0.99 -->
Algebraic measures of pseudorandomness can relate to statistical or computational measures, aid analysis of algebraic constructions, and have independent applications.

<a id="pdf-bf2ce5422088-p308-b002"></a>
<!-- pdf-source: page=308; block=2; confidence=1.00 -->
A random variable $X=(X_1,\ldots,X_n)\in\{0,1\}^n$ is $\varepsilon$-biased if, for every nonempty $S\subseteq[n]$, $(1-\varepsilon)/2\le \Pr[\bigoplus_{i\in S}X_i=1]\le(1+\varepsilon)/2$.

<a id="pdf-bf2ce5422088-p308-b003"></a>
<!-- pdf-source: page=308; block=3; confidence=0.99 -->
There is an explicit generator $G:\{0,1\}^d\to\{0,1\}^n$ with $d=O(\log(n/\varepsilon))$ such that $G(U_d)$ is $\varepsilon$-biased, hence fools all parity tests. Applications include almost $k$-wise independent hash functions, generators for small-width branching programs, derandomization, and almost-linear-length PCPs.

<a id="pdf-bf2ce5422088-p308-b004"></a>
<!-- pdf-source: page=308; block=4; confidence=0.98 -->
Small-bias generators correspond to binary linear codes whose nonzero codewords have weights in $[(1-\varepsilon)/2,(1+\varepsilon)/2]$ times the block length, and to Cayley expanders over $\mathbb Z_2^n$ with spectral expansion $1-\varepsilon$. For a group $G$ and $S\subseteq G$, the Cayley graph is the $|S|$-regular directed graph on $G$ with neighbors of $g$ given by $\{gs:s\in S\}$.

<a id="pdf-bf2ce5422088-p308-b005"></a>
<!-- pdf-source: page=308; block=5; confidence=0.99 -->
For $G=\mathbb Z_2^n$, define $\chi_S(x)=(-1)^{\bigoplus_{i\in S}x_i}$. The small-bias condition is equivalent to $|\mathbb E[\chi_S(X)]|\le\varepsilon$ for every nonempty $S\subseteq[n]$; equivalently, every nontrivial Fourier coefficient of the distribution is at most $\varepsilon$ in absolute value.

<a id="pdf-bf2ce5422088-p308-b006"></a>
<!-- pdf-source: page=308; block=6; confidence=0.98 -->
The equivalent viewpoints motivate extensions to codes over larger finite fields and to Cayley graphs and Fourier analysis over groups other than $\mathbb Z_2^n$.

<a id="pdf-bf2ce5422088-p309-b001"></a>
<!-- pdf-source: page=309; block=1; confidence=0.99 -->
For abelian groups, small-bias Fourier coefficients are the eigenvalues of the associated Cayley graph. Explicit constructions for many abelian groups, including $\mathbb Z_p^n$ for prime $p$, have seed length $O(\log\log |G|+\log(1/\varepsilon))$ and yield Cayley expanders with spectral expansion $1-\varepsilon$ and degree $\operatorname{poly}(\log|G|,1/\varepsilon)$.

<a id="pdf-bf2ce5422088-p309-b002"></a>
<!-- pdf-source: page=309; block=2; confidence=0.99 -->
Cayley expanders over abelian groups require degree $\Omega(\log N)$ for $N=|G|$ vertices; the same lower bound applies to Schreier graphs from group actions on vertices. Many constant-degree constructions, including Ramanujan graphs, instead use Cayley or Schreier graphs over nonabelian groups. Their spectral analysis uses representation theory and matrix-valued functions rather than scalar Fourier analysis.

<a id="pdf-bf2ce5422088-p309-b003"></a>
<!-- pdf-source: page=309; block=3; confidence=0.99 -->
More generally, we can take \(G=H^n\) for any finite group \(H\), and consider a random variable \(X=(X_1,\ldots,X_n)\) taking values in \(\{0,1\}^n\) to be pseudorandom if for every \((h_1,\ldots,h_n)\in H^n\), the distribution of \(h_1^{X_1}h_2^{X_2}\cdots h_n^{X_n}\) is statistically close to \(h_1^{R_1}h_2^{R_2}\cdots h_n^{R_n}\), where \(R=(R_1,\ldots,R_n)\) is uniformly distributed in \(\{0,1\}^n\).

<a id="pdf-bf2ce5422088-p310-b001"></a>
<!-- pdf-source: page=310; block=1; confidence=0.98 -->
distributed in \(\{0,1\}^n\). This notion is of interest in part because the function \(f_h(x_1,\ldots,x_n)=h_1^{x_1}\cdots h_n^{x_n}\) can be computed by a read-once branching program of width \(|H|\) (see Section 8.2.1). Thus constructing generators fooling such “group product programs” are a natural warm-up to constructing pseudorandom generators for space-bounded computation, and in fact are equivalent to constructing generators for permutation branching programs in the case of constant width [250].

<a id="pdf-bf2ce5422088-p310-b002"></a>
<!-- pdf-source: page=310; block=2; confidence=0.91 -->
Generators that fool group product programs are a warm-up for space-bounded pseudorandom generators; at constant width, this problem is equivalent to fooling permutation branching programs [250].

<a id="pdf-bf2ce5422088-p310-b003"></a>
<!-- pdf-source: page=310; block=3; confidence=0.96 -->
A sum of $d$ small-bias spaces over a finite field cannot be distinguished from uniform by degree-$d$ polynomials [75, 270, 413]. This connects to Gowers uniformity norms and higher-order Fourier analysis [180, 181].

<a id="pdf-bf2ce5422088-p310-b004"></a>
<!-- pdf-source: page=310; block=4; confidence=1.00 -->
## Explicit Constructions via Polynomial Evaluation

<a id="pdf-bf2ce5422088-p310-b005"></a>
<!-- pdf-source: page=310; block=5; confidence=0.98 -->
**Definition.** For a finite field $F$, a seed set $E\subseteq F^t$, and input $f\in F^n$ interpreted as a low-degree polynomial in $t$ variables, define $\Gamma:F^n\times E\to F^m$ by $\Gamma(f,y)=(f_1(y),\ldots,f_m(y))$, where $f_1,\ldots,f_m$ are related low-degree polynomials derived from $f$. Reed–Solomon and Reed–Muller constructions use $m=1$ and $f_1=f$; Parvaresh–Vardy obtains related polynomials by powering modulo an irreducible polynomial; Folded Reed–Solomon uses $f_i(Y)=f(\gamma^{i-1}Y)$.

<a id="pdf-bf2ce5422088-p310-b006"></a>
<!-- pdf-source: page=310; block=6; confidence=0.99 -->
If outputs evaluate $f$ at points $g_1(y),\ldots,g_m(y)$, this is equivalently evaluation at $y$ of $f_i=f\circ g_i$.

<a id="pdf-bf2ce5422088-p311-b001"></a>
<!-- pdf-source: page=311; block=1; confidence=0.98 -->
Prior to Parvaresh–Vardy codes, constructions of this type were used for extractors and pseudorandom generators. Specifically, Miltersen and Vinodchandran [289] show that if we take \(f\) to describe a multivariate polynomial (via low-degree extension) and evaluate it on the points of a random axis-parallel line through \(y\), we obtain a hitting-set generator construction against nondeterministic circuits (assuming \(f\) has appropriate worst-case hardness for nondeterministic circuits); this construction has played a key role in derandomizations of \(\mathrm{AM}\) under uniform assumptions [195, 358]. Ta-Shma, Zuckerman, and Safra [384] showed that a similar construction yields randomness extractors with seed length \((1+O(1))\log n\) for polynomially small min-entropy and polynomial entropy loss. Shaltiel and Umans [356, 399] showed that evaluating the \(t\)-variate polynomial \(f\) at the points \(y,\gamma y,\gamma^2 y,\ldots,\gamma^{m-1}y\), where \(\gamma\) is a primitive element of the field of size \(|\mathbb{F}|^t\) (which we associate with \(\mathbb{F}^t\)), yields both a very good extractor construction and an optimal construction of pseudorandom generators from worst-case hard functions. Recently, Kopparty, Saraf, and Yekhanin [249] have introduced yet another useful way of obtaining the “related polynomials” \(f_1,\ldots,f_m\), namely by taking derivatives of \(f\); this has yielded the first codes with rate approaching 1 while being locally (list-)decodable in sublinear time [249, 248] as well as codes matching the optimal rate-distance tradeoff of Folded Reed–Solomon Codes [193, 248].

<a id="pdf-bf2ce5422088-p311-b002"></a>
<!-- pdf-source: page=311; block=2; confidence=0.99 -->
Polynomial evaluation is proposed as a route to unified, near-optimal constructions of pseudorandom objects (Open Problem 8.5).

<a id="pdf-bf2ce5422088-p312-b001"></a>
<!-- pdf-source: page=312; block=1; confidence=1.00 -->
## Acknowledgments

<a id="pdf-bf2ce5422088-p313-b001"></a>
<!-- pdf-source: page=313; block=1; confidence=0.99 -->
The author credits course scribes, reviewers, colleagues, and institutions that supported the survey.

<a id="pdf-bf2ce5422088-p314-b001"></a>
<!-- pdf-source: page=314; block=1; confidence=0.99 -->
Bibliography entries [1]–[10], covering work on derandomization, identity testing, primality, arithmetic circuits, Fourier coefficients, and parallel sorting.

<a id="pdf-bf2ce5422088-p315-b001"></a>
<!-- pdf-source: page=315; block=1; confidence=0.99 -->
Bibliography entries [11]–[26], covering deterministic simulation, random walks, expanders, pseudorandomness, discrepancy, frequency moments, and probabilistic methods.

<a id="pdf-bf2ce5422088-p316-b001"></a>
<!-- pdf-source: page=316; block=1; confidence=1.00 -->
Bibliographic entries on derandomization, pseudorandomness, proof verification, algebra, and complexity theory; no mathematical statements are given.

<a id="pdf-bf2ce5422088-p317-b001"></a>
<!-- pdf-source: page=317; block=1; confidence=1.00 -->
Bibliographic entries on randomized proof systems, extractors, entropy, random number generation, and related complexity topics; no mathematical statements are given.

<a id="pdf-bf2ce5422088-p318-b001"></a>
<!-- pdf-source: page=318; block=1; confidence=1.00 -->
Bibliographic entries on expanders, extractors, coding, cryptography, pseudorandomness, and program checking; no mathematical statements are given.

<a id="pdf-bf2ce5422088-p322-b001"></a>
<!-- pdf-source: page=322; block=1; confidence=1.00 -->
Bibliography entries [124]–[141], covering work on multiplicity methods, subspace-evasive sets, locally decodable codes, cryptography, list decoding, graph theory, product distributions, interactive proofs, Markov chains, concatenated codes, and intersection theorems.

<a id="pdf-bf2ce5422088-p323-b001"></a>
<!-- pdf-source: page=323; block=1; confidence=1.00 -->
Bibliography entries [142]–[159] cite work on sparse-table access, expander eigenvalues, truncated integers, deterministic encryption, superconcentrators, affine-source extractors, low-density parity-check codes, polynomial self-testing and correction, coding, probabilistic computation, expander walks, semidefinite approximation, sampling, cryptography, and promise problems.

<a id="pdf-bf2ce5422088-p324-b001"></a>
<!-- pdf-source: page=324; block=1; confidence=1.00 -->
Bibliography entries [160]–[175] cite work on probabilistic proofs, complexity, pseudorandom generators, randomized complexity, random-function construction, property testing, hardness amplification, hard-core predicates, computational indistinguishability, zero-knowledge proofs, Yao’s XOR lemma, BPP derandomization, hashing, and cryptography.

<a id="pdf-bf2ce5422088-p328-b001"></a>
<!-- pdf-source: page=328; block=1; confidence=1.00 -->
Bibliography entries on coding theory, derandomization, graph expansion and random walks, extractors, advice-taking machines, approximation algorithms, cryptography, character sums, polynomial identity testing, and circuit lower bounds.

<a id="pdf-bf2ce5422088-p329-b001"></a>
<!-- pdf-source: page=329; block=1; confidence=1.00 -->
Bibliography entries on boosting and hard-core sets, communication complexity, randomness extraction, coding, pseudorandom generators, pairwise independence, the polynomial hierarchy, one-way functions, and polynomial identity testing.

<a id="pdf-bf2ce5422088-p330-b001"></a>
<!-- pdf-source: page=330; block=1; confidence=1.00 -->
Bibliography entries on Kolmogorov complexity, finite fields, hitting sets, approximate inclusion–exclusion, matching algorithms, graph capacity and expanders, pseudorandom generators, extractors, and parallel algorithms.

<a id="pdf-bf2ce5422088-p331-b001"></a>
<!-- pdf-source: page=331; block=1; confidence=0.99 -->
Bibliographic entries [280]–[296] cite work on approximate circuit counting, pairwise independence, coding theory, expander graphs and Markov chains, primality testing, derandomization, randomized algorithms, matching, data streams, and small-bias probability spaces.

<a id="pdf-bf2ce5422088-p332-b001"></a>
<!-- pdf-source: page=332; block=1; confidence=0.99 -->
Bibliographic entries [297]–[316] cite work on graph eigenvalues and concentrators, pseudorandom generators, space-bounded computation, randomness extraction, hardness versus randomness, Boolean-function analysis, error-correcting codes, and probabilistic constructions.

<a id="pdf-bf2ce5422088-p333-b001"></a>
<!-- pdf-source: page=333; block=1; confidence=0.99 -->
Bibliographic entries [317]–[331] cite work on mixing, extractors, randomness recycling and reduction, arithmetic progressions, circuit lower bounds, natural proofs, coding theory, log-space connectivity, and pseudorandom walks.

<a id="pdf-bf2ce5422088-p334-b001"></a>
<!-- pdf-source: page=334; block=1; confidence=0.99 -->
Bibliography entries cover expanders and extractors, entropy, property testing, pseudorandom generators, complexity, and semirandom sources; no mathematical statements are given.

<a id="pdf-bf2ce5422088-p335-b001"></a>
<!-- pdf-source: page=335; block=1; confidence=0.99 -->
[347] R. Santhanam, “Circuit lower bounds for Merlin-Arthur classes,” in *STOC’07 — Proceedings of the Annual ACM Symposium on Theory of Computing*, pp. 275–283, New York, 2007.

<a id="pdf-bf2ce5422088-p336-b001"></a>
<!-- pdf-source: page=336; block=1; confidence=0.99 -->
Bibliography entries cover complexity and randomness, expander codes and spectral graph theory, weak random sources, hashing, coding theory, and pseudorandom generators; no mathematical statements are given.

<a id="pdf-bf2ce5422088-p337-b001"></a>
<!-- pdf-source: page=337; block=1; confidence=0.99 -->
Bibliography entries [383]–[399] cover extractors, pseudorandom generators, coding theory, finite-group Fourier analysis, additive combinatorics, and computational complexity. No mathematical statements or proofs are given.

<a id="pdf-bf2ce5422088-p338-b001"></a>
<!-- pdf-source: page=338; block=1; confidence=0.99 -->
Bibliography entries [400]–[416] concern probabilistic proof systems, pseudoentropy, extractors, graph and circuit complexity, error-correcting codes, randomness extraction, and pseudorandomness. No mathematical statements or proofs are given.

<a id="pdf-bf2ce5422088-p339-b001"></a>
<!-- pdf-source: page=339; block=1; confidence=0.99 -->
Bibliography entries [417]–[428] cover hash functions, circuit lower bounds, list decoding, affine extractors, locally decodable codes, sparse-polynomial algorithms, and randomness-efficient simulation and sampling. No mathematical statements or proofs are given.
