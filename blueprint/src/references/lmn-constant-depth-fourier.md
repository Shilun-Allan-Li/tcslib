<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 63759bd909d5b75d76be750f9993ce95106bf03476e9e13d7791bd54f3a19ff9 -->

<a id="pdf-63759bd909d5-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Constant Depth Circuits, Fourier Transform, and Learnability

Nathan Linial (Hebrew University, Jerusalem, Israel), Yishay Mansour (Tel-Aviv University, Tel-Aviv, Israel), and Noam Nisan (Hebrew University, Jerusalem, Israel).

<a id="pdf-63759bd909d5-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Boolean functions in AC⁰ are studied via harmonic analysis on the cube. Main result: an AC⁰ Boolean function has almost all of its "power spectrum" on the low-order Fourier coefficients; hence AC⁰ functions can be approximated well by low-degree real polynomials. Key proof ingredient: Håstad's switching lemma. Derived properties: AC⁰ functions have low "average sensitivity" and cannot be pseudorandom function generators. Main application: an O(n^{polylog(n)})-time algorithm for learning AC⁰ functions, which observes the function on O(n^{polylog(n)}) uniformly random inputs, computes an approximate Fourier transform, and then predicts the function's value on new random inputs with high probability.

<a id="pdf-63759bd909d5-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.85 -->
Preliminary version appeared in Proc. 30th Annual Symposium on Foundations of Computer Science, IEEE, 1989, pp. 574–579. Author affiliations and grant acknowledgments (NSF CCR 86-5727, ARO DAAL 03-86-K-017, ISEF fellowship; work done at MIT LCS, IBM Almaden, and Stanford). Standard ACM copyright notice.

<a id="pdf-63759bd909d5-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.80 -->
ACM subject descriptors (Computation by Abstract Devices; Analysis of Algorithms; Probability and Statistics; Learning) and keywords: AC⁰ circuits, approximation, Boolean functions, complexity, Fourier transform, harmonic analysis, learning.

<a id="pdf-63759bd909d5-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
## 1. Introduction

Harmonic analysis is widely used throughout classical mathematics. Recently, Kahn et al. [9] suggested using harmonic analysis on the hypercube for studying Boolean functions, proving inequalities that the Fourier coefficients of Boolean functions must satisfy and deriving bounds on the "influence" of variables; harmonic analysis was also used [3] for lower bounds on the size of decision trees, DNF, and CNF. This paper relates the computational complexity of Boolean functions to their Fourier transform, deriving an inequality satisfied by the transform of constant-depth-circuit functions and applying it to complexity and learnability.

<a id="pdf-63759bd909d5-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.88 -->
Best-known constant-depth lower bound: computing parity requires very large size; small constant-depth circuits cannot even approximate parity well (Håstad). Since the Fourier coefficient f̂(S) measures the correlation between f and the parity of the input bits in S, any function computed by a small constant-depth circuit must have very small "high" Fourier coefficients ("high" = coefficients for sets S of large cardinality).

<a id="pdf-63759bd909d5-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
**Main Lemma.** Let f be a Boolean function on n variables computable by a Boolean circuit of depth d and size M, and let t be any integer. Then

$$\sum_{S \subseteq \{1,\dots,n\},\ |S|>t} \hat f(S)^2 \;\le\; 2M\,2^{-t^{1/d}/20},$$

where $\hat f(S)$ denotes the Fourier transform of f at S.

<a id="pdf-63759bd909d5-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.95 -->
First application: learning Boolean functions computed by polynomial-size AC⁰ constant-depth circuits. The algorithm observes the circuit's behavior on O(n^{polylog(n)}) uniformly random inputs to derive, with high probability, good approximations of all the "low" Fourier coefficients. By the Main Lemma the "high" coefficients carry little power, so the approximated low coefficients suffice to predict the circuit's behavior on new random inputs, and few low coefficients means this can be done efficiently.

<a id="pdf-63759bd909d5-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
The algorithm rests on three ideas: (1) lower bounds (negative results) can be used to construct learning algorithms (positive results), analogous to how lower bounds enable derandomization/pseudorandom generators; (2) learning can be achieved by estimating Fourier coefficients; (3) real arithmetic and real-valued functions are used to approximate Boolean functions.

<a id="pdf-63759bd909d5-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.85 -->
Unlike Valiant's distribution-free (PAC) learning: this algorithm runs in time O(n^{polylog(n)}) (not polynomial) and learns only under the uniform distribution on inputs (not arbitrary distributions). On the positive side, the concept class learned (AC⁰) is far richer than earlier positive results (k-DNF, k-decision lists), whereas richer classes such as NC¹ had only negative results.

<a id="pdf-63759bd909d5-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
Consequences of the Main Lemma for functions in AC⁰:

1. Every AC⁰ function can be approximated well by a low-degree real polynomial (complements results of [14], [17] over finite fields).
2. Every AC⁰ function has low average sensitivity: for random input and random bit position, flipping that bit rarely changes the function value.
3. AC⁰ functions cannot be pseudorandom function generators (in the sense of [6]).
4. AC⁰ functions cannot distinguish the uniform distribution from any polynomially bounded, polylog-wise independent distribution. (A polynomially bounded distribution over Z₂ⁿ is one in which every input has probability less than poly(n)/2ⁿ.)

<a id="pdf-63759bd909d5-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.92 -->
Organization: Section 2 gives notation, definitions, and Fourier-transform background on the hypercube; Section 3 proves the Main Lemma; Section 4 covers the learning algorithm; Section 5 gives further applications of the Main Lemma.

<a id="pdf-63759bd909d5-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.95 -->
## 2. Notation

### 2.1. Fourier Transform

<a id="pdf-63759bd909d5-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.90 -->
**Definition (2.1).** Boolean functions on n variables are viewed as real-valued functions f: {0,1}ⁿ → {−1, 1}. The set of all real functions on the cube is a 2ⁿ-dimensional real vector space equipped with the inner product

$$\langle g, f \rangle = 2^{-n} \sum_{x} f(x)g(x) = \mathbb{E}(fg).$$

<a id="pdf-63759bd909d5-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.92 -->
The norm of a function is the Euclidean norm $\|f\| = \sqrt{\langle f, f\rangle}$ ($E$ = expectation). Motivation: harmonic analysis amounts to choosing a clever basis (the group characters) for the space of real functions on a group; here the group is the cube $\mathbb{Z}_2^n$.

<a id="pdf-63759bd909d5-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
**Definition.** For each subset $S \subseteq \{1,\dots,n\}$, define $\chi_S(x_1,\dots,x_n) = +1$ if $\sum_{i\in S} x_i$ is even, and $-1$ if $\sum_{i\in S} x_i$ is odd.

<a id="pdf-63759bd909d5-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.88 -->
**Properties.** (i) For all $A,B$: $\chi_A\,\chi_B = \chi_{A\triangle B}$, where $A\triangle B$ is symmetric difference. (ii) The family $\{\chi_S : S\subseteq\{1,\dots,n\}\}$ is an orthonormal basis: $\langle\chi_A,\chi_B\rangle = 0$ for $A\neq B$ and $\langle\chi_A,\chi_A\rangle = 1$. Every real function on the cube has a unique expansion $f = \sum_S \hat{f}(S)\,\chi_S$ with real coefficients; the coefficients form the Fourier transform, and the $S$th Fourier coefficient is $\hat{f}(S) = \langle f, \chi_S\rangle$.

<a id="pdf-63759bd909d5-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.96 -->
**Definition.** For Boolean $f$, $\hat{f}(S) = \Pr\big[f(x) = \bigoplus_{i\in S} x_i\big] - \Pr\big[f(x) \neq \bigoplus_{i\in S} x_i\big]$, where $x=(x_1,x_2,\dots,x_n)$ is chosen uniformly at random in $\{0,1\}^n$.

<a id="pdf-63759bd909d5-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.90 -->
**Parseval's identity.** Orthonormality gives $\|f\|^2 = \sum_{S\subseteq\{1,\dots,n\}} \hat{f}(S)^2$. In particular, if $f$ is Boolean then $\|f\| = 1$.

<a id="pdf-63759bd909d5-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.92 -->
**Definition.** $\deg(f)$ is the size of the largest set $S$ with $\hat{f}(S)\neq 0$; this equals the degree of $f$ written as a real multilinear polynomial.

<a id="pdf-63759bd909d5-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.85 -->
**Definition (AC0 circuits).** An AC0 circuit is built from unbounded-fanin AND and OR gates on inputs $x_1,\dots,x_n$ and their negations $\bar{x}_1,\dots,\bar{x}_n$. Its size (number of gates) is bounded by a polynomial in $n$ and its depth by a constant. WLOG the circuit is leveled: gates on the same level share a type, and types alternate AND/OR between levels, with each gate's inputs coming from the previous level. The class of depth-$d$ such circuits is denoted $AC^0[d]$.

<a id="pdf-63759bd909d5-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.88 -->
**Definition (restriction).** A restriction $\rho$ maps each input variable to $0$, $1$, or $*$. The restricted function $f_\rho$ has as its variables the $x_i$ with $\rho(x_i)=*$; all others are fixed per $\rho$. For $S=\{x_{i_1},\dots,x_{i_{|S|}}\}$ and $R=(r_1,\dots,r_{|S|})\in\{0,1\}^{|S|}$, $S\to R$ denotes the restriction $\rho$ with $\rho(x_{i_j})=r_j$ for $x_{i_j}\in S$ and $\rho(x)=*$ for $x\notin S$. A random restriction with parameter $p$ sets each variable independently: $\Pr[\rho(x_i)=*]=p$ and $\Pr[\rho(x_i)=1]=\Pr[\rho(x_i)=0]=(1-p)/2$. We write $\Pr[*]$ for $\Pr[\rho(x_i)=*]$.

<a id="pdf-63759bd909d5-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.83 -->
**Definitions.** For real $r$, $\mathrm{sign}(r)=1$ if $r>0$, $-1$ if $r<0$, and $\mathrm{sign}(0)=0$. The complement of $S\subseteq\{1,\dots,n\}$ is $S^c$. A *minterm* of a Boolean function is a minimal set of variables such that setting all of them to one forces the function to one (equivalently, a minimal $S$ with $f_{S\to \vec 1}\equiv 1$). A *maxterm* is a minimal set $S$ forcing the function to zero (i.e. $f_{S\to \vec 0}\equiv 0$).

<a id="pdf-63759bd909d5-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.80 -->
Håstad's Switching Lemma states that AC0 functions simplify substantially under random restrictions. The article uses a stronger form (attributed to Håstad and Boppana, [8, p. 65]) than originally stated, which the original proof also yields.

<a id="pdf-63759bd909d5-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
**Lemma 1 (Håstad).** Let $f$ be given by a CNF formula in which each clause has size at most $t$, and choose a random restriction $\rho$ with parameter $p$ (i.e. $\Pr[\rho(x_i)=*]=p$). Then with probability at least $1-(5pt)^s$, $f_\rho$ can be expressed as a DNF formula in which every clause has size at most $s$ and the clauses accept pairwise disjoint sets of inputs.

<a id="pdf-63759bd909d5-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.88 -->
**Corollary 1.** If $f$ is given by a CNF (or DNF) of bottom fanin at most $t$, and $\rho$ is chosen at random with $\Pr[*]=p$, then $\Pr[\deg(f_\rho) > s] < (5pt)^s$.

<a id="pdf-63759bd909d5-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.80 -->
**Proof.** Whenever $f_\rho$ satisfies conditions (1) and (2) of Håstad's lemma, then for every set $S$ with $|S|>s$, each clause of the DNF for $f_\rho$ accepts exactly the same number of strings of even parity as of odd parity on $S$ (because clause size is bounded by $s$, so at least one variable of $S$ does not appear in the clause). Since the clauses accept disjoint input sets, $f_\rho$ accepts equally many even- and odd-parity strings on $S$, so $\hat{f_\rho}(S)=0$; hence $\deg(f_\rho)\le s$. $\qquad\square$

<a id="pdf-63759bd909d5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
**Lemma 2.** Let $f$ be a Boolean function computed by a circuit of size $M$ and depth $d$. Then $\Pr[\deg(f_\rho) > s] \le M\,2^{-s}$, where $\rho$ is a random restriction with $\Pr[*] = \dfrac{1}{10^{d}\,s^{d-1}}$.

<a id="pdf-63759bd909d5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
**Proof.** View $\rho$ as a first random restriction with $\Pr[*]=1/10$ followed by $d-1$ successive restrictions each with $\Pr[*]=1/(10s)$.

After the first restriction, with high probability every bottom-level fanin is at most $s$. For each bottom gate (WLOG bottom level is AND), two cases: (1) original fanin $\ge 2s$: probability the gate is not eliminated (no input assigned $0$) is at most $0.55^{2s} < 2^{-s}$; (2) original fanin $\le 2s$: probability that at least $s$ inputs are assigned $*$ is at most $\binom{2s}{s}(0.1)^{s} < 2^{-s}$. So failure at this stage is at most $m_1 2^{-s}$, with $m_1$ the number of bottom gates.

Then apply $d-2$ further restrictions with $\Pr[*]=1/(10s)$. After each, use the switching lemma to convert the bottom two levels from CNF to DNF (or vice versa), collapsing the second and third levels from the bottom into one and reducing depth by one. For each gate, the probability it has a minterm (respectively maxterm) of size larger than $s$ is bounded by $2^{-s}$; the probability that some level-$i$ gate has such a minterm/maxterm is at most $m_i 2^{-s}$, with $m_i$ the number of gates at level $i$.

After these $d-2$ stages a CNF (or DNF) of bottom fanin at most $s$ remains; apply the last restriction with $\Pr[*]=1/(10s)$ and Corollary 1 to obtain degree at most $s$. Summing, each gate of the original circuit contributes $2^{-s}$ failure probability exactly once, giving total $M\,2^{-s}$. $\qquad\square$

<a id="pdf-63759bd909d5-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.78 -->
The article now turns to analyzing the probability that restrictions of $f$ have low degree, beginning with a lemma relating the Fourier transform of $f$ to the transforms of its restrictions.

<a id="pdf-63759bd909d5-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.90 -->
**Lemma 3.** Let $f$ be a Boolean function and $S$ an arbitrary subset of the variables. Then for any subset $A$ of the variables,
$$\hat{f}(A) = 2^{-|S^c|} \sum_{R\in\{0,1\}^{|S^c|}} \chi_{A\cap S^c}(R)\; \widehat{f_{S^c\leftarrow R}}(A\cap S).$$
$\qquad\square$

<a id="pdf-63759bd909d5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Proof (continuation).** Recall $\hat f(A)=E_x[f\chi_A]$; the right-hand side averages first over the variables in $S$ and then over those in $S^c$. It is rearranged into $2^{-|S^c|}\sum_{R_1\in\{0,1\}^{|S^c|}}2^{-|S|}\sum_{R_2\in\{0,1\}^{|S|}}\chi_{A\cap S^c}(R_1)\,\chi_{A\cap S}(R_2)\,f_{S^c\leftarrow R_1}(R_2)$. Key identities: $\chi_{A\cap S^c}(R_1)\chi_{A\cap S}(R_2)=\chi_A(x)$ for the $x$ that equals $R_1$ on $S^c$ and $R_2$ on $S$, and $f_{S^c\leftarrow R_1}(R_2)=f(x)$. Averaging over the pair $(R_1,R_2)$ is averaging over $x\in\{0,1\}^n$ (using $|S|+|S^c|=n$), giving $2^{-n}\sum_{x\in\{0,1\}^n}\chi_A(x)f(x)$, which equals $\hat f(A)$ by definition. ∎

<a id="pdf-63759bd909d5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.94 -->
**Lemma 4.** Let $f$ be Boolean and $S$ an arbitrary subset. For any $B\subseteq S$,
$$\sum_{C\subseteq S^c}\hat f(B\cup C)^2 = 2^{-|S^c|}\sum_{R\in\{0,1\}^{|S^c|}}\widehat{f_{S^c\leftarrow R}}(B)^2.$$

<a id="pdf-63759bd909d5-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.93 -->
**Proof.** By Lemma 3, express $\widehat{f_{S^c\leftarrow R}}(B)$ in terms of the coefficients $\hat f(B\cup C)$, $C\subseteq S^c$, using $\chi_{B\cup C}(R)=\chi_C(R)$ and $(B\cup C)\cap S=B$. Expanding the square and summing over $C\subseteq S^c$ produces a double sum over restrictions $R_1,R_2$ whose inner factor $2^{-|S^c|}\sum_{C\subseteq S^c}\chi_C(R_1\oplus R_2)$ equals $1$ when $R_1=R_2$ and $0$ otherwise. The double sum therefore collapses to $2^{-|S^c|}\sum_{R\in\{0,1\}^{|S^c|}}\widehat{f_{S^c\leftarrow R}}(B)^2$. ∎

<a id="pdf-63759bd909d5-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.70 -->
**Lemma 5.** Let $f$ be Boolean, $S$ an arbitrary subset, and $k$ an integer. Then
$$\sum_{A:\,|A\cap S|>k}\hat f(A)^2 \le \Pr_R\big[\deg(f_{S^c\leftarrow R})>k\big],$$
where $R$ is a uniformly random 0-1 assignment to the variables in $S^c$.

<a id="pdf-63759bd909d5-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.65 -->
**Proof.** If $\deg(f_{S^c\leftarrow R})\le k$, then for every $A$ with $|A\cap S|>k$ the coefficient $\widehat{f_{S^c\leftarrow R}}(A\cap S)=0$. As $f_{S^c\leftarrow R}$ is Boolean, $\sum_{|B|>k}\widehat{f_{S^c\leftarrow R}}(B)^2\le 1$, so it suffices to prove
$$\sum_{A:\,|A\cap S|>k}\hat f(A)^2 = E_R\Big[\sum_{|B|>k}\widehat{f_{S^c\leftarrow R}}(B)^2\Big].$$
Rewrite the left side as $\sum_{B\subseteq S,\,|B|>k}\sum_{D\subseteq S^c}\hat f(D\cup B)^2$; by Lemma 4 this equals $\sum_{B\subseteq S,\,|B|>k}2^{-|S^c|}\sum_{R\in\{0,1\}^{|S^c|}}\widehat{f_{S^c\leftarrow R}}(B)^2$, which is exactly the claimed expectation. ∎

<a id="pdf-63759bd909d5-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.70 -->
Averaging Lemma 5's sums over all choices of the subset $S$ yields a bound on the total weight of the high-order Fourier coefficients.

<a id="pdf-63759bd909d5-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->
**Lemma 6.** Let $f$ be Boolean, $t$ an integer, and $0<p<1$ with $pt>8$. Then
$$\sum_{|A|>t}\hat f(A)^2 \le 2\,E_S\Big(\sum_{|A\cap S|>pt/2}\hat f(A)^2\Big),$$
where $S$ is a random subset in which each variable is included independently with probability $p$.

<a id="pdf-63759bd909d5-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.65 -->
**Proof.** By Chernoff bounds, for a fixed $A$ with $|A|>t$ (so $E[|A\cap S|]=p|A|>pt$), $\Pr_S[|A\cap S|>pt/2]\ge 1-\exp(-tp/8)$; since $tp>8$ this probability is at least $1/2$. Thus each $A$ with $|A|>t$ contributes $\hat f(A)^2$ to the $|A\cap S|>pt/2$ sum for at least half of the random sets $S$. Averaging over $S$ and applying Lemma 5 with $k=pt/2$ gives the stated bound. ∎

<a id="pdf-63759bd909d5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->
**Lemma 7 (Main Lemma).** Let $f$ be Boolean, computed by a circuit of depth $d$ and size $M$, and let $t$ be any integer. Then
$$\sum_{|A|>t}\hat f(A)^2 \le 2M\,2^{-t^{1/d}/20}.$$

<a id="pdf-63759bd909d5-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.90 -->
**Proof.** Fix $p=1/(10\,t^{(d-1)/d})$ and $s=pt/2=t^{1/d}/20$. By Lemma 6 (each variable in $S$ chosen independently w.p. $p$) and Lemma 5, the weight is bounded above by $2E_S\Pr[\deg(f_{S^c\leftarrow R})>s]$. The restriction $S^c\leftarrow R$ formed by first choosing $S$ (each variable w.p. $p$) and then a random 0-1 assignment $R$ on $S^c$ has exactly the distribution of a random restriction $\rho$ with $\Pr[\ast]=p$. Since by the choice of $p,s$ we have $p\le 1/(10^{d}s^{d-1})$, Lemma 2 applies and bounds the quantity by $2M\,2^{-s}=2M\,2^{-t^{1/d}/20}$. ∎

<a id="pdf-63759bd909d5-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.90 -->
## 4. Learning Constant Depth Circuits

<a id="pdf-63759bd909d5-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.75 -->
Sets up learning of Boolean concepts: a known concept class contains an unknown target; from input/output examples the learner seeks a concept close to it. Models differ in how examples are selected (by the algorithm, uniformly at random, from an unknown distribution, or adversarially) and in the notion of closeness (agreement probability under some distribution). This paper uses a two-phase model. In the learning phase the algorithm receives random inputs $x$ together with $f(x)$; in the prediction phase it receives only random inputs $x$ and must output a value for $f(x)$.

<a id="pdf-63759bd909d5-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.65 -->
**Definition.** For a distribution $D$, an algorithm is an $(\epsilon,\delta,D)$ prediction algorithm for $f$ if
$$\Pr_D[\text{the algorithm disagrees with } f \text{ on more than an } \epsilon \text{ fraction of the inputs}] < \delta.$$

<a id="pdf-63759bd909d5-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
Presents an (ε, δ, U) learning algorithm for circuits of depth d and size M under the uniform distribution U. For fixed d the running time is quasi-polynomial in ε, δ, and M. The algorithm has a learning phase (estimate Fourier coefficients of f) and a prediction phase (use the estimates to predict f's value).

<a id="pdf-63759bd909d5-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.82 -->
**4.1 Learning Phase.** The algorithm observes f on m randomly chosen sample points x_1,...,x_m, where m = 4(2n^k/ε) ln(2n^k/δ) and k = (20 log(2M/ε))^d. Its approximation a_S to the S-th Fourier coefficient f̂(S) is the empirical average (1/m) Σ_{i=1}^m f(x_i) χ_S(x_i) for all |S| ≤ k, and a_S = 0 for all |S| > k.

<a id="pdf-63759bd909d5-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.90 -->
**Prediction Phase.** The predicted value of f on input x is f(x) = sign( Σ_{|S|≤k} a_S χ_S(x) ).

<a id="pdf-63759bd909d5-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Theorem 1.** The above algorithm is an (ε, δ, U) learning algorithm for circuits of depth d and size M, where U is the uniform distribution. Its proof uses Lemmas 8 and 9.

<a id="pdf-63759bd909d5-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.92 -->
**Lemma 8.** With high probability all low-order coefficients are approximated well: Pr[ for some S with |S| ≤ k, |a_S − f̂(S)| > √(ε/(2n^k)) ] ≤ δ.

<a id="pdf-63759bd909d5-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.90 -->
**Proof.** For a subset S consider the random variable Y_S = f(x) χ_S(x). Its expected value is, by definition, f̂(S). The algorithm estimates this expectation by averaging over m samples. The lemma follows from a standard application of Chernoff bounds (see [7]).

<a id="pdf-63759bd909d5-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.92 -->
**Lemma 9.** Let f be a Boolean function and g an arbitrary function such that Σ_S (f̂(S) − ĝ(S))^2 < ε. Then Pr[f(x) ≠ sign(g(x))] < ε.

<a id="pdf-63759bd909d5-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.90 -->
**Proof.** Since f is Boolean, f(x) ≠ sign(g(x)) implies |f(x) − g(x)| > 1. Note ||f − g||^2 = E_x[(f(x) − g(x))^2]; thus Pr[|f(x) − g(x)| > 1] ≤ ||f − g||^2. Finally, by Parseval's equality, ||f − g||^2 = Σ_S (f̂(S) − ĝ(S))^2 ≤ ε.

<a id="pdf-63759bd909d5-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.85 -->
**Proof of Theorem 1.** Consider g = Σ_{|S|≤k} a_S χ_S, so ĝ(S) = 0 for |S| > k. Since f has a circuit of depth d and size M, the Main Lemma gives Σ_{|S|>k} (f̂(S) − ĝ(S))^2 = Σ_{|S|>k} f̂(S)^2 < ε/2.

<a id="pdf-63759bd909d5-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
By Lemma 8, with probability at least 1 − δ, (ĝ(S) − f̂(S))^2 ≤ ε/(2n^k) for every set |S| ≤ k. Whenever this is the case, g satisfies the conditions of Lemma 9, so sign(g) disagrees with f on no more than an ε fraction of the inputs. ∎

<a id="pdf-63759bd909d5-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**5. Further Corollaries.** The Main Lemma is used to derive new properties of functions in AC^0.

<a id="pdf-63759bd909d5-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
**5.1 Approximations by a Low Degree Polynomial.** Boolean functions viewed as real-valued can be approximated by simple real functions such as low-degree polynomials; this complements the finite-field approximation results of [14] and [17].

<a id="pdf-63759bd909d5-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.85 -->
**Lemma 10.** Let f ∈ AC^0[d]. Then for every ε > 0 there exists a polynomial p of degree at most O(log(n/ε)^d) such that ||f − p|| < ε.

<a id="pdf-63759bd909d5-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.85 -->
**Proof.** Approximate f by p = Σ_{|S|≤k} f̂(S) m_S, where m_S = Π_{l∈S} x_l and the input bits x_l take values 1 and −1 (for false and true). The lemma becomes a restatement of the Main Lemma. (Remark: [14] and [17] over finite fields yield more general weighted approximations, corresponding to arbitrary probability distributions; the present result applies only to the uniform distribution.)

<a id="pdf-63759bd909d5-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.90 -->
**5.2 Low Average Sensitivity.** **Definition 1.** For a Boolean function f and w ∈ {0,1}^n, the sensitivity of f at w is the number of Hamming neighbors w' of w with f(w) ≠ f(w'). The average sensitivity s(f) is the average, over all w ∈ {0,1}^n, of the sensitivity of f at w. Equivalently it is the sum of the influences of all variables on f (see [9]).

<a id="pdf-63759bd909d5-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.90 -->
**Lemma 11.** For any Boolean function f: s(f) = Σ_S |S| f̂(S)^2.

<a id="pdf-63759bd909d5-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.90 -->
In [9] this appears as 4 Σ_S |S| f̂(S)^2, because there Boolean functions map to {0,1}, whereas here the range is {1, −1}.

<a id="pdf-63759bd909d5-p011-b009"></a>
<!-- pdf-source: page=11; block=9; confidence=0.94 -->
**Lemma 12.** For any function f ∈ AC^0[d], s(f) = O((log n)^d) (via the Main Lemma). This bound is not far from optimal: the parity function on (log n)^{d−1} bits has sensitivity (log n)^{d−1} and is computable in AC^0[d].

<a id="pdf-63759bd909d5-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
The average-sensitivity lemma gives a general, simple way to prove lower bounds for AC^0 and has recent applications: [16] uses it to lower-bound the number of negations required by AC^0 circuits; [12] uses it to show universal hashing cannot be done in AC^0.

<a id="pdf-63759bd909d5-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.88 -->
**5.3 No Pseudorandom Function Generators.** A function f: {0,1}^{n_1} × {0,1}^{n_2} → {0,1} is a pseudorandom function generator if no polynomial-time oracle Turing machine M can distinguish a truly random oracle from the oracle f(s, ·) with s chosen at random. (Here the generator outputs one bit rather than a string; see [6] for exact definitions and constructions.)

<a id="pdf-63759bd909d5-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.95 -->
**Lemma 13.** There does not exist a pseudorandom function generator in AC^0.

<a id="pdf-63759bd909d5-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.85 -->
**Proof.** The distinguishing algorithm exploits the low average sensitivity of AC^0 functions. It chooses a random x, flips a random bit of x to obtain x', and queries the oracle. If f(x) = f(x') it guesses "AC^0 function"; otherwise it guesses "random function."

<a id="pdf-63759bd909d5-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.82 -->
**5.4 Correlation with t-wise Independent Probability Distributions.** A distribution μ on {0,1}^n is t-wise independent if for every x_{i_1},...,x_{i_t} and every ε_1,...,ε_t ∈ {0,1}, Pr(x_{i_1}=ε_1, ..., x_{i_t}=ε_t) = 2^{−t}. Observation: viewed as a real function on the cube, μ is t-wise independent iff its Fourier transform vanishes on all S with 1 ≤ |S| ≤ t. Such distributions are used to design pseudorandom generators for AC^0 [2,13]. Conjecture [11]: any polylog-wise independent distribution is a pseudorandom generator for AC^0; specifically, for f ∈ AC^0[d] and a (log^{d−1} n)-wise independent μ, |E(f) − E_μ(f)| ≤ 0.1, where E_μ(f) (resp. E(f) = E_U(f)) is the expectation of f under μ (resp. uniform). The result below is of similar flavor but falls short of the conjecture. For this section Boolean functions map into {0,1}.

<a id="pdf-63759bd909d5-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.70 -->
**Lemma 14.** Let f be a Boolean function computable by a circuit of depth d and size M, and let μ be a t-wise independent probability distribution. Then
$$\big|E_U(f) - E_\mu(f)\big| \le 2^n\,\|\mu\|\,\sqrt{2M}\;2^{-t^{1/d}/40}.$$

<a id="pdf-63759bd909d5-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.75 -->
**Proof.** Note E_μ(f) = 2^n (f, μ) = 2^n Σ_{S⊆{1,...,n}} f̂(S) μ̂(S), the last equality by orthonormality of the character basis. Since f maps to {0,1}, its expectation equals E_U(f) = f̂(∅), and ... (continues beyond the supplied pages).

<a id="pdf-63759bd909d5-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->
**Constant Depth Circuits, Fourier Transform, and Learnability** — page 619.

<a id="pdf-63759bd909d5-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.90 -->
**Proof (conclusion).** Since $f$ maps into $\{0,1\}$, $E_U(f)=\hat f(\emptyset)$ and $\hat\mu(\emptyset)=2^{-n}$. Also $\mu$ is $t$-wise independent, so $\hat\mu(S)=0$ for all $1\le|S|\le t$. By the Cauchy–Schwartz inequality,
$$\big|E_U(f)-E_\mu(f)\big| = 2^n\Big|\sum_{|S|>t}\hat f(S)\,\hat\mu(S)\Big| \le 2^n\sqrt{\sum_{|S|>t}\hat f(S)^2\;\sum_{|S|>t}\hat\mu(S)^2}.$$
An application of the Main Lemma completes the proof. ∎

<a id="pdf-63759bd909d5-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.70 -->
Remark: $\lVert\mu\rVert$ is central to the bound. Note $\lVert\mu\rVert_2^2$ equals the collision probability of the distribution (probability that two values drawn independently under $\mu$ coincide). For a nontrivial upper bound (less than one), $\lVert\mu\rVert$ must be exponentially small. E.g., if $K$ is polynomially bounded so that $\mu(x)<\mathrm{poly}(n)/2^n$ for every $x$, a meaningful bound follows; thus $\mu$ must be "fairly close" to the uniform distribution for the bound to be meaningful.

<a id="pdf-63759bd909d5-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
Acknowledgments thanking Mauricio Karchmer, Mike Sipser, Robert Sloan, Prasoon Tiwari, and the anonymous referees. (Non-mathematical.)

<a id="pdf-63759bd909d5-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.85 -->
Bibliography section begins (references 1–13: Ajtai; Ajtai–Wigderson; Brandman–Hennessy–Orlitsky; Dym–McKean; Furst–Saxe–Sipser; Goldreich–Goldwasser–Micali; Hagerup–Rüb; Håstad–Boppana; Kahn–Kalai–Linial; Kearns–Valiant; Linial–Nisan; Mansour–Nisan–Tiwari; Nisan–Wigderson). Bibliographic list, no mathematical content.

<a id="pdf-63759bd909d5-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.85 -->
Bibliography continued (references 14–20: Razborov; Rivest; Santha–Wilson; Smolensky; Valiant; Yao [two entries]). Publication footer: received December 1989, revised November 1991, accepted November 1991; *Journal of the ACM*, Vol. 40, No. 3, July 1993. Bibliographic/metadata content, no mathematics.
