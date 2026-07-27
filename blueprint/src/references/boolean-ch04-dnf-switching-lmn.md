<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: fc447f3269100012c1e1bf10316f1acd21c186aa8f8f6bedce44bf0bdca4b4f5 -->

<a id="pdf-fc447f326910-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Chapter 4. DNF formulas and small-depth circuits

<a id="pdf-fc447f326910-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.98 -->
This chapter investigates Boolean functions representable by small DNF formulas and constant-depth circuits, significant generalizations of decision trees. These classes have strong Fourier concentration properties.

<a id="pdf-fc447f326910-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
## 4.1. DNF formulas

<a id="pdf-fc447f326910-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.98 -->
**Definition 4.1.** A DNF (disjunctive normal form) formula over Boolean variables $x_1,\ldots,x_n$ is a logical OR of terms, each a logical AND of literals. A literal is either $x_i$ or its negation $\bar{x}_i$. No term contains both a variable and its negation. The number of literals in a term is its width. We identify a DNF formula with the Boolean function $f:\{0,1\}^n\to\{0,1\}$ that it computes.

<a id="pdf-fc447f326910-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.99 -->
**Example 4.2.** Recall the function $\operatorname{Sort}_3$, defined by $\operatorname{Sort}_3(x_1,x_2,x_3)=1$ if and only if $x_1\le x_2\le x_3$ or $x_1\ge x_2\ge x_3$. We can represent it by a DNF formula as follows:

$$\operatorname{Sort}_3(x_1,x_2,x_3)=(x_1\wedge x_2)\vee(\bar x_2\wedge\bar x_3)\vee(\bar x_1\wedge x_3)\vee(x_1\wedge\bar x_3).$$

<a id="pdf-fc447f326910-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
The DNF representation says that the bits are sorted if either the first two bits are $1$, the last two bits are $0$, the first bit is $0$ and the last bit is $1$, or the first bit is $1$ and the last bit is $0$.

<a id="pdf-fc447f326910-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.98 -->
**Definition 4.3.** The size of a DNF formula is its number of terms, and its width is the maximum width of its terms. For $f:\{0,1\}^n\to\{0,1\}$, write $\operatorname{DNFsize}(f)$ and $\operatorname{DNFwidth}(f)$ for the least size and width of a DNF computing $f$.

<a id="pdf-fc447f326910-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
The DNF for $\operatorname{Sort3}$ in Example 4.2 has size $3$ and width $2$. Every function $f:\{0,1\}^n\to\{0,1\}$ can be computed by a DNF of size at most $2^n$ and width at most $n$.

<a id="pdf-fc447f326910-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.99 -->
**Definition 4.4.** A CNF (conjunctive normal form) formula is a logical AND of clauses, each a logical OR of literals. Size and width are defined as for DNFs.

<a id="pdf-fc447f326910-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.96 -->
Some functions have more compact CNFs than DNFs. Switching ANDs and ORs in a CNF computing $f$ gives a DNF computing the dual function $f^\dagger$. Since $f$ and $f^\dagger$ have essentially the same Fourier expansion, the chapter focuses mainly on DNFs.

<a id="pdf-fc447f326910-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.99 -->
**Proposition 4.5.** Let $f:\{0,1\}^n\to\{0,1\}$ be computable by a decision tree $T$ of size $s$ and depth $k$. Then $f$ is computable by a DNF, and also a CNF, of size at most $s$ and width at most $k$.

<a id="pdf-fc447f326910-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.99 -->
**Proof.** For every path in $T$ from the root to a leaf labeled $1$, form the logical AND of the literals describing the path. These terms form the required DNF. For the CNF, take paths to leaves labeled $0$ and negate all literals describing each path. ∎

<a id="pdf-fc447f326910-p002-b008"></a>
<!-- pdf-source: page=2; block=8; confidence=0.99 -->
**Example 4.6.** If we perform this conversion on the decision tree computing $\operatorname{Sort}_3$ in Figure 3.1 we get the DNF

$$ (\bar x_1\wedge\bar x_3\wedge x_2)\vee(\bar x_1\wedge x_3)\vee(x_1\wedge\bar x_2\wedge\bar x_3)\vee(x_2\wedge x_3). $$

This has size $4$ (indeed at most the decision tree size $6$) and width $3$ (indeed at most the decision tree depth $3$). It is not as simple as the equivalent DNF from Example 4.2, though; DNF representation is not unique.

<a id="pdf-fc447f326910-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
## 4.1. DNF formulas

<a id="pdf-fc447f326910-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
The class of functions computable by small DNFs is intensively studied in learning theory. We begin by relating DNF width to total influence, using the $\{-1,1\}$ notation.

<a id="pdf-fc447f326910-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->
**Proposition 4.7.** Suppose $f:\{-1,1\}^n\to\{-1,1\}$ has $\operatorname{DNFwidth}(f)\le w$. Then $I[f]\le 2w$.

<a id="pdf-fc447f326910-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.99 -->
**Proof.** We use Exercise 2.10, which states that

$$I[f]=2\,\mathbb E_{x\sim\{-1,1\}^n}[\#\text{ $(-1)$-pivotal coordinates for $f$ on $x$}],$$

where coordinate $i$ is $(-1)$-pivotal on input $x$ if $f(x)=-1$ but $f(x^{\oplus i})=1$. It thus suffices to show that on every input $x$ there are at most $w$ coordinates which are $(-1)$-pivotal. To have any $(-1)$-pivotal coordinates at all on $x$ we must have $f(x)=-1$ (True); this means that at least one term $T$ in $f$'s width-$w$ DNF representation must be made True by $x$. But now if $i$ is a $(-1)$-pivotal coordinate then either $x_i$ or $\bar x_i$ must appear in $T$; otherwise, $T$ would still be made true by $x^{\oplus i}$. Thus the number of $(-1)$-pivotal coordinates on $x$ is at most the number of literals in $T$, which is at most $w$. Since $I[f^\dagger]=I[f]$ the proposition is also true for CNFs of width at most $w$.

<a id="pdf-fc447f326910-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.97 -->
The parity function $\chi_{[w]}$ shows the proposition is close to tight: $I[\chi_{[w]}]=w$ and $\operatorname{DNFwidth}(\chi_{[w]})\le w$. Exercise 4.17 improves the upper bound to the tight value $w$.

<a id="pdf-fc447f326910-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.96 -->
**Corollary 4.8.** If $f:\{-1,1\}^n\to\{-1,1\}$ has DNF width at most $w$, then for every $\varepsilon>0$ its Fourier spectrum is $\varepsilon$-concentrated on degrees at most $2w/\varepsilon$.

<a id="pdf-fc447f326910-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.97 -->
The dependence on $w$ is of the correct order, while the dependence on $\varepsilon$ will be improved in Section 4.4.

<a id="pdf-fc447f326910-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.98 -->
**Proposition 4.9.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be computable by a DNF (or CNF) of size $s$, and let $\varepsilon\in(0,1]$. Then $f$ is $\varepsilon$-close to a function $g$ computable by a DNF of width $\log(s/\varepsilon)$.

<a id="pdf-fc447f326910-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.98 -->
**Proof.** Delete all terms having more than $\log(s/\varepsilon)$ literals, and let $g$ be the resulting DNF. Each deleted term is true on a random input with probability at most $2^{-\log(s/\varepsilon)}=\varepsilon/s$. A union bound over at most $s$ deleted terms gives $\Pr[g(x)\ne f(x)]\le\varepsilon$. The CNF case is analogous. ∎

<a id="pdf-fc447f326910-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.96 -->
Combining Proposition 4.9 and Corollary 4.8 shows that size-$s$ DNFs have Fourier spectra $\varepsilon$-concentrated up to degree $O(\log(s/\varepsilon)/\varepsilon)$. Section 4.4 improves the dependence on $\varepsilon$. Section 4.3 will show that size-$s$ DNFs have total influence $O(\log s)$.

<a id="pdf-fc447f326910-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
**Mansour’s Conjecture.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be computable by a DNF of size $s>1$ and let $\varepsilon\in(0,1/2]$. Strong conjecture: $f$’s Fourier spectrum is $\varepsilon$-concentrated on a collection $\mathcal F$ with $|\mathcal F|\le s^{O(\log(1/\varepsilon))}$. Weaker conjecture: if $s\le\operatorname{poly}(n)$ and $\varepsilon>0$ is any fixed constant, then $|\mathcal F|\le\operatorname{poly}(n)$.

<a id="pdf-fc447f326910-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.99 -->
## 4.2. Tribes

<a id="pdf-fc447f326910-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.98 -->
Tribes DNFs are important examples and counterexamples in analysis of Boolean functions. For suitable parameters, the function is essentially unbiased while all individual influences are tiny.

<a id="pdf-fc447f326910-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.90 -->
Recall $\operatorname{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}$, defined by the width-$w$, size-$s$ DNF
$$\operatorname{Tribes}_{w,s}(x)=\bigvee_{j=1}^s\bigwedge_{i=1}^w x_{(j-1)w+i},$$
using the convention that $1$ is True and $-1$ is False.

<a id="pdf-fc447f326910-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.98 -->
**Fact 4.10.** $\Pr_x[\operatorname{Tribes}_{w,s}(x)=1]=1-(1-2^{-w})^s$.

<a id="pdf-fc447f326910-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.88 -->
**Definition 4.11.** For $w\in\mathbb N^+$, let $s$ be the largest integer such that $(1-2^{-w})^s\ge 1/2$. When $n=sw$, define $\operatorname{Tribes}_n:=\operatorname{Tribes}_{w,s}$. This is defined only for certain $n$.

<a id="pdf-fc447f326910-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->
**Proposition 4.12.** For the $\operatorname{Tribes}_n$ function as in Definition 4.11:

- $s=\ln(2)2^w-\Theta_w(1)$;
- $n=\ln(2)w2^w-\Theta(w)$, thus $n_{w+1}=(2+o(1))n_w$;
- $w=\log n-\log\log n+o_n(1)$, and $2^w=\dfrac{n}{\ln n}(1+o_n(1))$;
- $\Pr[\operatorname{Tribes}_n(x)=-1]=\dfrac12-O\!\left(\dfrac{\log n}{n}\right)$.

<a id="pdf-fc447f326910-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.97 -->
**Proposition 4.13.** For every $i\in[n]$, $\operatorname{Inf}_i[\operatorname{Tribes}_n]=(\ln n/n)(1\pm o(1))$, and therefore $I[\operatorname{Tribes}_n]=\ln n\,(1\pm o(1))$.

<a id="pdf-fc447f326910-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.91 -->
**Proof.** Viewing Tribes as a voting rule, voter $i$ is pivotal exactly when all other voters in $i$’s tribe vote True and all other tribes vote False. The probability is
$$2^{-(w-1)}(1-2^{-w})^{s-1}=\frac{2}{2^w}\Pr[\operatorname{Tribes}_n=1],$$
which, using Fact 4.10 and Proposition 4.12, equals $(\ln n/n)(1\pm o(1))$. ∎

<a id="pdf-fc447f326910-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
**Kahn–Kalai–Linial (KKL) Theorem.** For every $f:\{-1,1\}^n\to\{-1,1\}$,
$$\operatorname{MaxInf}[f]:=\max_{i\in[n]}\operatorname{Inf}_i[f]\ge \Omega\!\left(\frac{\log n}{n}\operatorname{Var}[f]\right).$$
The theorem is proved in Chapter 9.

<a id="pdf-fc447f326910-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.99 -->
**Proposition 4.14.** Suppose we index the Fourier coefficients of the function $\operatorname{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}$ by sets $T=(T_1,\ldots,T_s)\subseteq[sw]$, where $T_i$ is the intersection of $T$ with the $i$th “tribe.” Then

$$\widehat{\operatorname{Tribes}}_{w,s}(T)=\begin{cases}2(1-2^{-w})^s-1&\text{if }T=\varnothing,\\2(-1)^{k+|T|}2^{-kw}(1-2^{-w})^{s-k}&\text{if }k=\#\{i:T_i\ne\varnothing\}>0.\end{cases}$$

<a id="pdf-fc447f326910-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.99 -->
## 4.3. Random restrictions

<a id="pdf-fc447f326910-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.98 -->
Random restrictions are a Fourier-friendly method for simplifying Boolean functions. They will be used to prove that size-$s$ DNFs have total influence $O(\log s)$.

<a id="pdf-fc447f326910-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.97 -->
**Definition 4.15.** For $\delta\in[0,1]$, a subset $J\subseteq N$ is $\delta$-random if each element is included independently with probability $\delta$. A $\delta$-random restriction on $\{-1,1\}^n$ is $(J,z)$, where $J$ is $\delta$-random and $z\in\{-1,1\}^{[n]\setminus J}$ is uniformly random. Coordinates in $J$ are free; coordinates outside $J$ are fixed. Equivalently, each coordinate is free with probability $\delta$ and fixed to each sign with probability $(1-\delta)/2$.

<a id="pdf-fc447f326910-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.97 -->
**Definition 4.16.** Given $f:\{-1,1\}^n\to\{-1,1\}$ and a restriction $(J,z)$, identify the restricted function $f|_z^J:\{-1,1\}^J\to\{-1,1\}$ with its extension to $\{-1,1\}^n$ that ignores coordinates outside $J.

<a id="pdf-fc447f326910-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.93 -->
**Proposition 4.17.** Fix $f:\{-1,1\}^n\to\{-1,1\}$ and $S\subseteq[n]$. If $(J,z)$ is a $\delta$-random restriction, then
$$\mathbb E[\widehat{f|_z^J}(S)]=\delta^{|S|}\widehat f(S),$$
and
$$\mathbb E[\widehat{f|_z^J}(S)^2]=\sum_{U\supseteq S}\delta^{|U|}(1-\delta)^{|U\setminus S|}\widehat f(U)^2.$$

<a id="pdf-fc447f326910-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.91 -->
**Proof.** First condition on the free set $J$. Corollary 3.22 gives
$$\mathbb E_z[\widehat{f|_z^J}(S)]=\widehat f(S)\mathbf 1_{S\subseteq J},$$
$$\mathbb E_z[\widehat{f|_z^J}(S)^2]=\sum_{U\supseteq S}\widehat f(U)^2\mathbf 1_{U\subseteq J}\mathbf 1_{S\subseteq J}.$$
Taking expectation over $J$ yields the stated formulas. ∎

<a id="pdf-fc447f326910-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.98 -->
**Corollary 4.18.** If $(J,z)$ is a $\delta$-random restriction and $i\in[n]$, then
$$\mathbb E[\operatorname{Inf}_i[f|_z^J]]=\delta\operatorname{Inf}_i[f],$$
and hence $\mathbb E[I[f|_z^J]]=\delta I[f]$.

<a id="pdf-fc447f326910-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.93 -->
**Proof.** Expand the influence using Fourier coefficients and apply Proposition 4.17. The condition that $U\cap J$ contains $i$ contributes a factor $\delta$, and summing over $U$ gives $\delta\operatorname{Inf}_i[f]$. ∎

<a id="pdf-fc447f326910-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.96 -->
**Lemma 4.19.** Let $T$ be a DNF term over $\{-1,1\}^n$, let $w\in\mathbb N^+$, and let $(J,z)$ be a $(1/2)$-random restriction. Then
$$\Pr[\operatorname{width}(T|_z^J)\ge w]\le(3/4)^w,$$
assuming the original width is at least $w$.

<a id="pdf-fc447f326910-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.98 -->
**Proof.** If any literal in $T$ is fixed False, the restricted term is constantly False and has width $0$. Each literal is fixed False with probability $1/4$, so the probability that no one of $w$ literals is fixed False is at most $(3/4)^w$. ∎

<a id="pdf-fc447f326910-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.99 -->
**Theorem 4.20.** If $f:\{-1,1\}^n\to\{-1,1\}$ is computable by a DNF of size $s$, then $I[f]=O(\log s)$.

<a id="pdf-fc447f326910-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
**Proof.** Let $(J\mid z)$ be a $(1/2)$-random restriction on $\{-1,1\}^n$ and write $w=\operatorname{DNFwidth}(f_{J\mid z})$. By a union bound and Lemma 4.19 we have that $\Pr[w\ge w]\le s(3/4)^w$. Hence

$$\mathbb E[w]=\sum_{w=1}^{\infty}\Pr[w\ge w]\le 3\log s+\sum_{w>3\log s}s(3/4)^w\le 3\log s+4s(3/4)^{3\log s}\le 3\log s+4/s^{0.2}=O(\log s).$$

From Proposition 4.7 we obtain $\mathbb E[I[f_{J\mid z}]]\le2\cdot O(\log s)=O(\log s)$. And so from Corollary 4.18 we conclude $I[f]=2\mathbb E[I[f_{J\mid z}]]=O(\log s)$.

<a id="pdf-fc447f326910-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.99 -->
## 4.4. Håstad’s Switching Lemma and the spectrum of DNFs

<a id="pdf-fc447f326910-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.97 -->
A $\delta$-random restriction with $\delta\approx1/w$ usually trivializes each width-$w$ term: a literal is fixed False, or all literals are fixed True. The only nontrivial case leaves at least one literal free while all fixed literals are True.

<a id="pdf-fc447f326910-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.98 -->
**Baby Switching Lemma.** If $f:\{-1,1\}^n\to\{-1,1\}$ is computable by a DNF or CNF of width at most $w$, and $(J,z)$ is a $\delta$-random restriction, then
$$\Pr[f|_z^J\text{ is not constant}]\le5\delta w.$$

<a id="pdf-fc447f326910-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.98 -->
**Håstad’s Switching Lemma.** If $f$ is computable by a DNF or CNF of width at most $w$, and $(J,z)$ is a $\delta$-random restriction, then for every $k\in\mathbb N$,
$$\Pr[\operatorname{DT}(f|_z^J)\ge k]\le(5\delta w)^k.$$
The bound is independent of both the DNF size and $n$.

<a id="pdf-fc447f326910-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.98 -->
The Baby Switching Lemma is Exercise 4.19; Håstad’s lemma is proved in Håstad’s original paper or Razborov’s alternate proof.

<a id="pdf-fc447f326910-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.99 -->
**Lemma 4.21.** Let $f:\{-1,1\}^n\to\{-1,1\}$ and let $(J\mid z)$ be a $\delta$-random restriction, $\delta>0$. Fix $k\in\mathbb N^+$ and write $\varepsilon=\Pr[\operatorname{DT}(f_{J\mid z})\ge k]$. Then the Fourier spectrum of $f$ is $3\varepsilon$-concentrated on degree up to $3k/\delta$.

<a id="pdf-fc447f326910-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.88 -->
**Proof.** A depth-$k$ decision tree has no Fourier weight above degree $k$. Thus the expected Fourier weight of $f|_z^J$ above degree $k$ is at most $\varepsilon$. By Proposition 4.17, this equals
$$\sum_{U:|U|\ge k}\Pr[|U\cap J|\ge k]\widehat f(U)^2.$$
For $|U|\ge3k/\delta$, the random variable $|U\cap J|$ is binomial with mean at least $3k$, and a Chernoff bound gives $\Pr[|U\cap J|<k]\le2/3$. Hence the contribution from these $U$ is at most $3\varepsilon$. ∎

<a id="pdf-fc447f326910-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.98 -->
**Theorem 4.22.** If $f$ is computable by a DNF of width $w$, then its Fourier spectrum is $\varepsilon$-concentrated on degrees up to $O(w\log(1/\varepsilon))$.

<a id="pdf-fc447f326910-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.98 -->
**Proof.** Apply Håstad’s Switching Lemma and Lemma 4.21 with $\delta=1/(10w)$ and $k=C\log(1/\varepsilon)$ for sufficiently large constant $C$. ∎

<a id="pdf-fc447f326910-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
**Lemma 4.23.** Let $f:\{-1,1\}^n\to\{-1,1\}$ and let $(J\mid z)$ be a $\delta$-random restriction. Then

$$\sum_{U\subseteq[n]}\delta^{|U|}\lvert\widehat f(U)\rvert\le\mathbb E_{(J\mid z)}\left[2^{\operatorname{DT}(f_{J\mid z})}\right].$$

<a id="pdf-fc447f326910-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.98 -->
**Theorem 4.24.** If $f$ is computable by a DNF of width $w$, then for every $k$,
$$\sum_{|U|\le k}|\widehat f(U)|\le2(20w)^k.$$

<a id="pdf-fc447f326910-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.97 -->
**Proof.** Apply Håstad’s Switching Lemma with $\delta=1/(20w)$:
$$\mathbb E[2^{\operatorname{DT}(f|_z^J)}]\le\sum_{d\ge0}2^d(5/20)^d=2.$$
Lemma 4.23 then bounds the sum of Fourier coefficients by $2(20w)^k$. ∎

<a id="pdf-fc447f326910-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.98 -->
**Theorem 4.25.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be computable by a DNF of width $w$, and let $\varepsilon\in(0,1/2]$. Then its Fourier spectrum is $\varepsilon$-concentrated on a collection $\mathcal F$ satisfying
$$|\mathcal F|\le w^{O(w\log(1/\varepsilon))}.$$

<a id="pdf-fc447f326910-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.90 -->
**Proof.** Set $k=Cw\log(4/\varepsilon)$ and let $g$ be the truncation of $f$ to degree $k$. Theorem 4.22 gives $\|\widehat f-\widehat g\|_2^2\le\varepsilon^2/4$, while Theorem 4.24 implies that $g$ is concentrated on a collection of size at most $w^{O(w\log(1/\varepsilon))}$. Exercise 3.16 and Exercise 3.17 transfer this concentration to $f$. ∎

<a id="pdf-fc447f326910-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.99 -->
## 4.5. Highlight: LMN’s work on constant-depth circuits

<a id="pdf-fc447f326910-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.98 -->
The chapter extends the DNF/CNF Fourier results to constant-depth circuits, beginning with Håstad’s application of the Switching Lemma and then discussing Linial–Mansour–Nisan (LMN). Figure 4.1 gives an example of a depth-3 circuit.

<a id="pdf-fc447f326910-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
**Figure 4.1.** Example of a depth-$3$ circuit, with the layer-$0$ nodes at the bottom and the layer-$3$ node at the top. This circuit computes the function

$$x_1x_2\wedge(\bar x_1x_3\vee x_3x_4)\wedge(x_3x_4\vee\bar x_2).$$

<a id="pdf-fc447f326910-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.94 -->
**Definition 4.26.** For an integer $d\ge2$, a depth-$d$ circuit over Boolean variables $x_1,\ldots,x_n$ is a directed acyclic graph whose gates are arranged in $d+1$ layers, with wires directed from layer $j-1$ to layer $j$. Layer $0$ has exactly $2n$ input nodes labeled by the literals. Layer $d$ has one output node. Gates in odd layers use one connective ($\wedge$ or $\vee$), and gates in even layers use the other. Each gate computes the corresponding AND or OR of its inputs. DNFs and CNFs are depth-2 circuits.

<a id="pdf-fc447f326910-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.97 -->
**Definition 4.27.** The size of a depth-$d$ circuit is the number of nodes in layers $1$ through $d-1$. Its width is the maximum in-degree of any node at layer $1$. No layer-1 node is connected to a variable or its negation more than once.

<a id="pdf-fc447f326910-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.97 -->
The stipulated layering can be achieved with a factor-$2^d$ size overhead for an unbounded-fan-in AND/OR/NOT circuit.

<a id="pdf-fc447f326910-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.99 -->
**Lemma 4.28.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be computable by a depth-$d$ circuit of size $s$ and width $w$, and let $\varepsilon\in(0,1]$. Set

$$\delta=\frac1{10w}\left(\frac1{10\ell}\right)^{d-2},\qquad\text{where }\ell=\log(2s/\varepsilon).$$

Then if $(J\mid z)$ is a $\delta$-random restriction,

$$\Pr[\operatorname{DT}(f_{J\mid z})\ge\log(2/\varepsilon)]\le\varepsilon.$$

<a id="pdf-fc447f326910-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.86 -->
**Proof.** The case $d=2$ follows from Håstad’s Switching Lemma. For $d\ge3$, random restrictions compose. View the restriction as: first a $1/(10w)$-restriction, then $d-3$ successive $1/(10\ell)$-restrictions, followed by a final $1/(10\ell)$-restriction. After the first restriction, every layer-2 DNF switches to a decision tree, hence to a width-$\ell$ CNF, except with probability at most $s_2 2^{-\ell}$, where $s_2$ is the number of layer-2 nodes. Compress layers 2 and 3, reducing depth by one. Repeating gives a union-bound failure probability at most $s2^{-\ell}+s2^{-\ell}+\cdots\le\varepsilon/2$. The final restriction switches the remaining width-$\ell$ CNF to a decision tree of depth less than $\log(2/\varepsilon)$ except with probability at most $\varepsilon/2$. ∎

<a id="pdf-fc447f326910-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.96 -->
**Figure 4.2.** Under the restriction fixing $x_3=$ True, all three layer-2 DNFs may be replaced by CNFs of width at most $2$, after which layers 2 and 3 can be compressed. The exact figure is not present in the extracted text.

<a id="pdf-fc447f326910-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.87 -->
Assuming the first failure event does not occur, the initial restriction reduces the circuit to depth $d-1$ and width at most $\ell$; the number of nodes at the new layer 2 is at most the original number of layer-3 nodes. Each subsequent restriction similarly switches the current CNFs to DNFs and permits another compression. The displayed geometric/union-bound estimate is at most $\varepsilon/2$.

<a id="pdf-fc447f326910-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.98 -->
The final $1/(10\ell)$-random restriction reduces the circuit to a decision tree of depth less than $\log(2/\varepsilon)$, except with probability at most $\varepsilon/2$, completing the proof of Lemma 4.28. ∎

<a id="pdf-fc447f326910-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.99 -->
**LMN Theorem.** Let $f:\{-1,1\}^n\to\{-1,1\}$ be computable by a depth-$d$ circuit of size $s>1$ and let $\varepsilon\in(0,1/2]$. Then $f$’s Fourier spectrum is $\varepsilon$-concentrated up to degree

$$O\!\left(\log(s/\varepsilon)^{d-1}\,\log(1/\varepsilon)\right).$$

<a id="pdf-fc447f326910-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.84 -->
**Proof.** If the circuit also had width at most $w$, Lemma 4.28 combined with Lemma 4.21 would give $3\varepsilon$-concentration up to degree $O(w\log(2/\varepsilon))^d$. Delete all layer-1 nodes of width at least $\log(s/\varepsilon)$; as in Proposition 4.9, the resulting circuit computes a function $\varepsilon$-close to $f$. Applying Exercise 3.17 gives the stated degree bound after adjusting constants. ∎

<a id="pdf-fc447f326910-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.84 -->
**Remark 4.29.** Håstad [Hås01a] slightly sharpened the degree in the LMN Theorem to $O(\log(s/\varepsilon)^d\log(1/\varepsilon))$.

<a id="pdf-fc447f326910-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.96 -->
**Theorem 4.30.** If $f:\{-1,1\}^n\to\{-1,1\}$ is computable by a depth-$d$ circuit of size $s$, then $I[f]\le O(\log s)^{d-1}$.

<a id="pdf-fc447f326910-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.93 -->
**Theorem 4.31.** Let $\mathcal C$ be the class of functions $f:\{-1,1\}^n\to\{-1,1\}$ computable by depth-$d$, polynomial-size circuits. Then $\mathcal C$ can be learned from random examples with error $\varepsilon\ge1/\operatorname{poly}(n)$ in time $n^{O(\log n)^d}$. Thus $\mathrm{AC}^0$ is learnable in quasipolynomial time.

<a id="pdf-fc447f326910-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.98 -->
Håstad’s original motivation was proving that parity cannot be computed, or even approximately computed, by $\mathrm{AC}^0$. This follows from the LMN Theorem.

<a id="pdf-fc447f326910-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.91 -->
**Corollary 4.32.** Fix a constant $\varepsilon_0>0$. If a depth-$d$ circuit $C$ satisfies $\Pr_x[C(x)=\chi_{[n]}(x)]\ge1/2+\varepsilon_0$, then its size is at least $2^{\Omega(n^{1/(d-1)})}$.

<a id="pdf-fc447f326910-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.83 -->
**Proof.** The approximation hypothesis implies a nonzero Fourier correlation with parity. Applying the LMN Theorem with error parameter comparable to $\varepsilon_0$ forces degree at least $n$, yielding the stated size lower bound. ∎

<a id="pdf-fc447f326910-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.95 -->
The bound is close to tight: parity $\chi_{[n]}$ can be computed by a depth-$d$ circuit of size
$$O\!\left(n^{1/(d-1)}\right)\,2^{n^{1/(d-1)}}$$
for any $d\ge2$; see Exercise 4.12. Theorem 4.30 also gives lower bounds for majority: since $I[\operatorname{Maj}_n]=\Theta(\sqrt n)$, any constant-depth circuit computing $\operatorname{Maj}_n$ must have size at least $2^{n^{\Omega(1)}}$.

<a id="pdf-fc447f326910-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.88 -->
LMN also gave a cryptographic application. Informally, a function $f:\{-1,1\}^m\times\{-1,1\}^n\to\{-1,1\}$ is a pseudorandom function generator with seed length $m$ if efficient oracle algorithms cannot distinguish $f(s,\cdot)$ for random seed $s$ from a uniformly random function. Theorem 4.30 implies such generators cannot be computed by $\mathrm{AC}^0$ circuits: an algorithm querying $h(x)$ and $h(x\oplus e_i)$ accepts when the values differ, with acceptance probability $1/2$ for a random function and $I[h]/n$ in general.

<a id="pdf-fc447f326910-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
## 4.6. Exercises and notes

<a id="pdf-fc447f326910-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.86 -->
**Exercises 4.1–4.4.** Show that every Boolean function has a DNF of size at most $2^n$ and width at most $n$; prove the CNF/dual-DNF correspondence; characterize monotone DNFs; and prove the stated learning-related claim for size-$s$ DNFs.

<a id="pdf-fc447f326910-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.70 -->
Exercises 4.4–4.13 ask, respectively, for: a large Fourier coefficient of a size-$s$ DNF; verification of Propositions 4.12 and 4.14; properties and influence of Tribes; a direct proof of Corollary 4.18; sharpening Theorem 4.20; a proof of Lemma 4.23; parity DNF/CNF size and depth-$d$ circuits; the definition and analysis of De Morgan circuits; and related circuit-size questions.

<a id="pdf-fc447f326910-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.94 -->
Exercises continue with lower bounds for CNFs computing Tribes; distance from Tribes to juntas; consequences of KKL for transitive-symmetric functions; and the algorithmic proof that a width-$w$ CNF has total influence at most $w$. Exercise 4.18 defines random monotone terms and DNFs and asks for sensitivity bounds.

<a id="pdf-fc447f326910-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.91 -->
**Exercise 4.17 (statement).** For a CNF $C$ of width $w$, analyze the algorithm that processes a random permutation of variables, forces variables when unit clauses arise, and outputs a satisfying assignment. Show: (a) a non-aborting execution outputs a satisfying assignment; (b) for every satisfying $y$, the probability of producing $y$ is expressed through the expected number of forced variables; (c) $2^np(y)\ge1$; (d) if $y\oplus e_j$ does not satisfy $C$, then $\mathbb E_\pi[F_j(\pi,y)]\ge1/w$; and (e) deduce $I[f]\le w$.

<a id="pdf-fc447f326910-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.92 -->
**Exercise 4.18 (statement).** For a random monotone DNF of width $\sqrt n$ and size $2\sqrt n$, analyze the events that terms are false or have exactly one false literal, prove a constant-probability sensitivity lower bound $c\sqrt n$, and deduce a monotone function with sensitivity at least $c\sqrt n$ on a constant fraction of inputs. Compare this with majority, which also has average sensitivity $\Theta(\sqrt n)$.

<a id="pdf-fc447f326910-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.94 -->
**Exercise 4.19 (statement).** Prove the Baby Switching Lemma with constant $3$ in place of $5$. For a bad restriction, choose the first nonconstant term and its first surviving literal; associate an extending restriction that does not falsify that term. Show that no restriction is associated with more than $w$ bad restrictions and conclude $\Pr[\text{bad}]\le3\delta w$.

<a id="pdf-fc447f326910-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.99 -->
**Exercise 4.20 (statement).** Say that a $(d,w,s')$-circuit is a depth-$d$ circuit with width at most $w$ and with at most $s'$ nodes at layers $2$ through $d$ (i.e., excluding layers $0$ and $1$). (a) Show by induction on $d\ge2$ that any $f:\{-1,1\}^n\to\{-1,1\}$ computable by a $(d,w,s')$-circuit satisfies

$$I[f]\le w\,O(\log s')^{d-2}.$$

(b) Deduce Theorem 4.30.

<a id="pdf-fc447f326910-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.99 -->
## Notes

<a id="pdf-fc447f326910-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.98 -->
Mansour’s Conjecture dates from 1994. The weaker version would imply that the Kushilevitz–Mansour algorithm learns polynomial-size DNFs with constant error in polynomial time; Jackson later obtained this learning result by another method. Gopalan, Kalai, and Klivans showed that the conjecture would imply the analogous agnostic-learning result. Theorems 4.24 and 4.25 are due to Mansour.

<a id="pdf-fc447f326910-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.98 -->
Random restrictions date to Subbotovskaya. Håstad’s Switching Lemma and Lemma 4.28 build on work of Furst–Saxe–Sipser, Ajtai, and Yao. Linial, Mansour, and Nisan proved Lemma 4.21 and derived the LMN Theorem and its consequences. Further cryptographic applications appear in Goldmann–Russell. The strongest known lower bounds for approximate parity in $\mathrm{AC}^0$ are attributed to Impagliazzo–Matthews–Paturi and independently Håstad.

<a id="pdf-fc447f326910-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.98 -->
Theorem 4.20 and its generalization Theorem 4.30 are attributed to Boppana; LMN had the weaker $O(\log s)^d$ bound. Exercise 4.17 is due to Amano, and Exercise 4.18 to Talagrand.
