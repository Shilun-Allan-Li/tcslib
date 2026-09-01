<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 6bd33ae73ade77ad4a393e92243ca508478906f32de19880904153123c7e900d -->

<a id="pdf-6bd33ae73ade-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Combinatorial Bounds for List Decoding

Venkatesan Guruswami, Johan Håstad, Madhu Sudan, David Zuckerman.

<a id="pdf-6bd33ae73ade-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** A code is "nicely" list-decodable if every Hamming ball of large radius contains few codewords. Main positive result: there exist rate-$R$, block-length-$n$ codes with at most $c$ codewords in every Hamming ball of radius $H^{-1}(1-R-1/c)\cdot n$ (answering the main open question of Elias [8]). Consequence: for every $\varepsilon>0$, a polynomial-time constructible asymptotically good family of binary codes of rate $\Omega(\varepsilon^4)$ that is poly-time list decodable from a fraction $(1/2-\varepsilon)$ of errors using lists of size $O(\varepsilon^{-2})$. Main negative result: for every $\delta$ and $c$ there exist $\tau<\delta$, $c_1>0$, and an infinite family of linear codes $\{C_i\}$ with $C_i$ of block length $n_i$, minimum distance $\ge\delta\cdot n_i$, containing more than $c_1\cdot n_i^{\,c}$ codewords in some Hamming ball of radius $\tau\cdot n_i$ — the first bound separating the polynomial-list-decodability radius from the minimum distance.

<a id="pdf-6bd33ae73ade-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.92 -->
# I. Introduction

List decoding (Elias [7], Wozencraft [24]) lets the decoder output a list of codewords, succeeding if the correct message is in the list; early work analyzed average error probability at low rates and channel capacity (Shannon–Gallager–Berlekamp [17], Ahlswede [1]). Eighties work (Zyablov–Pinsker [25], Blinovsky [3],[4], Elias [8]) studied the adversarial/jammer setting, asking how many errors are recoverable with small lists, as a function of rate and minimum distance. Renewed interest follows efficient list-decoding algorithms [19],[12],[18],[13] that decode past half the minimum distance, prompting Høholdt–Justesen [16] to revisit combinatorial bounds. This paper studies linear codes with non-trivial list decoding: large rate that are nicely list-decodable, and large minimum distance that are not, and restates the concatenated-code consequence (rate $\Omega(\varepsilon^4)$, list-decodable from $(1/2-\varepsilon)$ errors, list size $O(\varepsilon^{-2})$).

<a id="pdf-6bd33ae73ade-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
# II. Definitions and Main Results

For prime power $q$, $\mathbb{F}_q$ is the field of cardinality $q$. An $[n,k]_q$ linear code $C$ is a $k$-dimensional subspace of $\mathbb{F}_2^n$; $n$ = blocklength, $k$ = dimension. The paper considers only binary ($q=2$) linear codes unless stated otherwise. For strings $x,y\in\Sigma^n$, $\Delta(x,y)$ is the Hamming distance (number of differing coordinates) and $\delta(x,y)=\Delta(x,y)/n$ the relative distance. Minimum distance $\mathrm{dist}(C)=\min_{x,y\in C,\,x\ne y}\Delta(x,y)$; relative distance $\delta(C)$ defined analogously.

<a id="pdf-6bd33ae73ade-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Definition (infinite family).** An infinite family of binary codes is $\mathcal{C}=\{C_i\mid i\in\mathbb{Z}^+\}$ with $C_i$ an $[n_i,k_i]_2$ code and $n_i>n_{i-1}$. Rate: $\mathrm{rate}(\mathcal{C})=\liminf_i\{k_i/n_i\}$. Relative distance: $\Delta(\mathcal{C})=\liminf_i\{\mathrm{dist}(C_i)/n_i\}$.

<a id="pdf-6bd33ae73ade-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.93 -->
For $x\in\mathbb{F}_2^n$, $B(x,r)=\{y\in\mathbb{F}_2^n\mid\Delta(x,y)\le r\}$. A code $C\subseteq\mathbb{F}_2^n$ is **$(e,\ell)$-list decodable** if $|B(x,e)\cap C|\le\ell$ for all $x\in\mathbb{F}_2^n$.

**Definition 1 (List Decoding Radius).** For an $[n,k]$ binary code $C$ and list size $\ell$, $\mathrm{radius}(C,\ell)$ is the maximum $e$ for which $C$ is $(e,\ell)$-list decodable.

**Definition 2 (radius for code and function families).** For an infinite family $\mathcal{C}$ and $\ell:\mathbb{Z}^+\to\mathbb{Z}^+$, $\mathrm{Rad}(\mathcal{C},\ell)=\liminf_i\{\mathrm{radius}(C_i,\ell(n_i))/n_i\}$. For a family $F$ of integer-valued functions, $\mathrm{Rad}(\mathcal{C},F)=\sup_{\ell\in F}\mathrm{Rad}(\mathcal{C},\ell)$.

<a id="pdf-6bd33ae73ade-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
The two broad questions: (1) do codes of large rate have large list decoding radius for fixed $\ell$? (2) do codes of large distance have small list decoding radius for given $\ell$? The other two combinations are uninteresting: small-rate codes can have small radius (code spanned by few standard basis vectors sits in a small ball around $0$), and small-distance codes can have large radius even for lists of size 2 (add one codeword close to an existing one in a large-distance code).

<a id="pdf-6bd33ae73ade-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
## A. List decoding radius vs. Rate

**Definition 3 (upper bound on radius).** For rate $0\le R\le1$ and $\ell:\mathbb{Z}^+\to\mathbb{Z}^+$, $U_\ell(R)=\sup_{\mathcal{C}\,:\,\mathrm{rate}(\mathcal{C})\ge R}\mathrm{Rad}(\mathcal{C},\ell)$. For a family $F$, $U_F(R)=\sup_{\ell\in F}U_\ell(R)$. ("Upper bound" = radius of the best code of at least rate $R$.)

**Definition 4.** $U_c^{\mathrm{const}}(R)=U_\ell(R)$ with $\ell(n)=c$. $U_c^{\mathrm{poly}}(R)=U_{F_c}(R)$ where $F_c=\{\ell_{c_1}:\ell_{c_1}(n)=c_1 n^c\}$. Also $U^{\mathrm{const}}(R)=\limsup_{c\to\infty}U_c^{\mathrm{const}}(R)$ and $U^{\mathrm{poly}}(R)=\limsup_{c\to\infty}U_c^{\mathrm{poly}}(R)$, the max relative radius for constant- and polynomial-size lists.

<a id="pdf-6bd33ae73ade-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.92 -->
**Result (Zyablov–Pinsker [25]).** $U^{\mathrm{const}}(R)=U^{\mathrm{poly}}(R)=H^{-1}(1-R)$, where $H$ is the binary entropy function $H(x)=-x\lg x-(1-x)\lg(1-x)$ ($\lg$ = base-2 log), and for $0\le y\le1$, $H^{-1}(y)$ is the unique $z\in[0,1/2]$ with $H(z)=y$. The behavior of $U_c^{\mathrm{const}}(R)$ for specific constants $c$ was not fully known; investigated in [25],[3],[4],[8],[23],[5].

<a id="pdf-6bd33ae73ade-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
$U_c^{\mathrm{const}}(R)$ is monotonic in $c$, hence always $\ge H^{-1}(1-R)/2$ (Gilbert–Varshamov bound). Zyablov–Pinsker [25] showed
$$U_c^{\mathrm{const}}(R)\ge H^{-1}\!\Big(1-\tfrac{1}{\lg(c+1)}-R\Big).\tag{1}$$
This implies $U^{\mathrm{const}}(R)=H^{-1}(1-R)$. The dependence on $c$ is weaker than hoped. Blinovsky [3],[4] studied small $c$ with lower bounds via non-linear codes; [5] extends to linear codes; Wei–Feng [23] also treat small $c$.

<a id="pdf-6bd33ae73ade-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
**Result (Elias [8]).** 
$$U_c^{\mathrm{const}}(R)\ge\frac{1}{2}\left(1-\sqrt{\,1-\frac{2(c-1)}{c}H^{-1}(1-R)\,}\right).\tag{2}$$

<a id="pdf-6bd33ae73ade-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
Bounds (1) and (2) are incomparable: (2) has better dependence on list size $c$ but weaker dependence on rate $R$ than (1). Motivating case: binary linear codes with list-of-$c$ radius $(1/2-\varepsilon)$. Bound (1) gives such codes of rate $\Omega(\varepsilon^2)$ (optimal) but list size $c=2^{O(\varepsilon^{-2})}$ (very large); bound (2) gives rate $\Omega(\varepsilon^4)$ with $c=O(1/\varepsilon^2)$. Theorem 5 combines optimal rate $\Omega(\varepsilon^2)$ with list size $O(1/\varepsilon^2)$, answering Elias's open question on improving the list-size dependence in (1).

<a id="pdf-6bd33ae73ade-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.96 -->
**Theorem 5.** For each fixed integer $c\ge1$ and rate $0<R<1$, $U_c^{\mathrm{const}}(R)\ge H^{-1}\!\big(1-R-\tfrac{1}{c}\big)$.

<a id="pdf-6bd33ae73ade-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.82 -->
### Upper bounds on $U_c^{\mathrm{const}}(R)$

All results above (including Theorem 5) are lower bounds on $U_c^{\mathrm{const}}$; the only simple upper bound is $U_c^{\mathrm{const}}(R)\le U^{\mathrm{poly}}(R)\le H^{-1}(1-R)$. Blinovsky [3] gave, for $c'=\lceil c/2\rceil$ and $\lambda=H^{-1}(1-R)$,
$$U_c^{\mathrm{const}}(R)\le\lambda-\binom{2c'}{c'}\,\frac{c'+2}{c'+1}\cdot\frac{(\lambda(1-\lambda))^{c'+1}}{(c'+2)-2(2c'+1)\lambda(1-\lambda)}.\tag{3}$$
This holds for non-linear codes too; the $c=2$ case was improved in [2].

<a id="pdf-6bd33ae73ade-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.95 -->
**Theorem 6 (follows from [3]).** For every $c\ge1$ and $0<R<1$, $U_c^{\mathrm{const}}(R)<H^{-1}(1-R)$.

<a id="pdf-6bd33ae73ade-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.85 -->
**Argument.** Bound (3) shows Theorem 5 has the right dependence on $c$. For a family with $\mathrm{Rad}(\mathcal{C},\ell)\ge1/2-\varepsilon$, $\ell(n)=c$: Theorem 5 gives rate $\Omega(\varepsilon^2)$ at $c=O(\varepsilon^{-2})$; conversely (3) forces $c=\Omega(\varepsilon^{-2})$ for $\mathrm{rate}(\mathcal{C})>0$. Requiring $\mathrm{Rad}(\mathcal{C},c)\ge1/2-\varepsilon$ gives $\lambda\ge1/2-\varepsilon$, so $\lambda(1-\lambda)\ge1/4-\varepsilon^2$; then the second term of (3) is at least $\Omega\!\big((1-4\varepsilon^2)^{c'+1}/(c'(2+4c'\varepsilon^2))\big)$ using Stirling's $\binom{2c'}{c'}=\Theta(4^{c'}/\sqrt{c'})$. Since this term must be $O(\varepsilon)$, it follows $c'=\Omega(\varepsilon^{-2})$. Thus the $1/c$ loss in Theorem 5 cannot be improved asymptotically (e.g. not to $1/c^{1+\gamma}$), even for general non-linear codes. A rate-vs-radius account appears in [10, Chap. 5].

<a id="pdf-6bd33ae73ade-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.30 -->
## B. List decoding radius vs. Distance

Lower bounds on the radius as a function of minimum distance: large minimum distance implies large radius via known combinatorial bounds (e.g. [9]); the goal is the smallest possible radius for a code of at least a given minimum distance.

**Definition 7 (lower bound on list decoding radius).** For distance $0\le\delta\le1$ and list size $\ell:\mathbb{Z}^+\to\mathbb{Z}^+$, [definition continues on the next page].

<a id="pdf-6bd33ae73ade-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.92 -->
**Definition (lower bound function).** For binary codes of relative distance δ, the list-of-ℓ decoding radius lower bound is $L_\ell(\delta)=\inf_{C:\,\Delta(C)\ge\delta}\mathrm{Rad}(C,\ell)$. As with the upper bound $U_\ell$, rate/distance arguments may be functions of n, taking the inf over codes with $\mathrm{dist}(C_i)\ge\delta(n_i)\cdot n_i$.

<a id="pdf-6bd33ae73ade-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
**Definition 8.** For $0\le\delta<1/2$ and constant c: $L^{const}_c(\delta)=L_\ell(\delta)$ with $\ell(n)=c$; $L^{poly}_c(\delta)=\sup_{c_1}L_{\ell_{c_1}}(\delta)$ with $\ell_{c_1}(n)=c_1 n^{c}$. Also $L^{const}(\delta)=\limsup_{c\to\infty}L^{const}_c(\delta)$ and $L^{poly}(\delta)=\limsup_{c\to\infty}L^{poly}_c(\delta)$.

<a id="pdf-6bd33ae73ade-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.92 -->
Restriction $\delta<1/2$ (codes with $\delta\ge1/2$ have at most linearly many codewords). Known: $L_1(\delta)=\delta/2$ and $L^{poly}(\delta)\le\delta$, so all lower bounds of interest lie in $[\delta/2,\delta]$; exact values mostly unknown.

<a id="pdf-6bd33ae73ade-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.97 -->
**Conjecture 9.** For every $0<\delta<1/2$, $L^{const}(\delta)=L^{poly}(\delta)=\tfrac12\bigl(1-\sqrt{1-2\delta}\bigr)$.

<a id="pdf-6bd33ae73ade-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.85 -->
Known: $L^{poly}(\delta)\ge L^{poly}_1(\delta)\ge\tfrac12(1-\sqrt{1-2\delta})$ and $L^{const}_c(\delta)\ge\tfrac12(1-\sqrt{1-2\delta+2\delta/c})$ (see [9],[14]). Upper bounds on $L^{poly},L^{const}$ less studied; Justesen–Høholdt [16] give MDS families of distance δ with $\mathrm{Rad}(C,c)\le(1-\sqrt{1-\delta})$ for constant c, but not over fixed/binary alphabets.

<a id="pdf-6bd33ae73ade-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.88 -->
$L^{poly}(\delta)$ is least understood; for δ near 1/2 ($\tfrac12-o(1)$) or near 0 there is some confirming evidence. Dumer et al. [6] construct, for any $\varepsilon>0$, linear codes with $\delta(n)=n^{\varepsilon-1}$ and $L^{poly}(\delta)\le\delta/(2-\varepsilon)$.

<a id="pdf-6bd33ae73ade-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.93 -->
**Theorem 10.** For every $\varepsilon>0$ there is an infinite family of binary codes $\mathcal C$ and a superpolynomial $\ell:\mathbb Z^+\to\mathbb Z^+$ such that every $C\in\mathcal C$ of block length n satisfies $\dfrac{n/2-\Delta(C)}{n/2-\mathrm{radius}(C,\ell(n))}\le 3\varepsilon$.

<a id="pdf-6bd33ae73ade-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.90 -->
Interpreted as: the tangent of $L^{poly}(\delta)$ has infinite slope as $\delta\to1/2$, consistent with Conjecture 9. For non-linear codes the conjecture is known true [9]. Before this paper it was unknown whether $L^{poly}_c(\delta)<\delta$.

<a id="pdf-6bd33ae73ade-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.96 -->
**Theorem 11.** For every integer $c\ge1$ and every δ with $0<\delta<1/2$, $L^{poly}_c(\delta)<\delta$.

<a id="pdf-6bd33ae73ade-p004-b010"></a>
<!-- pdf-source: page=4; block=10; confidence=0.88 -->
Informally: if $\delta(n)=\tfrac12(1-\Theta((\log n)^{\varepsilon-1}))$ then $L^{poly}(\delta)\le\tfrac12[1-(1-2\delta)^{1/2+\varepsilon}]$ for arbitrarily small ε (formalized below since $L^{poly}$ is a limit, not a function of n). Follows from Lemma 14 (Section III-C).

<a id="pdf-6bd33ae73ade-p004-b011"></a>
<!-- pdf-source: page=4; block=11; confidence=0.93 -->
**Theorem 12.** For every $\varepsilon\in(0,1/2)$, there exist $\delta:\mathbb Z^+\to\mathbb Z^+$ with $\delta(n)=\tfrac12(1-\Theta((\log n)^{\varepsilon-1}))$, a superpolynomial $\ell:\mathbb Z^+\to\mathbb Z^+$, and an infinite family $\mathcal C$ such that every $C\in\mathcal C$ of block length n has relative minimum distance $\ge\delta(n)$ and list-of-$\ell(n)$ decoding radius $\le\tfrac12[1-(1-2\delta)^{1/2+\varepsilon}]$.

<a id="pdf-6bd33ae73ade-p004-b012"></a>
<!-- pdf-source: page=4; block=12; confidence=0.94 -->
Guruswami [11] resolves Conjecture 9 assuming a well-known number-theoretic conjecture; discussed further in Section VI.

<a id="pdf-6bd33ae73ade-p004-b013"></a>
<!-- pdf-source: page=4; block=13; confidence=0.87 -->
**Remark.** For q-ary codes above the Gilbert–Varshamov bound, the expected number of codewords within Hamming distance d (the min distance) of a random received word is exponential, giving $L^{poly}(q,\delta)<\delta$ for certain δ. Such codes exist for square prime powers $q\ge49$ (algebraic-geometric codes [21]). Since GV is the best known binary rate–distance trade-off, this gives nothing for binary codes.

<a id="pdf-6bd33ae73ade-p004-b014"></a>
<!-- pdf-source: page=4; block=14; confidence=0.90 -->
**C. Organization of the Paper.** $L^{poly}(\delta),L^{poly}_c(\delta)$ studied in Section III (Theorems 10, 11, 12); $U^{const}_c(R)$ and Theorem 5 in Section IV; an adaptation of Theorem 5 (Lemma 22) in Section V, used to construct binary linear codes with high algorithmic list-decodability.

<a id="pdf-6bd33ae73ade-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**III. List Decoding Radius and Minimum Distance.** Proves upper bounds on $L^{poly}(\delta)$ from Theorems 11 and 12; Theorem 12 (case $\delta=\tfrac12(1-o(1))$) proved first, then modified for Theorem 11. Reviews discrete Fourier analysis.

<a id="pdf-6bd33ae73ade-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**A. Fourier analysis.** Booleans represented in $\{1,-1\}$ (1=FALSE, −1=TRUE), so XOR becomes multiplication; a length-m binary code is a subset of $\{1,-1\}^m$. Characters $\chi_\alpha(x)=(-1)^{\alpha\cdot x}$ for $\alpha\in\{0,1\}^t$ are the additive characters of $GF(2^t)$ (indexed by $\alpha\in GF(2^t)$); $\sum_\alpha\chi_\alpha(y)=2^t$ if $y=0$, else 0. Normalized inner product $\langle f,g\rangle=2^{-t}\sum_x f(x)g(x)$; the $\chi_\alpha$ are an orthonormal basis, so any $f:GF(2^t)\to\mathbb R$ (incl. Boolean f) expands as $f(x)=\sum_\alpha\hat f_\alpha\chi_\alpha(x)$ (4), with $\hat f_\alpha=\langle f,\chi_\alpha\rangle=2^{-t}\sum_x f(x)\chi_\alpha(x)$. With $\Delta(f,g)=\Pr_x[f(x)\ne g(x)]$, $\hat f_\alpha=1-2\Delta(f,\chi_\alpha)$. Plancherel: $\sum_\alpha\hat f_\alpha^2=1$.

<a id="pdf-6bd33ae73ade-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.94 -->
**Definition (Hadamard code).** For integer t, $\mathrm{Had}_t$ maps $x\in GF(2^t)$ (t bits) to $\langle\chi_\alpha(x)\rangle_{\alpha\in GF(2^t)}\in\{1,-1\}^{2^t}$.

<a id="pdf-6bd33ae73ade-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
**B. Construction idea.** Concatenate an outer extended Reed–Solomon code over $F=GF(2^t)$ with $\mathrm{Had}_t$ (length $2^t$, dim t): messages are degree-ℓ polynomials P over $GF(2^t)$, encoded as $\langle\mathrm{Had}_t(P(z_1)),\dots,\mathrm{Had}_t(P(z_{2^t}))\rangle$. With $n=2^t$: blocklength $2^{2t}$, minimum distance $\tfrac12(1-\ell/n)2^{2t}$; if $\ell=(1-2\delta)n$ the relative min distance is δ (code denoted $\text{RS-HAD}_t(\delta)$). Received word: pick a subset/subgroup $S\subseteq GF(2^t)$ and $f:GF(2^t)\to\{1,-1\}$ with large $\hat f_\alpha$ for $\alpha\in S$; let v = values of f, and use $v^{|F|}$ (v repeated |F| times) as the ball center. Codewords from polynomials P with $P(z_i)\in S$ for many i agree well with $v^{|F|}$; choosing S a multiplicative subgroup of suitable size yields many such polynomials/codewords.

<a id="pdf-6bd33ae73ade-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.95 -->
**Theorem 13.** There exist infinitely many integers s with: for infinitely many t there is a multiplicative subgroup $S\le GF(2^t)$ of size s such that for every $\beta\ne0$ in $GF(2^t)$ there is $f:GF(2^t)\to\{1,-1\}$ with $\sum_{\alpha\in\beta\cdot S}\hat f_\alpha\ge\sqrt{s/3}$, where $\beta\cdot S=\{\beta x:x\in S\}$.

<a id="pdf-6bd33ae73ade-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.93 -->
**Remarks.** (1) Such s are dense: for any integer $k\ge4$ there is s with $k\le s<3k$ satisfying Theorem 13. (2) One can additionally require infinitely many t including one with $s/2\le t\le s$.

<a id="pdf-6bd33ae73ade-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.90 -->
For any $S\subseteq GF(2^t)$, $\sum_{\alpha\in S}\hat f_\alpha\le|S|^{1/2}$ by Plancherel and Cauchy–Schwarz (continued next page).

<a id="pdf-6bd33ae73ade-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.90 -->
Theorem 13 shows the $\Omega(|S|^{1/2})$ sum is achievable infinitely often for appropriate multiplicative subgroups S, matching the upper bound.

<a id="pdf-6bd33ae73ade-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
**C. Proof of Theorem 12.** Theorem 13 is used to prove Theorem 12, which follows from Lemma 14.

<a id="pdf-6bd33ae73ade-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.93 -->
**Lemma 14.** For every $\varepsilon\in(0,1/2)$ there are infinitely many t such that, with $N=2^{2t}$, there exist $r\in\{1,-1\}^N$ and $\delta=\tfrac12(1-\Theta((\log N)^{\varepsilon-1}))$ for which the number of codewords C of $\text{RS-HAD}_t(\delta)$ with $\Delta(r,C)\le\tfrac N2\bigl(1-(1-2\delta)^{1/2+\varepsilon}\bigr)$ is at least $N^{\Omega(\log^\varepsilon N)}$.

<a id="pdf-6bd33ae73ade-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.86 -->
**Proof.** Take s,t from Theorem 13 with $t\le s\le2t$, S a subgroup of size s, and f with $\sum_{\alpha\in S}\hat f_\alpha\ge\sqrt{s/3}$ (5). Set $n=2^t$, $N=2^{2t}$, $p=(n-1)/s$; then $s=\Theta(\log N)$ and $S\cup\{0\}$ are exactly the p-th powers in $GF(2^t)$. Fix received word $r=v^n$ where $v=\langle f(x)\rangle_{x\in GF(2^t)}$. With $\ell=(1-2\delta)n$, $C=\text{RS-HAD}_t(\delta)$ concatenates an extended RS code of dimension $\ell+1=(1-2\delta)n+1$ over $GF(2^t)$ with $\mathrm{Had}_t$; blocklength N, min distance δN.

<a id="pdf-6bd33ae73ade-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.85 -->
Let $m=\lfloor\ell/p\rfloor$ and take message $P(x)=R(x)^p$ for random R of degree $\le m$. Its RS encoding $(b_1,\dots,b_n)$ has $b_i\in S\cup\{0\}$ with $\Pr[b_i=a]=p/n$ for $a\in S$, $\Pr[b_i=0]=1/n$, and the $b_i$ pairwise independent. By definition, $\mathrm{Had}_t(b_i)$ and v have unnormalized inner product $n\hat f_{b_i}$ (agreement fraction $(1+\hat f_{b_i})/2$).

<a id="pdf-6bd33ae73ade-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.93 -->
For each i, $\mathbb E[\hat f_{b_i}]=\tfrac pn\sum_{\alpha\in S}\hat f_\alpha+\tfrac1n\hat f_0\ge\tfrac{n-1}{ns}\sum_{\alpha\in S}\hat f_\alpha-\tfrac1n\ge\tfrac1s\sum_{\alpha\in S}\hat f_\alpha-\tfrac2n\ge\tfrac1{\sqrt{3s}}-\tfrac2n$ (6), using (5). Let X be the unnormalized inner product of the codeword (for message $R(x)^p$) with $r=v^n$. By linearity, $\mathbb E[X]=\sum_{i=1}^n\mathbb E[n\hat f_{b_i}]\ge \tfrac{N}{\sqrt{3s}}-2\sqrt N\ge\tfrac{1.1N}{\sqrt{4s}}$ (7) for large N. Also $\mathbb E[\hat f_{b_i}^2]\le\tfrac pn\sum_{\alpha\in S\cup\{0\}}\hat f_\alpha^2\le1/s$; by pairwise independence $\mathrm{Var}(X)\le\mathbb E[X^2]=\sum_{i=1}^n\mathbb E[(n\hat f_{b_i})^2]\le N^{3/2}/s$ (8).

<a id="pdf-6bd33ae73ade-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.95 -->
By Chebyshev, since $\mathbb E[X]\ge1.1N/\sqrt{4s}$: $\Pr[X\le N/\sqrt{4s}]\le\Pr[|X-\mathbb E X|\ge\tfrac{N}{10\sqrt{4s}}]\le\frac{400\,s\,\mathbb E[X^2]}{N^2}\le\frac{400}{\sqrt N}<\tfrac12$ for large N. Hence at least $\tfrac12 n^m$ of the messages $R(x)^p$ give codewords differing from r in at most $(\tfrac12-\tfrac1{2\sqrt{4s}})N$ positions.

<a id="pdf-6bd33ae73ade-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.82 -->
With $s=\Theta(\log N)$, choose $m=s^\varepsilon$: $(1-2\delta)=\ell/n=\Theta(\ell/(ps))=\Theta(m/s)=\Theta((\log N)^{\varepsilon-1})$, so $\delta=\tfrac12(1-\Theta((\log N)^{\varepsilon-1}))$. Also $(1-2\delta)^{1/2+\varepsilon}\simeq s^{(\varepsilon-1)(1/2+\varepsilon)}\le(4s)^{-1/2}$ for large N (since $\varepsilon<1/2$). Thus there are $\Omega(n^m)=N^{\Omega(\log^\varepsilon N)}$ codewords of $\text{RS-HAD}_t(\delta)$ [argument continues on next page].

<a id="pdf-6bd33ae73ade-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Proof (conclusion).** The codewords lie in a Hamming ball of radius $\frac{N}{2}\bigl(1-(1-2\delta)^{1/2+\varepsilon}\bigr)$. Theorem 13 supplies infinitely many admissible values of $t$, hence infinitely many blocklengths $N$ for the construction, completing the proof.

<a id="pdf-6bd33ae73ade-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.98 -->
**D. Proof of Theorem 11**

<a id="pdf-6bd33ae73ade-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.90 -->
Upper bounds on $L^{\mathrm{poly}}_c(\delta)$ for fixed constant $c$. Taking $m\approx 2c$ and $s\approx 2c/(1-2\delta)$ in the earlier proof yields roughly $L^{\mathrm{poly}}_c(\delta)\le \tfrac12\bigl(1-(\tfrac{1-2\delta}{6c})^{1/2}\bigr)$, which beats $\delta$ only for $\delta>\tfrac12-\tfrac{1}{12c}$. Hence the Lemma 14 construction is modified via Lemma 15 (bounds not optimized).

<a id="pdf-6bd33ae73ade-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.95 -->
**Lemma 15.** For every $c$ and every $\delta$,
$$L^{\mathrm{poly}}_c(\delta)\le \min_{0\le\alpha\le 1/2-\delta}\ (\delta+\alpha)\Bigl(1-\bigl(\tfrac{\alpha}{12(2c+1)}\bigr)^{1/2}\Bigr).$$

<a id="pdf-6bd33ae73ade-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.90 -->
**Proof.** Follows the Lemma 14 construction. Given $0<\delta<1/2$, $0\le\alpha\le 1/2-\delta$, $c$; set $\alpha'=2\alpha$ and pick integer $s$ with $2(2c+1)/\alpha'\le s<6(2c+1)/\alpha'$ meeting Theorem 13, and $t$ so a subgroup $S\le GF(2^t)$ exists (infinitely many such $t$). Set $n=2^t$, $N=n^2$, $p=(n-1)/s$; use code $\mathrm{RS\text{-}HAD}_t(\delta)$ (messages = polynomials over $GF(2^t)$ of degree $\le \ell=(1-2\delta)n$, blocklength $N$). Change: set the first $B=(\ell-\alpha'n)=(1-2\delta-\alpha')n$ blocks of received word $r$ to zero; the last $n-B$ blocks are vectors $v^{(i)}$. Let $m=2c+1$. Consider messages $P(x)=(x-z_1)\cdots(x-z_B)R(x)^p$ with $z_1,\dots,z_B$ the field elements of the first $B$ RS positions and $R$ a random degree-$m$ polynomial. Then $\deg(P)=B+pm=\ell-\alpha'n+\frac{n-1}{s}(2c+1)\le\ell$ (since $s\ge 2(2c+1)/\alpha'$). The codeword agrees with $r$ on the first $nB$ positions; on remaining blocks $b_i\in S_i\cup\{0\}$ with coset $S_i=\beta_i S$, $\beta_i=(z_i-z_1)\cdots(z_i-z_B)$. For $B<i\le n$, $v^{(i)}\in\{1,-1\}^{2^t}$ comes from $f^{(i)}:GF(2^t)\to\{1,-1\}$ with $\sum_{\alpha\in S_i}\hat f^{(i)}_\alpha\ge\sqrt{s/3}$ (Theorem 13). As in Lemma 14, with probability $\ge 1/2$ the codeword differs from $r$ in at most $E=(n-B)(\tfrac12-\tfrac{1}{4s})n$ positions, giving at least $\tfrac12 n^{m}$ codewords within radius $E$. Since $N=n^2$, $m=2c+1$, $s<6(2c+1)/\alpha'$, there are $\omega(N^c)$ codewords in a Hamming ball of radius $N(\delta+\alpha'/2)\bigl(1-\sqrt{\tfrac{\alpha'}{24(2c+1)}}\bigr)$; with $\alpha'=2\alpha$ this equals $N(\delta+\alpha)\bigl(1-\sqrt{\tfrac{\alpha}{12(2c+1)}}\bigr)$, proving the claim. Theorem 13 gives an infinite family of such codes.

<a id="pdf-6bd33ae73ade-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.90 -->
**Proof (of Theorem 11).** Goal: $L^{\mathrm{poly}}_c(\delta)<\delta$. If $\delta>\tfrac12-\tfrac{1}{48(2c+1)}$, take $\alpha=\tfrac12-\delta$ in Lemma 15: $L^{\mathrm{poly}}_c(\delta)\le\tfrac12\bigl(1-(\tfrac{1-2\delta}{24(2c+1)})^{1/2}\bigr)<\delta$. If $\delta\le\tfrac12-\tfrac{1}{48(2c+1)}$, take $\alpha=\delta^2/(48(2c+1))$ (valid, $<\tfrac12-\delta$): $L^{\mathrm{poly}}_c(\delta)\le\delta+\alpha-\delta(\tfrac{\alpha}{12(2c+1)})^{1/2}<\delta$. Thus $L^{\mathrm{poly}}_c(\delta)<\delta$ in both cases.

<a id="pdf-6bd33ae73ade-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.98 -->
**E. Proof of Theorem 13**

<a id="pdf-6bd33ae73ade-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.95 -->
**Lemma 16.** For any integer $t$, let $S\subseteq GF(2^t)$ be a subset such that no four distinct elements of $S$ sum to $0$. Then there exists $f:GF(2^t)\to\{1,-1\}$ with $\sum_{\alpha\in S}\hat f_\alpha\ge\sqrt{|S|/3}$.

<a id="pdf-6bd33ae73ade-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.90 -->
**Proof.** *Claim:* Define $g(x)=\sum_{\alpha\in S}\chi_\alpha(x)$. The maximum of $\sum_{\alpha\in S}\hat f_\alpha$ over boolean $f$ equals $2^{-t}\sum_x|g(x)|$. *Proof of claim:* $\sum_{\alpha\in S}\hat f_\alpha=2^{-t}\sum_{x,\alpha\in S}f(x)\chi_\alpha(x)=2^{-t}\sum_x f(x)g(x)\le 2^{-t}\sum_x|g(x)|$ (continues on next page).

<a id="pdf-6bd33ae73ade-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.90 -->
**Proof (continued).** Equality holds for $f(x)=\mathrm{sign}(g(x))$, so it suffices to lower-bound $\sum_x|g(x)|$. By Hölder's inequality $\sum_x|h_1 h_2|\le(\sum_x|h_1|^p)^{1/p}(\sum_x|h_2|^q)^{1/q}$ with $1/p+1/q=1$, taking $h_1=|g|^{2/3}$, $h_2=|g|^{4/3}$, $p=3/2$, $q=3$:
$$\Bigl(\sum_x|g(x)|\Bigr)^{2/3}\Bigl(\sum_x g(x)^4\Bigr)^{1/3}\ge\sum_x g^2(x).\quad(9)$$
(Also from log-convexity of power means; HLP Thm 18.) Now $\sum_x g^2(x)=\sum_{\alpha_1,\alpha_2}\sum_x\chi_{\alpha_1+\alpha_2}(x)=|S|\cdot 2^t$ (via Plancherel). Similarly $\sum_x g^4(x)=\sum_{\alpha_1,\dots,\alpha_4\in S}\sum_x\chi_{\alpha_1+\alpha_2+\alpha_3+\alpha_4}(x)=N_{4,S}\cdot 2^t$, where $N_{4,S}$ counts $4$-tuples summing to $0$. Since no four distinct elements sum to $0$, only tuples with two equal $\alpha$'s contribute, of which there are $\le 3|S|^2$, so $N_{4,S}\le 3|S|^2$ and $\sum_x g^4(x)\le 3|S|^2 2^t$. Plugging into (9) with $f=\mathrm{sign}(g)$: $\sum_{\alpha\in S}\hat f_\alpha=2^{-t}\sum_x|g(x)|\ge\sqrt{|S|^3/(3|S|^2)}=\sqrt{|S|/3}$.

<a id="pdf-6bd33ae73ade-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.92 -->
**Definitions (cyclic codes).** A binary cyclic code of blocklength $n$ is an ideal in $R=\mathbb{F}_2[X]/(X^n-1)$, characterized by a generator polynomial $g(X)\mid(X^n-1)$; codewords are the multiples of $g(X)$. The code is *maximal* if $g(X)$ is irreducible over $GF(2)$. A *BCH code* has generator equal to the minimal polynomial with roots $\beta,\beta^2,\dots,\beta^{d-1}$, where $\beta$ is a primitive $n$th root of unity over $GF(2)$ and $d$ is the designed distance.

<a id="pdf-6bd33ae73ade-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.92 -->
**Lemma 17.** For any integer $k\ge4$, there exists an integer $s\in[k,3k)$ such that a maximal binary BCH code of blocklength $s$ and minimum distance $\ge5$ exists.

**Proof.** Choose $s=2^f-3$ in $[k,3k)$. Let $\beta$ be a primitive $s$th root of unity over $GF(2)$ and $h$ its minimal polynomial. Then $h(\beta^{2^i})=0$ for all $i\ge1$, so $h(\beta^2)=h(\beta^4)=0$; and $\beta^{2^f}=\beta^3$ gives $h(\beta^3)=0$. The cyclic code $C_h$ generated by $h$ is maximal ($h$ irreducible), and $h(\beta^i)=0$ for $i=1,2,3,4$, so by the BCH bound its minimum distance is $\ge5$.

<a id="pdf-6bd33ae73ade-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Lemma 18.** For any integer $k\ge4$, there exists $s\in[k,3k)$ such that: for infinitely many integers $t$, including one with $s/2\le t\le s$, there is a multiplicative subgroup $S\le GF(2^t)$ of size $s$ with no four or fewer distinct elements summing to $0$; moreover this holds for every coset $\beta S$, $\beta\ne0$.

**Proof.** Take $k\le s<3k$ with a BCH code $C$ from Lemma 17, generated by irreducible $h\mid(x^s-1)$. Let $t=\deg(h)\le s$; then $F=\mathbb{F}_2[X]/(h(X))\cong GF(2^t)$, and $S=\{1,X,X^2,\dots,X^{s-1}\}$ is a size-$s$ subgroup. Distance $\ge5$ implies $\sum_{i\in G}X^i$ is not divisible by $h(X)$ for any $G$ with $|G|\le4$, so no four or fewer distinct elements of $S$ sum to $0$ in $F$. Any multiple of $t$ also works ($S$ is a subgroup of $GF(2^{kt})$ too), so double $t$ until $s/2\le t\le s$. Coset claim: $a_1+a_2+a_3+a_4=0$ with $a_i\in\beta S$ gives $\beta^{-1}a_i\in S$ summing to $0$, a contradiction. (All ingredients for Theorem 13 now assembled.)

<a id="pdf-6bd33ae73ade-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.93 -->
**Proof (of Theorem 13).** Immediate from Lemma 16 and Lemma 18; Lemma 18 also yields the remarks following the statement of Theorem 13.

<a id="pdf-6bd33ae73ade-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.98 -->
**F. Proof of Theorem 10**

<a id="pdf-6bd33ae73ade-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.92 -->
**Lemma 19.** (Recall an MDS $[n,k]$ code has minimum distance $n-k+1$.) For any MDS $[n,k]_q$ code $C$ and $a\ge k$,
$$\tfrac1e\binom{n}{a}q^{k-a}\le \mathbb{E}_x\bigl[|B(x,n-a)\cap C|\bigr]\le\binom{n}{a}q^{k-a}.$$

**Proof.** *Upper bound:* for any set $S_a$ of $a$ positions, the expected number of codewords agreeing with $x$ on $S_a$ is $\le q^{k-a}$; fixing $S_k\subseteq S_a$ of $k$ positions, each $x$ has a unique codeword $w_x$ agreeing on $S_k$, and $\Pr[w_x\text{ agrees on }S_a]=q^{k-a}$. *Lower bound:* the probability a codeword agrees with $x$ on $S_a$ and disagrees outside equals $q^{k-a}(1-1/q)^{n-a}$; for an MDS code $n<q+k-1$, so $n-a\le n-k<q-1$ and $(1-1/q)^{n-a}>1/e$.

<a id="pdf-6bd33ae73ade-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->
**Corollary 20.** For any constants $\varepsilon,\gamma>0$ and large enough $n$, $L^{\mathrm{poly}}_n(1-n^{\varepsilon-1})\le 1-(1-\gamma)n^{\varepsilon-1}/\varepsilon$, where $L^{\mathrm{poly}}_q$ denotes the analog of $L^{\mathrm{poly}}$ for $q$-ary codes.

**Proof.** Use an MDS $[n,k]_q$ code with $n=q$, $k=n^\varepsilon$ (e.g. Reed-Solomon). Then $\binom{n}{a}q^{k-a}\ge(n/a)^a n^{k-a}=n^k/a^a$. Setting $a=(1-\gamma)n^\varepsilon/\varepsilon$, for large $n$ one has $a^a\le n^{(1-\gamma/2)n^\varepsilon}$, so the expected number of codewords in a ball of radius $n-a$ is $\Omega(n^{(\gamma/2)n^\varepsilon})$, giving the corollary.

<a id="pdf-6bd33ae73ade-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.96 -->
**Proof (of Theorem 10).** Construct a family of codes $\mathcal{C}$ such that every $C\in\mathcal{C}$ of block length $n$ satisfies: (1) relative minimum distance $\ge\tfrac12(1-n^{\varepsilon-1/2})$; (2) list-of-$\ell(n)$ decoding radius $\le\tfrac12\bigl(1-\tfrac{1}{3\varepsilon}n^{\varepsilon-1/2}\bigr)$. This suffices. The codes are concatenations of Reed-Solomon with Hadamard codes; for block length $n$ the RS code has block length $\sqrt{n}$, and the relative minimum distance of $C$ is half that of the RS code. The result then follows from Corollary 20 for $\ell(n)$ growing exponentially in $n$.

<a id="pdf-6bd33ae73ade-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.98 -->
**IV. LIST DECODING RADIUS VS. RATE**

<a id="pdf-6bd33ae73ade-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.80 -->
**Proof (of Theorem 5).** For each fixed integer $c\ge1$ and $0<p<1/2$, use the probabilistic method to obtain a binary linear code $C$ of blocklength $n$ with at most $c$ codewords in any ball of radius $e=pn$, and dimension $k=\lfloor(1-H(p)-1/c)n\rfloor$, for all large $n$; this gives the claimed lower bound on $U^{\mathrm{const}}_c$. Build $C=C_k$ iteratively: $C_0=\{0^n\}$; for $1\le i\le k$ pick a random nonzero $b_i$ linearly independent of $b_1,\dots,b_{i-1}$ and set $C_i=\mathrm{span}(b_1,\dots,b_i)$, so $C=C_k$ is an $[n,k]_2$ code; goal: list-of-$c$ decoding radius $\ge e$. Potential function:
$$S_C=\frac{1}{2^n}\sum_{x\in\{0,1\}^n}2^{\,\frac{n}{c}\,|B(x,e)\cap C|}.\quad(10)$$
Write $S_i=S_{C_i}$ and $T^i_x=|B(x,e)\cap C_i|$, so $S_i=2^{-n}\sum_x 2^{nT^i_x/c}$. With $B=|B(0,e)|=|B(0,pn)|\le 2^{H(p)n}$,
$$S_0=1-B/2^n+B\,2^{n/c}/2^n\le 1+2^{n(H(p)-1+1/c)}.\quad(11)$$
Given $C_i$ with $S_i=\hat S_i$, over random $b_{i+1}$ from outside $\mathrm{span}(b_1,\dots,b_i)$:
$$\mathbb{E}[S_{i+1}]=2^{-n}\sum_x 2^{nT^i_x/c}\,\mathbb{E}_{b_{i+1}}\!\bigl[2^{nT^i_{x+b_{i+1}}/c}\bigr],\quad(12)$$
using that $z\in B(x,e)\cap C_{i+1}$ implies $z\in B(x,e)\cap C_i$ or $z+b_{i+1}\in B(x,e)\cap C_i$. Unrestricted, (12) equals $\hat S_i^2$ (independence of $x$, $x+b_{i+1}$). Since expectation over $b_{i+1}$ outside the span is at most $(1-2^{i-n})^{-1}$ times that over uniform $b_{i+1}$,
$$\mathbb{E}[S_{i+1}]\le\frac{\hat S_i^2}{1-2^{i-n}}.\quad(13)$$

<a id="pdf-6bd33ae73ade-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
**Proof (continued).** Applying (13) for $i=0,\dots,k-1$ yields an $[n,k]$ binary linear code $C$ with $S_C=S_k \le \frac{S_0^{2^k}}{\prod_{i=0}^{k-1}(1-2^{i-n})^{2^{k-i}}} \le \frac{S_0^{2^k}}{(1-2^{k-n})^k} \le \frac{S_0^{2^k}}{1-k2^{k-n}}$ (14), using $(1-x)^a\ge 1-ax$ for $x,a\ge0$. Combining (14) with (11): $S_k \le (1-k2^{k-n})^{-1}\bigl(1+2^{n(H(R)-1+1/c)}\bigr)^{2^k}$, and using $(1+x)^a\le 1+2ax$ for $ax\ll1$: $S_k \le 2(1+2\cdot 2^{k+(H(p)-1+1/c)n}) \le 6$ (15), since $k=\lfloor(1-H(p)-1/c)n\rfloor$. By definition (10) of $S_k$, this gives $2^{(n/c)\cdot|B(x,e)\cap C|}\le 6\cdot 2^n < 2^{n+3}$, i.e. $|B(x,e)\cap C|\le(1+\tfrac3n)c$ for all $x\in\{0,1\}^n$. If $n>3c$ then $|B(x,e)\cap C|<c+1$, so the list-of-$c$ decoding radius of $C$ is at least $e$.

<a id="pdf-6bd33ae73ade-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->
**Remark.** Theorem 5 can additionally guarantee relative minimum distance $\Delta(R)\ge H^{-1}(1-R-1/c)$ by conditioning the random basis choice $b_{i+1}$ so that $\mathrm{span}(b_1,\dots,b_{i+1})$ contains no vector of weight $<pn$. Then (13) becomes $E[S_{i+1}]\le \dfrac{\hat S_i^2}{1-2^{i+H(p)n-n}}$, yielding a code $C$ of dimension $k=\lfloor(1-H(p)-1/c)n\rfloor$ and minimum distance $\ge pn$ with $S_C=O(1)$.

<a id="pdf-6bd33ae73ade-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.85 -->
**V. Application to Highly List Decodable Codes.** Applies the previous section's technique to construct concatenated codes list decodable from very high noise with good rate. Setting (as in [13]): given $\varepsilon>0$, seek asymptotically good binary linear families $C_\varepsilon$ efficiently list decodable up to a fraction $(1/2-\varepsilon)$ of errors, with explicit polynomial-time constructions of reasonable rate. Prior best [13]: rate $\Omega(\varepsilon^6)$ (AG code concatenated with a high-distance inner code like Hadamard). Non-constructively, Theorem 5 gives rate $\Omega(\varepsilon^2)$, asymptotically optimal. Using Theorem 5 codes as inner codes with an outer Reed–Solomon code recovers rate $\Omega(\varepsilon^6)$ without AG codes; an adaptation of Theorem 5 tailored to the weighted RS list-decoding algorithm of [12] instead achieves rate $\Omega(\varepsilon^4)$, the main result of the section.

<a id="pdf-6bd33ae73ade-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.83 -->
**Theorem 21.** There exist absolute constants $b,d>0$ such that for each fixed $\varepsilon>0$ there is a polynomial-time constructible code family $C$ with: (1) $\mathrm{rate}(C)\ge \varepsilon^4/b$; (2) $\mathrm{Rad}(C,\,d\varepsilon^{-2})\ge \tfrac12-\varepsilon$ (list decodable with list size $d\varepsilon^{-2}$ up to radius $\tfrac12-\varepsilon$); (3) $\Delta(C)\ge \tfrac12-\varepsilon$; (4) a polynomial-time list decoding algorithm for $C$ correcting a fraction $(1/2-\varepsilon)$ of errors. Follows from Theorem 24 (Section V-B).

<a id="pdf-6bd33ae73ade-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.90 -->
**V-A. An "inner code" construction; 1) Existence of a good code.** Proves existence of codes serving as inner codes in the later concatenation, via an adaptation of the Theorem 5 proof, and shows such a code is constructible in $2^{O(n)}$ time ($n$ = blocklength) by an iterative greedy procedure.

<a id="pdf-6bd33ae73ade-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.92 -->
**Lemma 22.** There exist absolute constants $\sigma,A>0$ such that for any $\varepsilon>0$ there is a binary linear code family $C$ with: (1) $\mathrm{rate}(C)=\sigma\varepsilon^2$; (2) for every $C\in\mathcal{C}$ and every $x\in\{0,1\}^n$ ($n$ = blocklength), $\displaystyle\sum_{\substack{c\in C\\ \delta(x,c)\le 1/2-\varepsilon}}\bigl(1-2\delta(x,c)\bigr)^2 \le A$ (16).

<a id="pdf-6bd33ae73ade-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.90 -->
**Proof.** For all large $n$, prove existence of a binary linear code $C_k$ of blocklength $n$ and dimension $k\ge\sigma\varepsilon^2 n$ satisfying (16) for every $x$. Follows the Theorem 5 proof: build $C_k$ iteratively over $k$ steps by randomly picking basis vectors $b_1,\dots,b_k$; set $C_i=\mathrm{span}(b_1,\dots,b_i)$, $0\le i\le k$. Key tool: a potential function $W_C$ defined for a blocklength-$n$ code $C$ (analogue of potential (10)).

<a id="pdf-6bd33ae73ade-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Proof (continued).** Define $W_C = 2^{-n}\sum_{x\in\{0,1\}^n} 2^{\frac{n}{A}\sum_{c\in C:\,\delta(x,c)\le 1/2-\varepsilon}(1-2\delta(x,c))^2}$ (17), with $A$ fixed later, $A>\ln 4$. Write $W_i=W_{C_i}$, and $R_i^x=\sum_{c\in C_i,\,\delta(x,c)\le 1/2-\varepsilon}(1-2\delta(x,c))^2$ (18), so $W_i=2^{-n}\sum_x 2^{\frac nA R_i^x}$. As in Theorem 5, $R_{i+1}^x=R_i^x+R_i^{x+b_{i+1}}$, giving $E_{b_{i+1}}[W_{i+1}\mid W_i=\hat W_i]=\hat W_i^2$ over uniform $b_{i+1}\in\{0,1\}^n$, and over a random $b_{i+1}$ outside $\mathrm{span}(b_1,\dots,b_i)$: $E[W_{i+1}\mid W_i=\hat W_i]\le \dfrac{\hat W_i^2}{1-2^{i-n}}$ (19).

<a id="pdf-6bd33ae73ade-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.90 -->
**Proof (continued).** Applying (19) for $i=0,\dots,k-1$ gives an $[n,k]$ code $C=C_k$ with $W_C=W_k\le \dfrac{W_0^{2^k}}{1-k2^{k-n}}$ (20). If $W_C=O(1)$ then by (17) $R_k^x\le A$ for every $x$, so $C$ satisfies (16). It remains to upper-bound $W_0$.

<a id="pdf-6bd33ae73ade-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.90 -->
**Proof (continued).** Set $a=(1/2-\varepsilon)n$. Since $C_0=\{0\}$, $R_0^x=(1-2\,\mathrm{wt}(x)/n)^2$ if $\mathrm{wt}(x)\le a$, else $0$ (with $\mathrm{wt}(x)=\Delta(x,0)$). Writing $\exp_2(x)=2^x$: $W_0=2^{-n}\sum_x \exp_2(\tfrac nA R_0^x) \le 1+2^{-n}\sum_{i=0}^{a}\binom{n}{i}\exp_2\!\bigl(\tfrac nA(1-\tfrac{2i}{n})^2\bigr) \le 1+n2^{-n}\exp_2\!\bigl(\max_{0\le i\le a}\{H(\tfrac in)n+\tfrac{4n}{A}(\tfrac12-\tfrac in)^2\}\bigr) \le 1+n2^{un}$ (21), where $u \overset{\mathrm{def}}{=} \max_{0\le y\le 1/2-\varepsilon}\{H(y)-1+\tfrac4A(\tfrac12-y)^2\}$.

<a id="pdf-6bd33ae73ade-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.92 -->
**Proof (continued).** Claim: for $0\le y\le 1/2$, $H(y)\le 1-\tfrac{2}{\ln 2}(\tfrac12-y)^2$. Proof by Taylor expansion of $H$ around $1/2$: $H'(1/2)=0$, $H''(1/2)=-4/\ln 2$, all odd derivatives at $1/2$ vanish and even derivatives are nonpositive, so $H(y)\le H(1/2)-\tfrac{H''(1/2)}{2}(1/2-y)^2 = 1-\tfrac{2}{\ln 2}(\tfrac12-y)^2$.

<a id="pdf-6bd33ae73ade-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.85 -->
**Proof (continued).** Hence $u \le \max_{0\le y\le 1/2-\varepsilon}\bigl(\tfrac4A-\tfrac2{\ln 2}\bigr)(\tfrac12-y)^2 = -4\bigl(\tfrac1{\ln 4}-\tfrac1A\bigr)\varepsilon^2$ (22), since $A>\ln 4$. Combining (20),(21),(22): $W_C=W_k=O(1)$ provided $k<-un$, i.e. $k<4(\tfrac1{\ln 4}-\tfrac1A)\varepsilon^2 n$. The lemma holds e.g. with $A=2$ and $\sigma=0.85$. $\square$

<a id="pdf-6bd33ae73ade-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.92 -->
**Remark.** As in the remark after Theorem 5, one can also require $\Delta(C)\ge 1/2-\varepsilon$ by picking $b_{i+1}$ randomly among choices with $\mathrm{span}(b_1,\dots,b_{i+1})\cap B(0,(\tfrac12-\varepsilon)n)=\emptyset$.

<a id="pdf-6bd33ae73ade-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.90 -->
**V-A.2) Algorithm GREEDY-INNER.** Parameters: dimension $k$; $\varepsilon,A>0$ (absolute constant from Lemma 22). Output: binary linear code $C=\mathrm{GREEDY}(k,\varepsilon)$ of dimension $k$, blocklength $n=O(k/\varepsilon^2)$, minimum distance $(1/2-\varepsilon)n$, satisfying (16) for every $x$. Steps: (1) $b_0=0$. (2) For $i=1,\dots,k$: let $U_i=\{x\in\{0,1\}^n: \mathrm{span}(b_1,\dots,b_{i-1},x)\cap B(0,(\tfrac12-\varepsilon)n)=\emptyset\}$; pick $b_i\in U_i$ minimizing $W_i=2^{-n}\sum_x 2^{\frac nA R_i^x}$ with $R_i^x$ as in (18) (ties broken arbitrarily). (3) Output $C=\mathrm{span}(b_1,\dots,b_k)$.

<a id="pdf-6bd33ae73ade-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.92 -->
**Lemma 23.** Algorithm GREEDY-INNER constructs a code $\mathrm{GREEDY}(k,\varepsilon)$ with the desired properties in $k\cdot 2^{O(n)}$ time. (Follows from the proof of Lemma 22, each of the $k$ loop iterations running in $2^{O(n)}$ time.)

<a id="pdf-6bd33ae73ade-p011-b009"></a>
<!-- pdf-source: page=11; block=9; confidence=0.90 -->
**V-B. A concatenated code construction. Theorem 24.** There exist absolute constants $b,d>0$ such that for every integer $K$ and every $\varepsilon>0$ there is a concatenated code $C_K \overset{\mathrm{def}}{=} \mathrm{RS}\oplus\mathrm{GREEDY}(m,\varepsilon/2)$ (suitable $m$) with: (1) $C_K$ linear of dimension $K$, blocklength $N\le bK/\varepsilon^4$, minimum distance $\ge(\tfrac12-\varepsilon)N$; (2) generator matrix constructible in $N^{O(\varepsilon^{-2})}$ time. Theorem 21 follows immediately from this.

<a id="pdf-6bd33ae73ade-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.92 -->
**Theorem 24 (continued).** (3) $C_K$ is $((\tfrac12-\varepsilon)N,\,d/\varepsilon^2)$-list decodable; any Hamming ball of radius $(\tfrac12-\varepsilon)N$ contains at most $O(\varepsilon^{-2})$ codewords of $C_K$. (4) There is a polynomial-time list decoding algorithm for $C_K$ correcting up to $(\tfrac12-\varepsilon)N$ errors.

<a id="pdf-6bd33ae73ade-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->
**Proof.** Concatenate an outer Reed–Solomon code over $\mathrm{GF}(2^m)$ of blocklength $n_0=2^m$, dimension $k_0=K/m$, with inner code $C_{\mathrm{inner}}=\mathrm{GREEDY}(m,\varepsilon/2)$ (Lemma 23). Inner blocklength $n_1=O(m/\varepsilon^2)$, so $C_K$ has dimension $K$, blocklength $N=O(n_0 m/\varepsilon^2)$ (23), and minimum distance $D\ge \bigl(1-\tfrac{K}{mn_0}\bigr)\bigl(\tfrac12-\tfrac\varepsilon2\bigr)N$ (24). Since $C_{\mathrm{inner}}$ is constructible in $2^{O(n_1)}=2^{O(m/\varepsilon^2)}$ time and $m=\log n_0$, the generator matrix of $C_K$ is constructible in $N^{O(\varepsilon^{-2})}$ time (Property 2).

List decoding: given received $y\in\{0,1\}^N$, find all $c\in C_K$ with $\Delta(y,c)\le 1/2-\varepsilon$. For $1\le i\le n_0$, let $y_i,c_i$ be the portions at the $i$th outer position; for $\alpha\in\mathrm{GF}(2^m)$ define $w_{i,\alpha}=\max\{(\tfrac12-\tfrac\varepsilon2-\Delta(y_i,C_{\mathrm{inner}}[\alpha])),\,0\}$ (25). By Lemmas 22/23, for each $i$: $\sum_{\alpha\in\mathrm{GF}(2^m)} w_{i,\alpha}^2 \le B'$ (26), $B'$ an absolute constant.

Decode inner codes by brute force over all codewords, passing per position $i$ the list of $\alpha$ with weights $w_{i,\alpha}$ (reliability that the $i$th outer symbol is $\alpha$); this costs $O(2^m)=O(n_0)$ per inner code, $\mathrm{poly}(N)$ total. Then apply the weighted (soft-decision) RS list-decoding algorithm of [12] (as in [13]), which in $\mathrm{poly}(n_0,1/\gamma)$ time finds all $c$ with $\sum_{i=1}^{n_0} w_{i,c_i} \ge \sqrt{\bigl(n_0-\tfrac{n_0-K/m+1}{1+\gamma}\bigr)\sum_{i,\alpha} w_{i,\alpha}^2}$ (27), where $w_{i,c_i}=w_{i,\alpha_i}$ with $C_{\mathrm{inner}}[\alpha_i]=c_i$; at most $(1+1/\gamma)$ codewords satisfy (27), so the list has $O(1/\gamma)$ entries.

By (25),(26), (27) holds if $\sum_{i=1}^{n_0}(\tfrac12-\tfrac\varepsilon2-\tfrac{\Delta(y_i,c_i)}{n_1}) \ge \sqrt{(\gamma n_0+\tfrac Km)\,n_0 B'}$, equivalently $\Delta(y,c)\le N\bigl(\tfrac12-\tfrac\varepsilon2-\sqrt{B'(\gamma+\tfrac{K}{mn_0})}\bigr)$ (28). Choosing $\gamma\le \tfrac{\varepsilon^2}{8B'}$ and $m$ with $\tfrac{K}{mn_0}=\tfrac{K}{m2^m}\le\tfrac{\varepsilon^2}{8B'}$, condition (27) holds whenever $\Delta(y,c)\le(\tfrac12-\varepsilon)N$. Thus the algorithm outputs all $O(1/\gamma)=O(\varepsilon^{-2})$ codewords within $(\tfrac12-\varepsilon)N$. Since $mn_0=O(K/\varepsilon^2)$, plugging into (23),(24) gives $N=O(K/\varepsilon^4)$ and $D\ge(\tfrac12-\varepsilon)N$. $\square$

<a id="pdf-6bd33ae73ade-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.90 -->
**Discussion.** The construction time $N^{O(\varepsilon^{-2})}$ is polynomial for each fixed $\varepsilon$ but not uniformly constructive (i.e. not $O(f(\varepsilon)n^c)$ for a fixed $c$). Using the best known algebraic-geometric codes (which beat the Gilbert–Varshamov bound) as the outer code instead of RS, the construction runs in $2^{O(\varepsilon^{-2}\log(1/\varepsilon))}N^c$ time (fixed $c$), but such AG codes have high construction complexity. Open question: find a simpler uniformly constructive code meeting Theorem 24's requirements.

<a id="pdf-6bd33ae73ade-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.80 -->
**VI. Concluding Remarks.** The paper reported codes with non-trivial list decoding properties; one result was an existence result (text continues beyond the supplied pages).

<a id="pdf-6bd33ae73ade-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.97 -->
Bibliography (references [10]–[25]) for a paper on combinatorial bounds for list decoding: works by Guruswami (list-decoding thesis; limits to list decodability of linear codes; with Sudan on Reed–Solomon/AG codes, concatenated codes, Johnson-bound extensions), Hardy–Littlewood–Pólya *Inequalities*, Justesen–Høholdt on MDS list-decoding bounds, Shannon–Gallager–Berlekamp error-probability bounds, Shokrollahi–Wasserman, Sudan (RS decoding beyond error-correction bound; survey), Tsfasman–Vlăduţ–Zink, van Lint, Wei–Feng, Wozencraft, Zyablov–Pinsker. Bibliographic only; no mathematical content.

<a id="pdf-6bd33ae73ade-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.90 -->
Concluding remarks (appears after the references in the flattened text). Key claims summarized: (1) Linear codes exist with an arbitrarily large polynomial number of codewords in a Hamming ball of relative radius strictly less than the relative distance; nonlinear existence is easy (random coding), the linear case harder. The Section III techniques plus new ideas were later used to prove Conjecture 9 under a widely believed number-theoretic conjecture [11] (cf. [10, Ch. 4]); this does not subsume Theorem 11, which holds unconditionally. (2) Theorem 5 gives existence of good-rate codes with few codewords in a large-radius Hamming ball, via a nonconstructive proof lacking a high-probability guarantee; whether a random linear code satisfies Theorem 5's property w.h.p. is open. (3) Theorem 5 adapts to yield linear inner codes for concatenation with an outer Reed–Solomon code, giving an efficiently constructible family of binary linear codes of rate $\Omega(\varepsilon^4)$ and relative distance $\ge 1/2-\varepsilon$, list-decodable from a $(1/2-\varepsilon)$ fraction of errors with list size $O(\varepsilon^{-2})$. This improves [13]'s best rate $\Omega(\varepsilon^6)$. Construction time is polynomial for fixed $\varepsilon$ but exponential in $1/\varepsilon$; reducing to polynomial in both $N$ and $1/\varepsilon$ is desirable.

<a id="pdf-6bd33ae73ade-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.97 -->
Acknowledgements: thanks to Amnon Ta-Shma and Alex Russell for discussions about Theorem 10.

<a id="pdf-6bd33ae73ade-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.97 -->
Bibliography (references [1]–[9]): Ahlswede (channel capacities for list codes), Ashikhmin–Barg–Litsyn (upper bound for size-2 list decoding), Blinovsky (three works on list-decoding bounds and multiple packing), Dumer–Micciancio–Sudan (hardness of approximating minimum distance), Elias (two works on list decoding), Goldreich–Rubinfeld–Sudan (learning polynomials, highly noisy case). Bibliographic only; no mathematical content.

<a id="pdf-6bd33ae73ade-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.97 -->
Author biographies (no mathematical content): Venkatesan Guruswami (Miller Postdoctoral Fellow, UC Berkeley; IIT Madras 1997, MIT PhD 2001; approximability, complexity, coding). Johan Håstad (Professor, Royal Institute of Technology, Stockholm; complexity, algorithms, cryptography, coding). Madhu Sudan (Associate Professor, MIT EECS; IIT Delhi 1987, UC Berkeley PhD 1992; complexity, algorithms, coding). David Zuckerman (Associate Professor, UT Austin; Harvard AB 1987, UC Berkeley PhD 1991; randomness in computation, pseudorandomness, complexity, coding).
