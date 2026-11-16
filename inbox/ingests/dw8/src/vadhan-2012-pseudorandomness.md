<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# Pseudorandomness

Salil P. Vadhan. *Foundations and Trends in Theoretical Computer Science* 7(1–3):1–336,
2012 (tag `Vad12`). Uploaded copy: the published Now Publishers version, 339 PDF pages
(file `pseudorandomness-published-Dec12.pdf`).

**Scope.** Only the passages that the leftover-hash citations use are transcribed (DW-8):
Theorem 6.18 (the Leftover Hash Lemma) with its proof, and the definitions it needs —
Definition 3.21 (pairwise independent hash functions) with Definition 3.22 and the
2-universal remark, Definition 4.7 (collision probability) with Lemma 4.8, Definition 6.2
(statistical difference) with Lemma 6.3, Definition 6.7 (entropy measures), Definition 6.9
(k-source), Definition 6.13 (seeded extractors) and Definition 6.16 (strong extractors).
Theorem 6.17 is transcribed because Theorem 6.18 is stated against it, the Rényi-entropy
remark because it qualifies the proof, and the chapter notes for attribution. The PDF is
not committed. Anchors use the **physical** PDF page; the printed page is $p-3$
(`p182` is printed page 179). The scoped raw extraction is
`vadhan-2012-pseudorandomness.raw.md`. Mathematics is set in LaTeX; the wording is the
monograph's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-bf2ce5422088-p067-b001"></a>
<!-- pdf-source: page=67; block=1; confidence=0.95 -->

**Definition 3.21 (pairwise independent hash functions) (p. 64).** A family (i.e.,
multiset) of functions $\mathcal H=\{h:[N]\to[M]\}$ is *pairwise independent* if the
following two conditions hold when $H\stackrel{\scriptscriptstyle R}{\leftarrow}\mathcal H$
is a function chosen uniformly at random from $\mathcal H$:

1. $\forall x\in[N]$, the random variable $H(x)$ is uniformly distributed in $[M]$.
2. $\forall x_1\neq x_2\in[N]$, the random variables $H(x_1)$ and $H(x_2)$ are
   independent.

Equivalently, we can combine the two conditions and require that

$$
\forall x_1\neq x_2\in[N],\ \forall y_1,y_2\in[M],\quad
\Pr_{H\stackrel{\scriptscriptstyle R}{\leftarrow}\mathcal H}
\left[H(x_1)=y_1\wedge H(x_2)=y_2\right]=\frac{1}{M^2}.
$$

Note that the probability above is over the random choice of a function from the family
$\mathcal H$. This is why we talk about a family of functions rather than a single
function.

*Transcription note.* The `-layout` extraction drops the $\neq$ glyph, printing
"$\forall x_1 = x_2$"; the page image (150 dpi) shows $\forall x_1\neq x_2$, as
transcribed.

<a id="pdf-bf2ce5422088-p067-b002"></a>
<!-- pdf-source: page=67; block=2; confidence=0.95 -->

**Definition 3.22 (p. 64).** A family of functions $\mathcal H=\{h:[N]\to[M]\}$ is
*explicit* if given the description of $h$ and $x\in[N]$, the value $h(x)$ can be computed
in time $\mathrm{poly}(\log N,\log M)$.

**The 2-universal notion (p. 64).** Pairwise independent hash functions are sometimes
referred to as *strongly 2-universal hash functions*, to contrast with the weaker notion of
*2-universal hash functions*, which requires only that $\Pr[H(x_1)=H(x_2)]\le 1/M$ for all
$x_1\neq x_2$. (Note that this property is all we needed for the deterministic MaxCut
algorithm, and it allows for a small savings in that we can also include $S=\emptyset$ in
Construction 3.18.)

<a id="pdf-bf2ce5422088-p088-b001"></a>
<!-- pdf-source: page=88; block=1; confidence=0.95 -->

**Definition 4.7 (p. 85).** For a probability distribution $\pi$, the *collision
probability* of $\pi$ is defined to be the probability that two independent samples from
$\pi$ are equal, namely $\mathrm{CP}(\pi)=\sum_x \pi_x^2$. The *support* of $\pi$ is
$\mathrm{Supp}(\pi)=\{x:\pi_x>0\}$.

**Lemma 4.8 (p. 85).** For every probability distribution $\pi\in[0,1]^N$, we have:

1. $\mathrm{CP}(\pi)=\lVert\pi\rVert^2=\lVert\pi-u\rVert^2+1/N$, where $u$ is the uniform
   distribution on $[N]$.
2. $\mathrm{CP}(\pi)\ge 1/|\mathrm{Supp}(\pi)|$, with equality iff $\pi$ is uniform on
   $\mathrm{Supp}(\pi)$.

*Transcription note.* The `-layout` extraction drops the norm bars, printing "$\pi 2$" for
$\lVert\pi\rVert^2$; the page image (150 dpi) shows the norms, as transcribed.

<a id="pdf-bf2ce5422088-p172-b001"></a>
<!-- pdf-source: page=172; block=1; confidence=0.95 -->

**Definition 6.2 (p. 169).** For random variables $X$ and $Y$ taking values in
$\mathcal U$, their *statistical difference* (also known as *variation distance*) is
$\Delta(X,Y)=\max_{T\subset\mathcal U}\left|\Pr[X\in T]-\Pr[Y\in T]\right|$. We say that
$X$ and $Y$ are *$\varepsilon$-close* if $\Delta(X,Y)\le\varepsilon$.

**Lemma 6.3 (properties of statistical difference) (p. 169).** Let
$X,Y,Z,X_1,X_2,Y_1,Y_2$ be random variables taking values in a universe $\mathcal U$.
Then,

1. $\Delta(X,Y)\ge 0$, with equality iff $X$ and $Y$ are identically distributed,
2. $\Delta(X,Y)\le 1$, with equality iff $X$ and $Y$ have disjoint supports,
3. $\Delta(X,Y)=\Delta(Y,X)$,
4. $\Delta(X,Z)\le\Delta(X,Y)+\Delta(Y,Z)$,
5. for every function $f$, we have $\Delta(f(X),f(Y))\le\Delta(X,Y)$,
6. $\Delta((X_1,X_2),(Y_1,Y_2))\le\Delta(X_1,Y_1)+\Delta(X_2,Y_2)$ if $X_1$ and $X_2$, as
   well as $Y_1$ and $Y_2$, are independent, and
7. $\Delta(X,Y)=\tfrac12\cdot|X-Y|_1$, where $|\cdot|_1$ is the $\ell_1$ distance. (Thus,
   $X$ is $\varepsilon$-close to $Y$ iff we can transform $X$ into $Y$ by "shifting" at
   most an $\varepsilon$ fraction of probability mass.)

<a id="pdf-bf2ce5422088-p174-b001"></a>
<!-- pdf-source: page=174; block=1; confidence=0.95 -->

**Section 6.1.2, Entropy Measures and General Weak Sources (p. 171).** Intuitively, to
extract $m$ almost-uniform bits from a source, the source must have at least "$m$ bits of
randomness" in it. (In particular, its support cannot be much smaller than $2^m$.) Ideally,
this is all we would like to assume about a source. Thus, we need some measure of how much
randomness is in a random variable; this can be done using various notions of entropy
described below.

**Definition 6.7 (entropy measures) (p. 171).** Let $X$ be a random variable. Then

- the *Shannon entropy* of $X$ is:
  $$\mathrm{H}_{\mathrm{Sh}}(X)=\operatorname*{\mathbb E}_{x\stackrel{\scriptscriptstyle R}{\leftarrow}X}\left[\log\frac{1}{\Pr[X=x]}\right].$$
- the *Rényi entropy* of $X$ is:
  $$\mathrm{H}_2(X)=\log\left(\frac{1}{\operatorname*{\mathbb E}_{x\stackrel{\scriptscriptstyle R}{\leftarrow}X}[\Pr[X=x]]}\right)=\log\frac{1}{\mathrm{CP}(X)},\quad\text{and}$$
- the *min-entropy* of $X$ is:
  $$\mathrm{H}_\infty(X)=\min_x\left(\log\frac{1}{\Pr[X=x]}\right),$$

where all logs are base 2.

<a id="pdf-bf2ce5422088-p176-b001"></a>
<!-- pdf-source: page=176; block=1; confidence=0.95 -->

**Definition 6.9 (p. 173).** A random variable $X$ is a *$k$-source* if
$\mathrm{H}_\infty(X)\ge k$, i.e., if $\Pr[X=x]\le 2^{-k}$.

A typical setting of parameters is $k=\delta n$ for some fixed $\delta$, e.g., $0.01$. We
call $\delta$ the *min-entropy rate*.

<a id="pdf-bf2ce5422088-p179-b001"></a>
<!-- pdf-source: page=179; block=1; confidence=0.95 -->

**Definition 6.13 (seeded extractors) (p. 176).** A function
$\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a *$(k,\varepsilon)$-extractor* if
for every $k$-source $X$ on $\{0,1\}^n$, $\mathrm{Ext}(X,U_d)$ is $\varepsilon$-close to
$U_m$.

(Sometimes we will refer to extractors $\mathrm{Ext}:[N]\times[D]\to[M]$ whose domain and
range do not consist of bit-strings. These are defined in the natural way, requiring that
$\mathrm{Ext}(X,U_{[D]})$ is $\varepsilon$-close to $U_{[M]}$.)

<a id="pdf-bf2ce5422088-p181-b001"></a>
<!-- pdf-source: page=181; block=1; confidence=0.95 -->

**Section 6.2.1, Extractors as Hash Functions (p. 178).** Proposition 6.12 says that for
any subset $S\subset[N]$ of size $K$, if we choose a completely random hash function
$h:[N]\to[M]$ for $M\ll K$, then $h$ will map the elements of $S$ almost-uniformly to
$[M]$. Equivalently, if we let $H$ be distributed uniformly over all functions
$h:[N]\to[M]$ and $X$ be uniform on the set $S$, then $(H,H(X))$ is statistically close to
$(H,U_{[M]})$, where we use the notation $U_T$ to denote the uniform distribution on a set
$T$. Can we use a smaller family of hash functions than the set of all functions
$h:[N]\to[M]$? This gives rise to the following variant of extractors.

**Definition 6.16 (strong extractors) (p. 178).** Extractor
$\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ is a *strong
$(k,\varepsilon)$-extractor* if for every $k$-source $X$ on $\{0,1\}^n$,
$(U_d,\mathrm{Ext}(X,U_d))$ is $\varepsilon$-close to $(U_d,U_m)$. Equivalently,
$\mathrm{Ext}'(x,y)=(y,\mathrm{Ext}(x,y))$ is a standard $(k,\varepsilon)$-extractor.

*Transcription note.* The `-layout` extraction prints the primed name as "Ext" without its
prime and "$M \quad K$" for $M\ll K$; the page image (150 dpi) shows $\mathrm{Ext}'$ and
$M\ll K$, as transcribed.

<a id="pdf-bf2ce5422088-p182-b001"></a>
<!-- pdf-source: page=182; block=1; confidence=0.95 -->

**Theorem 6.17 (p. 179).** For every $n,k\in\mathbb N$ and $\varepsilon>0$ there exists a
strong $(k,\varepsilon)$-extractor
$\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m$ with
$m=k-2\log(1/\varepsilon)-O(1)$ and $d=\log(n-k)+2\log(1/\varepsilon)+O(1)$.

Note that the output length is $m\approx k$ instead of $m\approx k+d$; intuitively a strong
extractor needs to extract randomness that is *independent* of the seed and thus can only
get the $k$ bits from the source.

We see that strong extractors can be viewed as very small families of hash functions having
the almost-uniform mapping property mentioned above. Indeed, our first explicit
construction of extractors is obtained by using pairwise independent hash functions.

<a id="pdf-bf2ce5422088-p182-b002"></a>
<!-- pdf-source: page=182; block=2; confidence=0.95 -->

**Theorem 6.18 (Leftover Hash Lemma) (p. 179).** If
$\mathcal H=\{h:\{0,1\}^n\to\{0,1\}^m\}$ is a pairwise independent (or even 2-universal)
family of hash functions where $m=k-2\log(1/\varepsilon)$, then
$\mathrm{Ext}(x,h)\stackrel{\mathrm{def}}{=}h(x)$ is a strong
$(k,\varepsilon)$-extractor. Equivalently, $\mathrm{Ext}(x,h)=(h,h(x))$ is a standard
$(k,\varepsilon)$-extractor.

Note that the seed length equals the number of random bits required to choose
$h\stackrel{\scriptscriptstyle R}{\leftarrow}\mathcal H$, which is at least $n$ by
Problem 3.5. This is far from optimal; for the purposes of simulating randomized algorithms
we would like $d=O(\log n)$. However, the output length of the extractor is
$m=k-2\log(1/\varepsilon)$, which is optimal up to an additive constant.

**Proof (opening).** Let $X$ be an arbitrary $k$-source on $\{0,1\}^n$, $\mathcal H$ as
above, and $H\stackrel{\scriptscriptstyle R}{\leftarrow}\mathcal H$. Let $d$ be the seed
length. We show that $(H,H(X))$ is $\varepsilon$-close to $U_d\times U_m$ in the following
three steps:

1. We show that the collision probability of $(H,H(X))$ is close to that of
   $U_d\times U_m$.

*Footnote 2 (p. 179).* Problem 3.5 refers to pairwise independent families, but a similar
argument shows that universal families require $\Omega(n)$ random bits. (Instead of
constructing orthogonal vectors, we construct vectors that have nonpositive dot product.)

<a id="pdf-bf2ce5422088-p183-b001"></a>
<!-- pdf-source: page=183; block=1; confidence=0.95 -->

**Proof of Theorem 6.18, continued (p. 180).**

2. We note that this is equivalent to saying that the $\ell_2$ distance between $(H,H(X))$
   and $U_d\times U_m$ is small.
3. Then we deduce that the statistical difference is small, by recalling that the
   statistical difference equals half of the $\ell_1$ distance, which can be (loosely)
   bounded by the $\ell_2$ distance.

*Proof of (1):* By definition,
$\mathrm{CP}(H,H(X))=\Pr[(H,H(X))=(H',H'(X'))]$, where $(H',X')$ is independent of and
identically distributed to $(H,X)$. Note that $(H,H(X))=(H',H'(X))$ if and only if $H=H'$
and either $X=X'$ or $X\neq X'$ but $H(X)=H(X')$. Thus

$$
\mathrm{CP}(H,H(X))=\mathrm{CP}(H)\cdot\left(\mathrm{CP}(X)+\Pr[H(X)=H(X')\mid X\neq X']\right)
\le\frac1D\cdot\left(\frac1K+\frac1M\right)\le\frac{1+\varepsilon^2}{DM}.
$$

To see the penultimate inequality, note that $\mathrm{CP}(H)=1/D$ because there are $D$
hash functions, $\mathrm{CP}(X)\le 1/K$ because $\mathrm{H}_\infty(X)\ge k$, and
$\Pr[H(X)=H(X')\mid X\neq X']\le 1/M$ by 2-universality.

*Proof of (2):*

$$
\lVert (H,H(X))-U_d\times U_m\rVert^2=\mathrm{CP}(H,H(X))-\frac{1}{DM}
\le\frac{1+\varepsilon^2}{DM}-\frac{1}{DM}=\frac{\varepsilon^2}{DM}.
$$

*Proof of (3):* Recalling that the statistical difference between two random variables $X$
and $Y$ is equal to $\tfrac12|X-Y|_1$, we have:

$$
\begin{aligned}
\Delta\left((H,H(X)),U_d\times U_m\right)
&=\frac12\cdot\left|(H,H(X))-U_d\times U_m\right|_1\\
&\le\frac{\sqrt{DM}}{2}\cdot\left\lVert (H,H(X))-U_d\times U_m\right\rVert\\
&\le\frac{\sqrt{DM}}{2}\cdot\sqrt{\frac{\varepsilon^2}{DM}}\\
&=\frac{\varepsilon}{2}.
\end{aligned}
$$

Thus, we have in fact obtained a strong $(k,\varepsilon/2)$-extractor. $\square$

*Transcription note.* The "if and only if" sentence is transcribed as printed: the page
image (150 dpi) shows $(H,H(X))=(H',H'(X))$ there, with an unprimed $X$ in $H'(X)$,
although the displayed collision probability and the surrounding argument use
$(H',H'(X'))$.

*Transcription note.* The `-layout` extraction drops the $\neq$ glyphs, the norm bars and
the $\ell_1$/$\ell_2$ subscripts (printing "$\ell$" as a bare superscript-like mark); all
were read from the page image (150 dpi), as transcribed.

<a id="pdf-bf2ce5422088-p184-b001"></a>
<!-- pdf-source: page=184; block=1; confidence=0.95 -->

**Rényi-entropy remark (p. 181).** The proof above actually shows that
$\mathrm{Ext}(x,h)=h(x)$ extracts with respect to collision probability, or equivalently,
with respect to the $\ell_2$-norm. This property may be expressed in terms of Rényi entropy
$\mathrm{H}_2(Z)\stackrel{\mathrm{def}}{=}\log(1/\mathrm{CP}(Z))$. Indeed, we can define
$\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^d\longrightarrow\{0,1\}^m$ to be a
*$(k,\varepsilon)$ Rényi-entropy extractor* if $\mathrm{H}_2(X)\ge k$ implies
$\mathrm{H}_2(\mathrm{Ext}(X,U_d))\ge m-\varepsilon$ (or
$\mathrm{H}_2(U_d,\mathrm{Ext}(X,U_d))\ge m+d-\varepsilon$ for strong Rényi-entropy
extractors). Then the above proof shows that pairwise-independent hash functions yield
strong Rényi-entropy extractors.

In general, it turns out that an extractor with respect to Rényi entropy must have seed
length $d\ge\min\{m/2,n-k\}-O(1)$ (as opposed to $d=O(\log n)$); this explains why the seed
length in the above extractor is large. (See Problem 6.4.)

<a id="pdf-bf2ce5422088-p212-b001"></a>
<!-- pdf-source: page=212; block=1; confidence=0.95 -->

**Chapter notes, attribution of Theorem 6.18 (pp. 209–210).** The notion of seeded
extractor we focus on in this section (Definitions 6.13, 6.16) was introduced by Nisan and
Zuckerman [303], who also gave the first construction of extractors with polylogarithmic
seed length (building on [426]). A form of the Leftover Hash Lemma (for flat distributions,
and where the quality of the output distribution is measured with entropy rather than
statistical difference) was first proven by Bennett, Brassard, and Robert [63]. The version
in Theorem 6.18 is due to Impagliazzo, Levin, and Luby [197], and the proof we give is due
to Rackoff [217].
