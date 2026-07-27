<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: b5e074215b9e0121d54f205bd83f4ab4e47b00b42a5b8d7e2691117e5b3b7ec3 -->

<a id="pdf-b5e074215b9e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Notes on Complexity Theory

**Last updated:** May 2015

## Lecture on H˚astad’s Switching Lemma

Jonathan Katz

<a id="pdf-b5e074215b9e-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
## 1. Introduction and Background

<a id="pdf-b5e074215b9e-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
We have already seen an “algebraic” approach to proving that computing parity requires exponential-size $\mathrm{AC}^0$ circuits. Here we give a more combinatorial proof. Besides being interesting as a different technique, it also gives a better lower bound on the size of $\mathrm{AC}^0$ circuits needed to compute parity.

Recall that $\mathrm{AC}^0$ is the set of languages/problems decided by constant-depth, polynomial-size circuits with gates of unbounded fan-in. We consider the basis consisting of AND, OR, and NOT gates, though NOT gates are not counted when measuring circuit depth or size.

<a id="pdf-b5e074215b9e-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.97 -->
A DNF formula on $n$ variables is a disjunction of terms, each of which is a conjunction of literals. For example,

$$f(x_1,\ldots,x_n)=(x_1\wedge\bar{x}_2)\vee(x_7\wedge\bar{x}_8\wedge\bar{x}_{11})$$

is a DNF formula. Analogously, a CNF formula is a conjunction of terms, each of which is a disjunction of literals. The size of a DNF/CNF formula is the number of terms, and its width is the maximum number of literals in any term.

<a id="pdf-b5e074215b9e-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.99 -->
A decision tree is a directed, acyclic graph with a designated start vertex having in-degree $0$. Each vertex other than the leaves has out-degree two. Each non-leaf vertex is labeled with a variable and has one outgoing edge labeled $0$ and one labeled $1$. Each leaf vertex is labeled either $0$ or $1$. A decision tree computes a function in the natural way.

The depth of a decision tree is the maximum path length from the start to a leaf, and its size is the number of leaves. For a function $f$, write $\mathrm{DTdepth}(f)$ for the smallest depth of any decision tree computing $f$. Any function on $n$ variables satisfies $\mathrm{DTdepth}(f)\le n$.

<a id="pdf-b5e074215b9e-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.99 -->
## 2. The Switching Lemma

<a id="pdf-b5e074215b9e-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.98 -->
Let $f:\{0,1\}^n\to\{0,1\}$ be a function on $n$ variables. An $s$-restriction $\alpha$ fixes $n-s$ of the variables to $0$ or $1$ and leaves the remaining $s$ variables free. We write $f|_\alpha$ for the resulting reduced function.

A uniform $s$-restriction is chosen by selecting a random subset of $s$ variables and fixing each of the other variables uniformly to $0$ or $1$.

<a id="pdf-b5e074215b9e-p001-b008"></a>
<!-- pdf-source: page=1; block=8; confidence=0.99 -->
**Theorem 1.** Let $f:\{0,1\}^n\to\{0,1\}$ be computed by a DNF formula of width at most $w$. Let $\alpha$ be a random $s$-restriction with $s=\sigma n\le n/5$. Then, for any $d\ge0$,

$$\Pr_\alpha\big[\mathrm{DTdepth}(f|_\alpha)>d\big]\le(10\sigma w)^d.$$

<a id="pdf-b5e074215b9e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
**Proof.** Fix $d$ and let $\mathcal B$ be the set of “bad” $s$-restrictions, namely those $s$-restrictions $\beta$ for which $\mathrm{DTdepth}(f|_\beta)>d$. We show that each bad restriction can be encoded using a small number of bits, and hence that $\mathcal B$ is small relative to the set of all $s$-restrictions.

<a id="pdf-b5e074215b9e-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.99 -->
Let $f$ be computed by the DNF formula $T_1\vee\cdots\vee T_\ell$, where each $T_i$ contains at most $w$ literals. Restriction $\alpha$ kills a term $T_i$ if it sets one of its literals to $0$; that term is then removed from $f|_\alpha$. We say that $\alpha$ fixes a term $T_i$ if it sets all literals in $T_i$ to $1$; then $T_i$, and hence the entire formula, becomes the constant $1$.

If $\beta$ is bad, it neither fixes any term nor kills all terms, since either case would yield a constant-depth decision tree.

For a bad restriction $\beta$, define a canonical decision tree for $f|_\beta$ as follows. Take the first term $T_{i_1}$ not killed by $\beta$, and suppose it has $d_1$ free variables. Form the complete depth-$d_1$ decision tree over those variables, considering them in order. Its unique $1$-leaf becomes a $1$-leaf in the canonical tree. For each $0$-leaf, continue by fixing variables according to the path to that leaf, thereby defining a new restriction $\beta'$, and repeat with the first term not killed by $\beta'$. If the remaining function is constant, that leaf is made a leaf of the canonical tree.

<a id="pdf-b5e074215b9e-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.96 -->
Since $\beta$ is bad, its canonical decision tree has depth greater than $d$. Take a path of length exceeding $d$, and let $P$ be its first $d$ steps. Fix the $d$ variables traversed by $P$ to their values on that path. The resulting $(s-d)$-restriction, consisting of $\beta$ plus these $d$ additional fixed variables, is denoted by $\pi$.

Suppose $P$ traverses subtrees associated with terms $T_{i_1},T_{i_2},\ldots,T_{i_\ell}$ involving $d_1,d_2,\ldots$ free variables, with $\pi$ possibly ending in the middle of $T_{i_\ell}$. Encode $\beta$ by an $(s-d)$-restriction $\gamma$ plus auxiliary information. Starting with $\beta$, form $\gamma$ by fixing the $d_1$ variables in $T_{i_1}$ to the unique values that fix $T_{i_1}$, then the $d_2$ variables in $T_{i_2}$, and so on. In general, $\gamma$ does not correspond to $\pi$.

For each term, record (1) which variables in the term are fixed at that iteration and (2) how those variables are set in $\pi$. The first item uses at most $d_i\lceil\log(w+1)\rceil\le d_i\log w+d_i$ bits, using an alphabet of size $w+1$ for positions and a termination character. The second uses $d_i$ bits.

<a id="pdf-b5e074215b9e-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.99 -->
The encoding recovers $\beta$ from $f$. Given the encoding, we find the first clause $T_{i_1}$ of $f$ that is fixed under $\gamma$. The auxiliary information tells us which variables in that clause were fixed when extending $\beta$, as well as how those variables were set in $\pi$. This process is continued until we get a list of all the variables that were set in forming $\gamma$ (equivalently, $\pi$), thus allowing us to recover the original restriction $\beta$.

How many bits did we use to encode $\beta$? We encoded $\beta$ using an $(s-d)$-restriction $\gamma$ plus $d\log w+2d$ additional bits. So the total number of bad restrictions is at most

$$\binom{n}{s-d}\cdot 2^{n-s+d}\cdot(4w)^d,$$

and the fraction of bad restrictions is at most

$$\frac{\binom{n}{s-d}\cdot 2^{n-s+d}\cdot(4w)^d}{\binom{n}{s}\cdot 2^{n-s}}
\le \left(\frac{s}{n-s+d}\right)^d(8w)^d
\le \left(\frac{\sigma}{1-\sigma}\right)^d(8w)^d
\le (10\sigma w)^d,$$

using $\sigma<1/5$.

<a id="pdf-b5e074215b9e-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
A similar proof applies when $f$ is computed by a CNF formula. For the next section, it is useful to rephrase the switching lemma using the following observation.

<a id="pdf-b5e074215b9e-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.99 -->
**Lemma 2.** If $\mathrm{DTdepth}(f)\le d$, then $f$ has a width-$d$ DNF formula and a width-$d$ CNF formula.

<a id="pdf-b5e074215b9e-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
**Proof.** Given a depth-$d$ decision tree for $f$, obtain a width-$d$ DNF for $f$ by taking the disjunction of all paths leading to $1$-leaves. Since $f$ has a depth-$d$ decision tree, so does $\neg f$. Hence $\neg f$ has a width-$d$ DNF, and by applying De Morgan’s law, $f$ has a width-$d$ CNF.

<a id="pdf-b5e074215b9e-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.99 -->
**Corollary 3.** Let $f : \{0,1\}^n \to \{0,1\}$ be computed by a DNF formula (resp., CNF formula) of width at most $w$. Let $\alpha$ be a random $s$-restriction with $s \le n/5$. Then $f|_\alpha$ can be computed by a CNF formula (resp., DNF formula) of width $w$ except with probability at most

$$\left(\frac{10sw}{n}\right)^w.$$

<a id="pdf-b5e074215b9e-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.99 -->
## 3. A Lower Bound for Parity

We use the switching lemma to derive a lower bound for the size of $\mathrm{AC}^0$ circuits computing parity. We rely on the following easy lemma.

<a id="pdf-b5e074215b9e-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.99 -->
**Lemma 4.** Any DNF (respectively, CNF) formula computing parity or its negation on $n$-bit inputs must have width $n$.

<a id="pdf-b5e074215b9e-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.99 -->
**Proof.** We focus on DNF formulas; CNF formulas are handled similarly. Suppose there is a term $T$ with fewer than $n$ literals. Set the variables so that $T$ evaluates to $1$. Then the DNF evaluates to $1$ regardless of how the remaining variables are set. But toggling any variable not in $T$ should toggle the value of parity (or its negation), a contradiction.

<a id="pdf-b5e074215b9e-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.99 -->
**Theorem 5.** For sufficiently large $n$, any depth-$d$ circuit that computes parity on $n$-bit inputs must have size at least

$$2^{\Omega(n^{1/(d-1)})}.$$

<a id="pdf-b5e074215b9e-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.97 -->
**Proof.** Suppose we have a depth-$d$ circuit of size $S$ computing parity. We assume, without loss of generality:

- NOT gates occur only at the inputs.
- The circuit is layered, with gates at one layer feeding only into the next layer, and all gates at a layer having the same type.
- Each gate has fan-out $1$; the inputs may have unbounded fan-out.

Any depth-$d$, size-$S$ circuit can be converted to this form without increasing depth and with size increasing to $O((dS)^d)$. Since $d$ is constant, this does not affect the theorem statement.

Let $w=20\log S$. Assume for concreteness that the inputs feed into AND gates at the top level; the OR case is analogous. We claim that every top-level gate may be assumed to have fan-in at most $w$.

<a id="pdf-b5e074215b9e-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.99 -->
If a top-level gate has fan-in greater than $w$, apply a random restriction in which each variable is fixed with probability $c=2-\sqrt{2}\approx 0.6$ (and, if so, is fixed to 0 or 1 with half probability each). One can show that, with positive probability, the resulting circuit has no gates at the top level with fan-in greater than $w$, and at least $n/4$ variables remain free. Note that the resulting restricted function computes parity or its negation. Since the number of variables is reduced by only a constant factor, this does not affect the theorem statement.

<a id="pdf-b5e074215b9e-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.98 -->
Set $n_0=n$ and let

$$n_i=\frac{n_{i-1}}{20w}\qquad\text{for }i=1,\ldots,d-2.$$

The gates at the second layer of the circuit each compute a DNF formula of width at most $w$. Focusing on any particular such gate, and applying Corollary 3 with an $n_1$-restriction, we see that the output of that gate (after the restriction) can be computed by a width-$w$ CNF formula except with probability

$$\left(\frac{10n_1w}{n_0}\right)^w=2^{-20\log S}\ll\frac1S.$$

Since there are at most $S$ gates, a union bound shows that there exists an $n_1$-restriction for which all level-2 gates switch. Choosing any such restriction, the DNF sub-circuits can then be swapped for width-$w$ CNF sub-circuits. But then the AND gates at levels 2 and 3 can be coalesced, reducing the depth by 1. Note that the restricted function still computes parity or its negation, now on $n_1$-bit inputs.

<a id="pdf-b5e074215b9e-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->
Continuing in this way, repeatedly apply Corollary 3 for $i=2,\ldots,d-2$. This yields a width-$w$ CNF or DNF formula computing parity on $n_{d-2}$-bit inputs, where

$$n_{d-2}=\frac{n}{(20w)^{d-2}}=\frac{n}{(400\log S)^{d-2}}.$$

By Lemma 4, such a formula must have width $n_{d-2}$. Hence $w=n_{d-2}$, which implies the claimed lower bound on $S$.

<a id="pdf-b5e074215b9e-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.99 -->
## Bibliographic Notes

The general proof strategy used here is due to Furst, Saxe, and Sipser, with the bound claimed here due to H˚astad [1]. The simplified proof of the switching lemma is due to Razborov. The presentation is based on notes by O’Donnell [2].

<a id="pdf-b5e074215b9e-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.99 -->
## References

[1] J. H˚astad. *Computational Limitations of Small-Depth Circuits*. MIT Press, 1987. Published version of the author’s PhD thesis.

[2] R. O’Donnell. “The Switching Lemma.” Lecture 14 of 15-855 *Intensive Intro to Complexity Theory*, Spring 2009. http://www.cs.cmu.edu/~odonnell/complexity
