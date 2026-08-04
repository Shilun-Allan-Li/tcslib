<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: abed77da6b7a75ec4d93cc73615f95b277fa31571f1e9c7c831aea094e4909e1 -->

<a id="pdf-abed77da6b7a-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->
# New Upper Bounds on the Rate of a Code via the Delsarte–MacWilliams Inequalities

R. J. McEliece, E. R. Rodemich, H. Rumsey Jr., L. R. Welch. IEEE Trans. Inform. Theory, IT-23, no. 2, March 1977.

<a id="pdf-abed77da6b7a-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** Starting from the Delsarte–MacWilliams inequalities, an upper bound on the rate of a binary code as a function of its minimum distance is derived; it is asymptotically smaller than Levenshtein's bound and hence than Elias's.

<a id="pdf-abed77da6b7a-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.97 -->
## I. Introduction

<a id="pdf-abed77da6b7a-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.93 -->
**Definitions.** $V_n$ = set of all $2^n$ binary $n$-tuples; for $x,y\in V_n$, $\|x-y\|$ = Hamming distance (number of differing components). A code $C=\{x_1,\dots,x_M\}\subseteq V_n$ has length $n$; the $x_i$ are codewords; minimum distance $d_{\min}(C)=\min_{i\ne j}\|x_i-x_j\|$; rate $R(C)=n^{-1}\log_2 M$. $M(n,d)$ = largest number of codewords in a length-$n$ code with minimum distance $\ge d$; $R(n,d)=n^{-1}\log_2 M(n,d)$. For $0\le\delta\le1$, (1.1): $R(\delta)=\sup\lim_{n\to\infty}R(n,d_n)$, the sup taken over all sequences $(d_n)$ with $d_n/n\to\delta$. (For a single vector $x$, $\|x\|=\|x-0\|$ is its Hamming weight.)

<a id="pdf-abed77da6b7a-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.90 -->
**Known values and classical bounds.** $R(0)=1$ and $R(\delta)=0$ for $1/2\le\delta\le1$; $R(\delta)$ unknown for $0<\delta<1/2$. Classical bounds (1.2): $1-g(4\delta(1-\delta))\le R(\delta)\le 1-g(2\delta)$, where for $0\le x\le1$, $g(x)=H_2\big((1-\sqrt{1-x})/2\big)$ and (1.3): $H_2(x)=-x\log_2 x-(1-x)\log_2(1-x)$. $g$ is monotonically increasing and concave on $[0,1]$; the lower bound is Gilbert's, the upper is Elias's. Sidelnikov and Levenshtein obtained upper bounds strictly below Elias's for $0<\delta<1/2$ (small numerical improvement).

<a id="pdf-abed77da6b7a-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.96 -->
**Main result.** For $0<\delta<1/2$, (1.4): $R(\delta)\le\min_{0\le u\le1-2\delta}\big[\,1+g(u^2)-g(u^2+2\delta u+2\delta)\,\big]$. Evaluating the bracket at $u=1-2\delta$ gives $g((1-2\delta)^2)$, so (1.4) implies (1.5): $R(\delta)\le g((1-2\delta)^2)$. Remarks: (1.4) equals (1.5) for $0.273\le\delta\le1/2$, so the minimization over $u$ improves (1.5) only for small $\delta$; at $u=0$, (1.4) yields the Elias bound, and since the derivative of $g(u^2)-g(u^2+2\delta u+2\delta)$ at $u=0$ is negative, (1.4) is always strictly below Elias. The bound (1.5) exceeds the Elias bound for $\delta<0.150$ and the Hamming bound $1-H_2(\delta/2)$ for $\delta<0.114$.

<a id="pdf-abed77da6b7a-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.85 -->
**Conjecture (footnote).** With $N(\delta)$ the new bound and $G(\delta)$ Gilbert's bound, $G(\delta)<R(\delta)<N(\delta)$ for all $0<\delta<1/2$.

<a id="pdf-abed77da6b7a-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.80 -->
**Fig. 2.** Plot of the Elias and Gilbert bounds versus $\delta$.

<a id="pdf-abed77da6b7a-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
**Table I.** Bounds on $R(\delta)$ ($L$ = Levenshtein, $E$ = Elias, $G$ = Gilbert). The upper-bound columns are (1.5), (1.4), $L$, and $E$; the lower-bound column is $G$.

| $\delta$ | (1.5) | (1.4) | $L$ | $E$ | $G$ |
|---|---|---|---|---|---|
| .00 | 1.000 | 1.000 | 1.000 | 1.000 | 1.000 |
| .02 | .943 | .918 | .919 | .919 | .859 |
| .04 | .886 | .854 | .856 | .856 | .758 |
| .06 | .831 | .797 | .801 | .801 | .673 |
| .08 | .776 | .744 | .749 | .750 | .598 |
| .10 | .722 | .693 | .701 | .702 | .531 |
| .12 | .669 | .644 | .655 | .656 | .471 |
| .14 | .617 | .597 | .612 | .613 | .416 |
| .16 | .567 | .551 | .570 | .571 | .366 |
| .18 | .517 | .505 | .529 | .531 | .320 |
| .20 | .469 | .461 | .490 | .492 | .278 |
| .22 | .422 | .418 | .451 | .454 | .240 |
| .24 | .377 | .375 | .414 | .417 | .205 |
| .26 | .333 | .333 | .377 | .381 | .173 |
| .28 | .291 | .291 | .342 | .346 | .145 |
| .30 | .250 | .250 | .307 | .312 | .119 |
| .32 | .212 | .212 | .272 | .278 | .096 |
| .34 | .175 | .175 | .238 | .245 | .075 |
| .36 | .141 | .141 | .205 | .213 | .057 |
| .38 | .110 | .110 | .172 | .181 | .042 |
| .40 | .081 | .081 | .140 | .150 | .029 |
| .42 | .056 | .056 | .107 | .119 | .019 |
| .44 | .035 | .035 | .076 | .088 | .010 |
| .46 | .017 | .017 | .045 | .059 | .005 |
| .48 | .005 | .005 | .018 | .029 | .001 |
| .50 | .000 | .000 | .000 | .000 | .000 |

<a id="pdf-abed77da6b7a-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.90 -->
**Plan.** §II outlines the proofs of (1.4) and (1.5); §III proves (1.5); §IV proves (1.4). Since (1.4) contains (1.5) as a special case, §III is logically optional but is included to introduce the intricate ideas needed for (1.4). The general bound (1.4) is only slightly better than the minimum of the Elias bound and (1.5), so (1.5) is regarded as the paper's most significant contribution.

<a id="pdf-abed77da6b7a-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
## II. The Delsarte–MacWilliams Inequalities and Linear Programming Bounds

<a id="pdf-abed77da6b7a-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.88 -->
**Setup.** Let $C=(x_1,\dots,x_M)$ be a code of length $n$ with $\|x_\mu-x_\nu\|\ge d$ for $\mu\ne\nu$. For each $i=0,1,\dots,n$, define $a_i$ as the average number of codewords at distance $i$ from a given codeword (definition continued on page 3).

<a id="pdf-abed77da6b7a-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->
**Distance distribution and DM inequalities.** (2.1) defines $a_i$ (average number of codewords at distance $i$ from a codeword). The vector $a=(a_0,a_1,\dots,a_n)$ is the distance distribution, with (2.2): $a_0=1$, $a_1=a_2=\cdots=a_{d-1}=0$, and $a_0+a_1+\cdots+a_n=M$. Let $K_j(i)$ be the coefficient of $y^j$ in $(1-y)^i(1+y)^{n-i}$. Delsarte–MacWilliams inequalities (2.3): $\sum_{i=0}^{n} a_i K_j(i)\ge0$ for $j=0,1,\dots,n$. (Proof in [4]; $K_j(i)$ discussed in Appendix A.)

<a id="pdf-abed77da6b7a-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
**Linear program.** $M_{LP}(n,d)$ = optimal value of the LP (2.4): maximize $a_0+a_1+\cdots+a_n$ subject to (2.4a) $a_0=1$ and $a_1=\cdots=a_{d-1}=0$; (2.4b) $a_i\ge0$ for $i=d,d+1,\dots,n$; (2.4c) $\sum_{i=0}^{n} a_i K_j(i)\ge0$ for $j=0,1,\dots,n$. By (2.2) and (2.3), $M(n,d)\le M_{LP}(n,d)$ — the linear programming bound.

<a id="pdf-abed77da6b7a-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->
**LP rate.** (2.5): $R_{LP}(\delta)=\sup\lim_{n\to\infty}n^{-1}\log_2 M_{LP}(n,d_n)$ (same sup as (1.1)). Clearly $R(\delta)\le R_{LP}(\delta)$. §III shows that for $0\le\delta\le1/2$, (2.6): $R_{LP}(\delta)\le g((1-2\delta)^2)$, which establishes (1.5). (Footnote: the authors do not believe this bound tight for any $0<\delta<1/2$.)

<a id="pdf-abed77da6b7a-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->
**Restriction to a subset (tighter bound).** For $B\subseteq V_n$, let $M_B(n,d)$ be the maximum number of codewords chosen from $B$ with pairwise distance $\ge d$. Well-known (2.7): $M(n,d)\le\dfrac{2^n}{|B|}\,M_B(n,d)$ (attributed to Elias or Bassalygo). Taking $B$ = all vectors of a fixed weight $w\in\{0,1,\dots,\lfloor n/2\rfloor\}$ and writing $M_B(n,d)=M(n,d,w)$ gives (2.8): $M(n,d)\le\dfrac{2^n}{\binom{n}{w}}\,M(n,d,w)$. Define (2.9): $R(\delta,\alpha)=\sup\lim_{n\to\infty}n^{-1}\log_2 M(n,d_n,w_n)$; using $n^{-1}\log_2\binom{n}{w_n}=H_2(\alpha)+o(n)$ (from Stirling) leads to (2.10).

<a id="pdf-abed77da6b7a-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.92 -->
**Table II.** Bounds on $R(\delta,\alpha)$ for $\delta=0.48$ (with $\delta^*=0.40$). Upper bounds: Levenshtein's bound and the new bound (2.16); Gilbert is the lower bound.

| $\alpha$ | Levenshtein | (2.16) | Gilbert (lower) |
|---|---|---|---|
| .40 | 0.00000 | 0.00000 | 0.00000 |
| .41 | 0.00117 | 0.00027 | 0.00004 |
| .42 | 0.00361 | 0.00085 | 0.00016 |
| .43 | 0.00657 | 0.00158 | 0.00031 |
| .44 | 0.00965 | 0.00236 | 0.00049 |
| .45 | 0.01240 | 0.00311 | 0.00066 |
| .46 | 0.01457 | 0.00378 | 0.00082 |
| .47 | 0.01612 | 0.00433 | 0.00096 |
| .48 | 0.01721 | 0.00475 | 0.00107 |
| .49 | 0.01764 | 0.00501 | 0.00113 |
| .50 | 0.01764 | 0.00509 | 0.00115 |

<a id="pdf-abed77da6b7a-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
The supremum in (2.9) is over sequences $(d_n),(w_n)$ with $d_n/n\to\delta$ and $w_n/n\to\alpha$. From (1.1) and (2.8):
$$R(\delta)\le 1-H_2(\alpha)+R(\delta,\alpha),\qquad 0\le\alpha\le\tfrac12.\tag{2.10}$$

<a id="pdf-abed77da6b7a-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.85 -->
Section IV bounds $M(n,d,w)$; its asymptotic form combined with (2.10) yields the main result (1.4). The bounding technique is sketched next.

<a id="pdf-abed77da6b7a-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.82 -->
**Definition.** Let $\{x_1,\dots,x_M\}$ be $M$ binary codewords of length $n$, weight $w$, with $\lVert x_\mu-x_\nu\rVert\ge d$ for $\mu\ne\nu$. For $i=0,1,\dots,w$ set
$$a_i=\tfrac1M\bigl|\{(\mu,\nu):\lVert x_\mu-x_\nu\rVert=2i\}\bigr|\tag{2.11}$$
(distances are even since all weights equal $w$). Then
$$a_0=1,\quad a_i=0\ \text{for }1\le i<d/2,\quad a_0+\cdots+a_w=M.\tag{2.12}$$

<a id="pdf-abed77da6b7a-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.82 -->
**Definition.** Delsarte [3, Thm 3.3] gives numbers $Q_j(i)$ playing the role of $K_j(i)$ in the constant-weight setting, satisfying
$$\sum_{i=0}^{w}a_i\,Q_j(i)\ge 0,\qquad j=0,1,\dots,w.\tag{2.13}$$
(These arise from Delsarte's theory of association schemes; (2.3) and (2.13) are special cases. The $Q_j(i)$ and their properties are in Appendix B.)

<a id="pdf-abed77da6b7a-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.85 -->
**Definition.** $M_{LP}(n,d,w)$ is the value of the linear program:
$$\text{maximize } a_0+a_1+\cdots+a_w$$
subject to $a_0=1$ (2.14a); $a_i=0$ for $1\le i<d/2$ (2.14b); $a_i\ge0$ for all $i$ (2.14c); $\sum_{i=0}^{w}a_iQ_j(i)\ge0$, $j=0,\dots,w$ (2.14d). Then $M(n,d,w)\le M_{LP}(n,d,w)$.

<a id="pdf-abed77da6b7a-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.85 -->
**Definition.**
$$R_{LP}(\delta,\alpha)=\sup\lim_{n\to\infty}\tfrac1n\log_2 M_{LP}(n,d_n,w_n),\tag{2.15}$$
supremum over the same sequences as in (2.9).

<a id="pdf-abed77da6b7a-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.70 -->
**Claim (proved in §IV).** For fixed $\delta$, $0<\delta<1/2$,
$$R_{LP}(\delta,\alpha)\le\begin{cases}0,&0\le\alpha\le\delta^*\\[2pt] g(u^2),&\delta^*\le\alpha\le\tfrac12\end{cases}\tag{2.16}$$
where $\delta^*=\dfrac{1-\sqrt{1-2\delta}}{2}$ and $u=-\delta+\bigl(\delta^2-2\delta+4\alpha(1-\alpha)\bigr)^{1/2}$. As $\alpha$ increases from $\delta^*$ to $1/2$, $u$ increases monotonically from $0$ to $1-2\delta$; since $H_2(\alpha)=g(u^2+2\delta u+2\delta)$, (2.10) and (2.16) together yield (1.4).

<a id="pdf-abed77da6b7a-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.62 -->
Levenshtein [5] also gives an upper bound on $R(\delta,\alpha)$; its complexity blocks analytic comparison, but (2.16) appears superior for relatively large $\delta$, as illustrated in Table II (Gilbert lower bound $H_2(\alpha)-\alpha H_2(\delta/2\alpha)-(1-\alpha)H_2(\delta/2(1-\alpha))$). Footnote conjecture: the bound is not tight, i.e. $R_{LP}(\delta,\alpha)<g(u^2)$ for $0<\delta<1/2$, $\delta^*<\alpha\le1/2$.

<a id="pdf-abed77da6b7a-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**III. Proof of (2.6).** Establishes the dual of the linear program (2.4); Fig. 4 shows the relationship between $K_{t+1}(x)$ and $K_j(x)$, $j\le t$.

<a id="pdf-abed77da6b7a-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.88 -->
**Theorem 1.** Let $(\lambda_0,\lambda_1,\dots,\lambda_n)$ be reals with
$$\lambda_0>0,\quad \lambda_j\ge0\ (j=1,\dots,n),\tag{3.1}$$
$$\sum_{j=0}^{n}\lambda_j K_j(i)\le0,\quad i=d,d+1,\dots,n.\tag{3.2}$$
Then
$$M_{LP}(n,d)\le\frac1{\lambda_0}\sum_{j=0}^{n}\lambda_j K_j(0).\tag{3.3}$$

<a id="pdf-abed77da6b7a-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.85 -->
**Proof.** Take $(a_0,\dots,a_n)$ feasible for (2.4) with $\sum a_i=M_{LP}(n,d)$, and set $b_j=\sum_{i=0}^n a_iK_j(i)$. By (3.1) and (2.4d),
$$\lambda_0 b_0\le\sum_{j=0}^n\lambda_j b_j=\sum_{i=0}^n a_i\sum_{j=0}^n\lambda_j K_j(i)\le\sum_{j=0}^n\lambda_j K_j(0).\tag{3.4}$$
Since $K_0(i)=1$ (coefficient of $z^0$ in $(1-z)^i(1+z)^{n-i}$), $b_0=\sum a_i=M_{LP}(n,d)$; combined with (3.4) this gives the theorem. $\square$

<a id="pdf-abed77da6b7a-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.90 -->
**Proof step.** $K_j(i)$ is a degree-$j$ polynomial in $i$, the Krawtchouk polynomial $K_j(x)$ (Appendix A). Fix integers $n,d$; take an integer $t$ with $1\le t\le n/2$ and a real $a\in[0,n]$. Define
$$P^*(x)=K_{t+1}(x)K_t(a)-K_t(x)K_{t+1}(a).$$
By property (A.16),
$$P^*(x)=\frac{2(a-x)}{t+1}\binom{n}{t}\sum_{k=0}^{t}\frac{K_k(x)K_k(a)}{\binom{n}{k}}.\tag{3.5}$$
Now define
$$P(x)=\frac{P^*(x)^2}{a-x}\tag{3.6}$$
$$=\frac{2}{t+1}\binom{n}{t}\bigl[K_{t+1}(x)K_t(a)-K_t(x)K_{t+1}(a)\bigr]\sum_{k=0}^{t}\frac{K_k(x)K_k(a)}{\binom{n}{k}}.\tag{3.7}$$

<a id="pdf-abed77da6b7a-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.72 -->
**Proof step.** Each $K_j(x)$ has $j$ distinct real zeros in $(0,n)$; let $x_1^{(j)}$ be the smallest. By (A.17), $x_1^{(t+1)}<x_1^{(t)}$. Choose $a$ with
$$x_1^{(t+1)}<a<x_1^{(t)}.\tag{3.8}$$
Since $K_j(0)=\binom{n}{j}>0$, then $K_j(a)>0$ for $j\le t$ and $K_{t+1}(a)<0$; so in (3.7) $P(x)$ is a nonnegative-coefficient sum of products of Krawtchouk polynomials, and by (A.19) each product re-expands with nonnegative coefficients. Hence $P(x)=\sum_j\lambda_j K_j(x)$ with $\lambda_j\ge0$. From (3.6), $P(x)\le0$ when $x\ge a$; assuming $a\le d$, $P(x)\le0$ for $x\ge d$, so the $\lambda_j$ satisfy Theorem 1 and $M_{LP}(n,d)\le P(0)/\lambda_0$.

<a id="pdf-abed77da6b7a-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.92 -->
**Proof step.** From (3.6), $M_{LP}(n,d)\le P(0)/\lambda_0$, where
$$P(0)=\frac1a\Bigl[\binom{n}{t+1}K_t(a)-\binom{n}{t}K_{t+1}(a)\Bigr]^2=\frac1a\binom{n}{t}^2K_t(a)^2\Bigl[\frac{n-t}{t+1}-Q\Bigr]^2,\quad Q=\frac{K_{t+1}(a)}{K_t(a)}.\tag{3.9}$$
Using $\lambda_0=\int P(x)\,d\beta$ (A.12) and the orthogonality (A.11),
$$\lambda_0=-\frac{2}{t+1}K_{t+1}(a)K_t(a)\int K_t^2(x)\,d\beta=-\frac{2}{t+1}\binom{n}{t}K_t(a)^2Q.\tag{3.10}$$

<a id="pdf-abed77da6b7a-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
**Proof step (§III cont.).** Combining (3.9),(3.10):
$$M_{LP}(n,d)\le\frac{\binom{n}{t}\,(n-t-(t+1)Q)^2}{-2a(t+1)Q},\quad Q=\frac{K_{t+1}(a)}{K_t(a)},\ x_1^{(t+1)}<a<x_1^{(t)},\ a<d.\tag{3.11}$$
Choosing $t$ with $x_1^{(t)}\le d$ and $a$ with $Q=-1$:
$$M_{LP}(n,d)\le\binom{n}{t}\frac{(n+1)^2}{2a(t+1)}\quad(x_1^{(t)}\le d,\ t\le n/2).\tag{3.12}$$
Since $a\ge x_1^{(t+1)}$ and $x_1^{(t+1)}\ge1$ (A.18),
$$M(n,d)\le\binom{n}{t}\frac{(n+1)^2}{2(t+1)}\le\binom{n}{t}(n+1)^2.\tag{3.13}$$

<a id="pdf-abed77da6b7a-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.75 -->
**Proof step.** Choose $\tau$ with $1/2-\sqrt{\delta(1-\delta)}<\tau<1/2$, and integer sequences $d_n/n\to\delta$, $t_n/n\to\tau$. By (A.20), $x_1^{(t_n)}/n\le 1/2-\sqrt{\tau(1-\tau)}<\delta$, so (3.13) applies for large $n$. Then
$$\lim_{n\to\infty}\tfrac1n\log_2 M_{LP}(n,d_n)=\lim_{n\to\infty}\tfrac1n\log_2\binom{n}{t_n}=H_2(\tau).\tag{3.14}$$
With (2.5), $R_{LP}\le H_2(\tau)$ for all such $\tau$; by continuity $R_{LP}\le H_2\bigl(1/2-\sqrt{\delta(1-\delta)}\bigr)=g((1-2\delta)^2)$, which is (2.6). $\square$

<a id="pdf-abed77da6b7a-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.88 -->
**IV. Proof of (2.16).** Techniques mirror §III (using the $Q_j(i)$ of Appendix B); some computational details omitted. The first result is analogous to Theorem 1 with the same proof (omitted).

<a id="pdf-abed77da6b7a-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.75 -->
**Theorem 2.** If reals $\lambda_0,\lambda_1,\dots,\lambda_w$ satisfy
$$\lambda_0>0,\quad \lambda_j\ge0\ (j=1,\dots,w),\tag{4.1}$$
$$\sum_{j=0}^{w}\lambda_j Q_j(i)\le0\quad\text{for }i>d/2,\tag{4.2}$$
then
$$M_{LP}(n,d,w)\le\frac1{\lambda_0}\sum_{j=0}^{w}\lambda_j Q_j(0).\tag{4.3}$$

<a id="pdf-abed77da6b7a-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.60 -->
**Proof step.** For fixed $(n,d,w)$, choose integer $t$ ($1\le t\le w$) and real $a\in(0,w)$, and define
$$P^*(x)=Q_{t+1}(x)Q_t(a)-Q_t(x)Q_{t+1}(a).\tag{4.4}$$
By (B.14),
$$P^*(x)=(a-x)\,\frac{(n-2t)(n-2t-1)}{(t+1)(w-t)(w'-t)}\,\mu_t\sum_{k=0}^{t}\frac{Q_k(x)Q_k(a)}{\mu_k},\quad w'=n-w,\tag{4.5}$$
with constants $\mu_k$ from (B.1). Define $P(x)=P^*(x)^2/(a-x)$ (4.6) — footnote 9: since this may exceed degree $w$, take the unique degree-$\le w$ polynomial agreeing at $x=0,1,\dots,w$. Equation (4.7) writes $P(x)$ as a nonnegative-coefficient sum of products of $Q_j$.

<a id="pdf-abed77da6b7a-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.90 -->
**Proof step.** Each $Q_j(x)$ has $j$ distinct real zeros in $(0,w)$; least zero $x_1^{(j)}$ with $x_1^{(t+1)}<x_1^{(t)}$ (B.16). Choose
$$x_1^{(t+1)}<a<x_1^{(t)}.\tag{4.8}$$
Since $Q_j(0)=\mu_j>0$ (B.10), $Q_j(a)>0$ for $j\le t$ and $Q_{t+1}(a)<0$; by (B.17),(B.18) $P(x)=\sum_{j=0}^{w}\lambda_j Q_j(x)$ with $\lambda_j\ge0$. From (4.6) $P(x)\le0$ for $x>a$; assuming $a\le d/2$, $P(x)\le0$ for $x\ge d/2$, so Theorem 2 gives $M_{LP}(n,d,w)\le P(0)/\lambda_0$. Assuming further $x_1^{(t)}\le d/2$ and $a\in(x_1^{(t+1)},x_1^{(t)})$ with $Q_{t+1}(a)/Q_t(a)=-1$, one computes
$$P(0)=\frac1a\,Q_t(a)^2\binom{n}{t}^2\Bigl[\frac{n^2-(2t-1)n-2t}{(n-t+1)(t+1)}\Bigr]^2\tag{4.9}$$
and, via $\lambda_0=\int P(x)\,d\beta(x)$ (B.14) with orthogonality (B.13),
$$\lambda_0=\mu_t\,\frac{(n-2t)(n-2t-1)}{(t+1)(w-t)(w'-t)}\,Q_t(a)^2.\tag{4.10}$$
Recalling $x_1^{(t+1)}<a$, the results are then combined (continued on the next page).

<a id="pdf-abed77da6b7a-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
**Bound (4.11).**
$$M_{LP}(n,d,w)\le\binom{n}{t}\frac{(n^2-(2t-1)n-2t)^2(w-t)(w'-t)}{x_1^{(t+1)}(t+1)(n-t+1)(n-2t-1)(n-2t)(n-2t+1)},$$
where $w'=n-w$ and $t$ is a free parameter, valid provided $x_1^{(t)}\le d/2$.

<a id="pdf-abed77da6b7a-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.70 -->
**Setup (4.12).** Take integer sequences (dₙ),(wₙ),(tₙ) with dₙ/n→δ, wₙ/n→ω(=α), tₙ/n→φ, and 0 ≤ φ < α < 1/2.

<a id="pdf-abed77da6b7a-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.60 -->
**Proof (asymptotics).** By (B.10)–(B.11) the Q-polynomial is positive at x=0 and, for large n, at x=1; any zero in (0,1) would force ≥2 zeros, impossible since (B.16) puts an integer between consecutive zeros — hence x₁ ≥ 1 (4.13) for large n. So the fraction in (4.11) is O(n⁶) and the bound is dominated by binom(n,tₙ). Since n⁻¹log₂binom(n,tₙ)→H₂(φ), combining (4.11) with (2.15) gives R_LP(δ,α) ≤ H₂(φ), provided x₁ < dₙ/2 for large n; by (B.21) this holds if ((α(1−α)−φ(1−φ))/(1−2φ)²)(1−2√(φ(1−φ))) ≤ δ/2.

<a id="pdf-abed77da6b7a-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.55 -->
**Bound (4.14a).** R_LP(δ) ≤ H₂(β), provided (4.14b): ((α(1−α)−β(1−β))/(1−2β)²)(1−2√(β(1−β))) ≤ δ/2.

<a id="pdf-abed77da6b7a-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.70 -->
**Case (4.15).** If α(1−α) ≤ δ/2 then (4.14b) holds with β=0 and R_LP(δ,α)=0.

<a id="pdf-abed77da6b7a-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.92 -->
**Proof ($\to$(2.16)).** Otherwise define $v,u$ by $v^2/4=\alpha(1-\alpha)$, $u^2/4=\beta(1-\beta)$; then (4.14b) becomes $(v^2-u^2)/(1+u)\le2\delta$. The smallest admissible $u$ is the unique positive root of $(v^2-u^2)/(1+u)=2\delta$, i.e. $u^2+2\delta u+2\delta=v^2$. Since $H_2(\beta)=g(u^2)$, this gives (4.16): $R_{LP}(\delta,\alpha)\le g(u^2)$ when $\alpha(1-\alpha)\ge\delta/2$; together with (4.15) this is the promised bound (2.16).

<a id="pdf-abed77da6b7a-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.90 -->
**Appendix A — Some Properties of Krawtchouk Polynomials.** Reference collection of properties of the polynomials K_j(x) defined in Section II.

<a id="pdf-abed77da6b7a-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.90 -->
**Definition (A.1).** K_j(x) = coefficient of y^j in (1−y)^x (1+y)^{n−x}.

<a id="pdf-abed77da6b7a-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.90 -->
**Formulas (A.2)–(A.3).** (A.2): $K_j(x)=\sum_{k=0}^{j}(-1)^k\binom{x}{k}\binom{n-x}{j-k}$. (A.3), from writing $(1-y)^x=(1+y-2y)^x$: $K_j(x)=\sum_{k=0}^{j}(-2)^k\binom{x}{k}\binom{n-k}{j-k}$.

<a id="pdf-abed77da6b7a-p007-b010"></a>
<!-- pdf-source: page=7; block=10; confidence=0.93 -->
**Values (A.4)–(A.9).** $K_0(x)=1$; $K_1(x)=-2x+n$; $K_2(x)=2x^2-2xn+(n^2-n)/2$; (A.7) leading term $K_j(x)=\frac{(-2)^j}{j!}x^j+\text{lower}$; (A.8) $K_j(0)=\binom{n}{j}$; (A.9) $K_j(1)=\frac{n-2j}{j}\binom{n-1}{j-1}$ for $j\ne0$.

<a id="pdf-abed77da6b7a-p007-b011"></a>
<!-- pdf-source: page=7; block=11; confidence=0.80 -->
**Reciprocity (A.10).** binom(n,i)K_j(i) = binom(n,j)K_i(j); follows because the coefficient of y^j z^i in (1+y+z−yz)^n is symmetric in y and z.

<a id="pdf-abed77da6b7a-p007-b012"></a>
<!-- pdf-source: page=7; block=12; confidence=0.65 -->
**Orthogonality (A.11)–(A.12).** With step function β(x) having jumps 2^{−n}binom(n,k) at x=k (k=0,…,n), used as Stieltjes integrator ∫P dβ = 2^{−n}Σ_k P(k)binom(n,k), the K_j are orthogonal: (A.11) ∫K_jK_k dβ = binom(n,j)δ_{jk}. Hence any P of degree ≤ n: (A.12) P(i)=Σ_{k=0}^n a_kK_k(i), with a_k = binom(n,k)^{-1}∫P dβ.

<a id="pdf-abed77da6b7a-p007-b013"></a>
<!-- pdf-source: page=7; block=13; confidence=0.75 -->
**Recurrence (A.13).** (j+1)K_{j+1}(x) − (n−2x)K_j(x) + (n−j+1)K_{j−1}(x) = 0.

<a id="pdf-abed77da6b7a-p007-b014"></a>
<!-- pdf-source: page=7; block=14; confidence=0.90 -->
**Acknowledgment.** Thanks to Philippe Delsarte, Andrew Odlyzko, and Neil Sloane. (Footnote: dependence on n is suppressed, written K_j^{(n)}(x) when needed.)

<a id="pdf-abed77da6b7a-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.75 -->
**Difference equation (A.14).** Transforming (A.13) via reciprocity (A.10): (n−i)K_j(i+1) − (n−2j)K_j(i) + iK_j(i−1) = 0.

<a id="pdf-abed77da6b7a-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.60 -->
**Christoffel–Darboux (A.15).** For polynomials P_k orthogonal wrt integrator α (∫P_iP_j dα = δ_{ij}ρ_j): Σ_{k=0}^j P_k(x)P_k(y)/ρ_k = (1/ρ_j)(L_j/L_{j+1})·(P_{j+1}(x)P_j(y) − P_j(x)P_{j+1}(y))/(x−y), where L_j is the leading coefficient of P_j.

<a id="pdf-abed77da6b7a-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.55 -->
**(A.16).** For the K_j, ρ_k=binom(n,k) (by A.11) and L_j/L_{j+1}=−(j+1)/2 (by A.7), so (A.15) reduces to an explicit formula in (K_{j+1}(x)K_j(y) − K_j(x)K_{j+1}(y))/(x−y).

<a id="pdf-abed77da6b7a-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.55 -->
**Zeros (A.17).** K_j has j distinct real zeros x_1^{(j)}<…<x_j^{(j)} in the open interval (0,n); zeros of K_j and K_{j+1} interlace: x_i^{(j+1)} < x_i^{(j)} < x_{i+1}^{(j+1)}, with x_0^{(j)}=0 and x_{j+1}=n. Each interval (x_i^{(j)},x_{i+1}^{(j)}) contains an integer (point of increase of β).

<a id="pdf-abed77da6b7a-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.70 -->
**(A.18).** x_1^{(j)} ≥ 1 if j < n/2 (since K_j(0)>0 by (A.8) and K_j(1)>0 by (A.9)).

<a id="pdf-abed77da6b7a-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.50 -->
**Product positivity (A.19).** K_i(x)K_j(x) = Σ_{k=0}^n a_kK_k(x) with a_k ≥ 0 (equality for x=0,…,n). Proof: K_i(x)K_j(x) is the coefficient of y^i z^j in (1−y)^x(1+y)^{n−x}(1−z)^x(1+z)^{n−x}; rewriting the product via (1+yz)^n and (y+z)/(1+yz) exhibits the coefficients as nonnegative. Here a_k is the number of weight-i vectors in V_n at distance j from a fixed weight-k vector.

<a id="pdf-abed77da6b7a-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.70 -->
**(A.20).** For (j_n) with j_n/n→τ∈[0,1], let x_1^{(j_n)} be the smallest zero of K_{j_n}. Then limsup_n x_1^{(j_n)}/n ≤ 1/2 − √(τ(1−τ)). (Remark: for τ≤1/2 the limit exists and equals this value; for τ≥1/2 it is 0. Only the upper bound is proved.)

<a id="pdf-abed77da6b7a-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.55 -->
**Proof of (A.20).** If false, for small fixed ε there is an infinite set of n with x_1^{(j_n)} ≥ n(r+ε)-scale, r=1/2−√(τ(1−τ)). Set i=i_n=⌊n(r+ε)⌋, j=j_n. Factoring K_j(x)=((−2)^j/j!)∏_k(x−x_k) and using i−x_k of order εn gives log(K_j(i±1)/K_j(i)) = ±Σ_k(i−x_k)^{-1}+O(n^{-1}), whence K_j(i+1)/K_j(i)=(K_j(i)/K_j(i−1))(1+O(n^{-1})). Substituting in (A.14) with ρ=K_j(i)/K_j(i−1) gives (iv): (n−i)ρ²(1+O(n^{-1})) − (n−2j)ρ + i = 0. Real ρ ⇒ discriminant ≥ 0: (n−2j)² − 4i(n−i) + O(n) ≥ 0, which by i/n→r+ε, j/n→τ and (1−2r)²=4r(1−r) reduces to (v): −ε(1−2r)+ε²+O(n^{-1}) ≥ 0. Choosing ε<1−2r makes (v) false for large n — contradiction. ∎

<a id="pdf-abed77da6b7a-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.85 -->
**Appendix B — Some Properties of the Q-Polynomials.** Properties of the numbers Q_j(i) from (2.13), mostly due to Delsarte; they depend on j, i, n, w, written Q_j^{n,w}(i).

<a id="pdf-abed77da6b7a-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.85 -->
**Definitions (B.1)–(B.7).** (B.1): $\mu_j=\binom{n}{j}-\binom{n}{j-1}=\binom{n}{j}\frac{n-2j+1}{n-j+1}$. (B.2): $v_i=\binom{w}{i}\binom{w'}{i}$, $w'=n-w$. (B.3): $Q_j(i)=\frac{\mu_j}{v_i}\cdot[\text{coefficient of }y^i z^i\text{ in }(1-yz)^j(1+y)^{w-j}(1+z)^{w'-j}]$. Expanding yields equivalent sums (B.4)–(B.5); the Krawtchouk-product form (B.6): $Q_j(i)=\frac{\mu_j}{2^j}\sum_{k=0}^{j}\frac{\binom{j}{k}}{\binom{w}{j-k}\binom{w'}{k}}K^{(w)}_{j-k}(i)K^{(w')}_k(i)$; and the Hahn / ${}_3F_2$ form (B.7): $Q_j(x)=\mu_j\cdot{}_3F_2(-j,-x,j-n-1;-w,-w';1)$. These show $Q_j(i)$ is a polynomial of degree $j$ in $i$, denoted $Q_j(x)$ or $Q_j^{n,w}(x)$.

<a id="pdf-abed77da6b7a-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.88 -->
**Values (B.8)–(B.12).** $Q_0(x)=1$; $Q_1(x)=(n-1)\bigl(1-\frac{nx}{ww'}\bigr)$; $Q_j(0)=\mu_j$; $Q_j(1)=\mu_j\bigl(1-\frac{j(n+1-j)}{ww'}\bigr)$; (B.12) leading term $Q_j(x)=\frac{(-1)^j}{j!}\cdot\frac{\binom{n}{w}}{\binom{n-2j}{w-j}}\,x^j+\text{lower degree terms}$.

<a id="pdf-abed77da6b7a-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.55 -->
**Orthogonality (B.13).** Delsarte: the Q_j are orthogonal wrt the Stieltjes integrator β(x) with jumps binom(w,i)binom(w′,i)/binom(n,i) at i=0,…,w: ∫Q_j(x)Q_k(x)dβ(x) = μ_j δ_{jk}.

<a id="pdf-abed77da6b7a-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.60 -->
**Expansion (B.14).** Any P of degree ≤ w: P(i)=Σ_{j=0}^w a_j Q_j(i) (i=0,…,w), with a_j = μ_j^{-1}∫P(x)Q_j(x)dβ(x).

<a id="pdf-abed77da6b7a-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.50 -->
**Christoffel–Darboux (B.15).** By the general orthogonal-polynomial theory, (Q_{j+1}(x)Q_j(y) − Q_j(x)Q_{j+1}(y))/(x−y) is proportional to Σ_{k=0}^j Q_k(x)Q_k(y)/μ_k.

<a id="pdf-abed77da6b7a-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.55 -->
**Zeros (B.16).** Each Q_j has j distinct real zeros x_1^{(j)}<…<x_j^{(j)} in the open interval (0,w); zeros of Q_j and Q_{j+1} interlace: x_i^{(j+1)} < x_i^{(j)} < x_{i+1}^{(j+1)}, with x_0^{(j)}=0, x_{j+1}=w; each interval (x_i^{(j)},x_{i+1}^{(j)}) contains an integer (point of increase of β).

<a id="pdf-abed77da6b7a-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.55 -->
**Product (B.17)–(B.19).** Q_j(i)Q_l(i)=Σ_{k=0}^w q_{jl}^{(k)}Q_k(i) (B.17); by Delsarte (lemma 2.4), q_{jl}^{(k)}=μ_k^{-1}∫Q_j Q_l Q_k dβ (B.18); and q_{jl}^{(k)} ≥ 0 for all j,k,l∈{0,…,w} (B.19).

<a id="pdf-abed77da6b7a-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.85 -->
**Difference equation (B.20).** $(w-i)(w'-i)Q_j(i+1)-\bigl(ww'-j(n-2i)-j(n+1-i)\bigr)Q_j(i)+i^2Q_j(i-1)=0.$

<a id="pdf-abed77da6b7a-p009-b009"></a>
<!-- pdf-source: page=9; block=9; confidence=0.90 -->
**(B.21).** For $(w_n),(j_n)$ with $w_n/n\to\alpha$, $j_n/n\to\beta$ and $\beta\le\alpha\le1/2$, let $x_1(j_n,w_n,n)$ be the smallest zero of $Q_{j_n}^{(n,w_n)}$. Then $\limsup_n x_1(j_n,w_n,n)/n\le\dfrac{\alpha(1-\alpha)-\beta(1-\beta)}{(1-2\beta)^2}\bigl(1-2\sqrt{\beta(1-\beta)}\bigr)$. (Remark: the limit exists and equals the RHS for all $\beta\le\alpha\le1/2$; proof omitted, not needed for (2.15).)

<a id="pdf-abed77da6b7a-p009-b010"></a>
<!-- pdf-source: page=9; block=10; confidence=0.55 -->
**Proof of (B.21).** If false, for small fixed ε there is an infinite sequence of n with x_1^{(j_n,w_n,n)} ≥ n(F+2ε), F the RHS of (B.21). For a fixed such n set i=i_n, j=j_n, w=w_n, w′=n−w_n, and write Q_j^{n,w}(x)=L_j(x−x_1)…(x−x_j). [Argument continues on the next (unsupplied) page.]

<a id="pdf-abed77da6b7a-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
**Proof (cont.).** But $i\le n(F+\epsilon)$ and $x_1^{(j)}\ge n(F+2\epsilon)$, so $|i-x_k^{(j)}|\ge\epsilon n$ for $k=1,2,\dots,j$. Thus
$$\log\!\Bigl(1\pm\frac{1}{i-x_k^{(j)}}\Bigr)=\frac{\pm1}{i-x_k^{(j)}}+O(n^{-2}).\tag{ii}$$
Combining (i) and (ii),
$$\log\frac{Q_j(i\pm1)}{Q_j(i)}=\pm\sum_{k=1}^{j}\frac{1}{i-x_k^{(j)}}+O(n^{-1}).\tag{iii}$$

<a id="pdf-abed77da6b7a-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.70 -->
**Proof (cont.).** Subtracting the "+" equation from the "$-$" equation in (iii): $\log\frac{Q_j(i+1)}{Q_j(i)}-\log\frac{Q_j(i)}{Q_j(i-1)}=O(n^{-1})$ (iv); hence $\dfrac{Q_j(i+1)}{Q_j(i)}=\dfrac{Q_j(i)}{Q_j(i-1)}\,\{1+O(n^{-1})\}$ (v).

<a id="pdf-abed77da6b7a-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.85 -->
**Proof (cont.).** The difference equation (B.20) is written as
$$(w-i)(w'-i)\frac{Q_j(i+1)}{Q_j(i)}\cdot\frac{Q_j(i)}{Q_j(i-1)}-\bigl(ww'-j(n-2i)-j(n+1-i)\bigr)\frac{Q_j(i)}{Q_j(i-1)}+i^2=0\tag{vi}$$
Denoting $\rho=Q_j(i)/Q_j(i-1)$ and using (v):
$$(w-i)(w'-i)\rho^2\bigl(1+O(n^{-1})\bigr)-\bigl(ww'-i(n-2i)-j(n+1-j)\bigr)\rho+i^2=0\tag{vii}$$

<a id="pdf-abed77da6b7a-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.92 -->
**Proof (cont.).** Since $\rho$ is real, the discriminant of (vii) must be $\ge0$:
$$\bigl(ww'-j(n-2i)-j(n+1-i)\bigr)^2-4(w-i)(w'-i)i^2+O(n^{3})\ge0.\tag{viii}$$
Despite appearances, this is only quadratic in $i$ and rearranges to
$$(n-2j)^2 i^2-2n(w-j)(w'-j)i+(w-j)^2(w'-j)^2+O(n^{3})\ge0.\tag{ix}$$

<a id="pdf-abed77da6b7a-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.92 -->
**Proof (cont.).** The two zeroes of $(n-2j)^2 i^2-2n(w-j)(w'-j)i+(w-j)^2(w'-j)^2$ are
$$i_1,i_2=\frac{(w-j)(w'-j)}{(n-2j)^2}\bigl(n\pm2\sqrt{j(n-j)}\bigr).\tag{x}$$
With $w/n\to\alpha$, $j/n\to\beta$, for large $n$:
$$\frac{i_1}{n},\frac{i_2}{n}\to\frac{\alpha(1-\alpha)-\beta(1-\beta)}{(1-2\beta)^2}\bigl(1\pm2\sqrt{\beta(1-\beta)}\bigr).\tag{xi}$$
Hence, if $\epsilon$ is selected so that $i=i_n=\lfloor n(F+\epsilon)\rfloor$ lies between $i_1$ and $i_2$, the discriminant (ix) will for large $n$ behave like a negative constant times $n^4$ — a contradiction, completing the proof of (B.21). $\blacksquare$

<a id="pdf-abed77da6b7a-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.95 -->
### References

<a id="pdf-abed77da6b7a-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.85 -->
Bibliography (8 items): [1] R. Askey, *Orthogonal Polynomials and Special Functions*, SIAM Regional Conf. Lectures in Applied Math. vol. 21, SIAM, 1975. [2] E. R. Berlekamp, *Algebraic Coding Theory*, McGraw-Hill, 1968. [3] P. Delsarte, *An Algebraic Approach to the Association Schemes of Coding Theory*, Philips Research Reports Supplements no. 10, 1973. [4] S. Karlin, J. L. McGregor, "The Hahn polynomials, formulas, and an application," *Scripta Mathematica* 26, pp. 33–46, 1961. [5] V. I. Levenshtein, "On the minimal redundancy of binary error-correcting codes" (Russian), *Problemy Peredachi Informatsii* 10, pp. 26–42, 1974 (Engl. transl. *Information and Control* 28, pp. 268–291, 1975). [6] V. M. Sidelnikov, "Upper bounds on the cardinality of a binary code with a given minimum distance" (Russian), *Problemy Peredachi Informatsii* 10, pp. 43–51, 1974 (Engl. transl. *Information and Control* 28, pp. 292–303, 1975). [7] G. Szegő, *Orthogonal Polynomials*, Amer. Math. Soc., 1939. [8] L. R. Welch, R. J. McEliece, H. Rumsey Jr., "A low-rate improvement on the Elias bound," *IEEE Trans. Inform. Theory* IT-20, pp. 676–678, Sept. 1974.
