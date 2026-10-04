<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 3f7c8a3e445e912dda75f3d0d75bfe87a90c3aed5d460a0aa56d066ce7d1ef42 -->

<a id="pdf-3f7c8a3e445e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Elementary Proof for Sion's Minimax Theorem

H. Komiya. Kodai Math. J. 11 (1988), 5–7. Received June 19, 1987.

<a id="pdf-3f7c8a3e445e-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
## 1. Introduction

Among generalizations of von Neumann's minimax theorem, this note concerns the one due to Sion [2].

<a id="pdf-3f7c8a3e445e-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
**Sion's Minimax Theorem.** Let $X$ be a compact convex subset of a linear topological space and $Y$ a convex subset of a linear topological space. Let $f$ be a real-valued function on $X\times Y$ such that:

- (i) $f(x,\cdot)$ is upper semicontinuous and quasi-concave on $Y$ for each $x\in X$;
- (ii) $f(\cdot,y)$ is lower semicontinuous and quasi-convex on $X$ for each $y\in Y$.

Then $\min_{x\in X}\sup_{y\in Y} f(x,y)=\sup_{y\in Y}\min_{x\in X} f(x,y)$.

<a id="pdf-3f7c8a3e445e-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
Sion's original proof used the Knaster–Kuratowski–Mazurkiewicz (KKM) theorem; alternative proofs by Fan [1] (sets with convex sections) and Takahashi [3] (Fan–Browder fixed point theorem) also rely on topological tools such as the Brouwer fixed point theorem or KKM. This note gives an elementary proof.

<a id="pdf-3f7c8a3e445e-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
## 2. Proof for the theorem

The method is inspired by the proof of [4, Theorem 2].

<a id="pdf-3f7c8a3e445e-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.92 -->
**Lemma 1.** Under the assumptions of Sion's theorem, for any $y_1,y_2\in Y$ and any real number $a$ with $a<\min_{x\in X}\max\big(f(x,y_1),f(x,y_2)\big)$, there exists $y_0\in Y$ with $a<\min_{x\in X} f(x,y_0)$.

<a id="pdf-3f7c8a3e445e-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.97 -->
**Proof.** Deny the conclusion and suppose that $\alpha\ge\min_{x\in X} f(x,y)$ for all $y\in Y$. Choose $\beta$ with $\alpha<\beta<\min_{x\in X}\max\big(f(x,y_1),f(x,y_2)\big)$.

<a id="pdf-3f7c8a3e445e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
**Proof (continued).** Let $[y_1,y_2]$ be the segment joining $y_1,y_2$. For each $z\in[y_1,y_2]$ define $C_z=\{x\in X: f(x,z)\le\alpha\}$ and $C'_z=\{x\in X: f(x,z)\le\beta\}$; set $A=C'_{y_1}$, $B=C'_{y_2}$. Each of $C_z,C'_z,A,B$ is nonempty and closed (lower semicontinuity of $f(\cdot,z)$), and $A\cap B=\varnothing$. Quasi-concavity of $f(x,\cdot)$ gives $f(x,z)\ge\min(f(x,y_1),f(x,y_2))$ for $x\in X$ and $z\in[y_1,y_2]$, whence $C'_z\subset A\cup B$; quasi-convexity of $f(\cdot,z)$ makes $C'_z$ convex, hence $C'_z$ is connected, so $C_z\subset C'_z\subset A$ or $C_z\subset C'_z\subset B$. Define $I=\{z\in[y_1,y_2]:C_z\subset A\}$ and $J=\{z\in[y_1,y_2]:C_z\subset B\}$; both are nonempty, $I\cap J=\varnothing$, and $I\cup J=[y_1,y_2]$. Let $\{z_n\}$ be a sequence in $I$ with $z_n\to z\in[y_1,y_2]$; for any $x\in C_z$, $f(x,z)<\beta$, so upper semicontinuity of $f(x,\cdot)$ gives $\varlimsup f(x,z_n)<\beta$, whence some $f(x,z_m)<\beta$, i.e. $x\in C'_{z_m}$, and $C'_{z_m}\subset A$ since $C_{z_m}\subset A$, so $x\in A$; thus $z\in I$ and $I$ is closed in $[y_1,y_2]$. Similarly $J$ is closed. The closedness of both $I$ and $J$ contradicts the connectedness of $[y_1,y_2]$. $\square$

<a id="pdf-3f7c8a3e445e-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
**Lemma 2.** Under the assumptions of Sion's theorem, for any finite $y_1,\dots,y_n\in Y$ and any real number $a$ with $a<\min_{x\in X}\max_i f(x,y_i)$, there exists $y_0\in Y$ with $a<\min_{x\in X} f(x,y_0)$.

<a id="pdf-3f7c8a3e445e-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Proof.** Induction on $n$; trivial for $n=1$. Let $X'=\{x\in X: f(x,y_n)\le\alpha\}$, which is compact and convex; if $X'$ is empty, take $y_0=y_n$. Otherwise $\alpha<\min_{x\in X'}\max_{1\le i\le n-1} f(x,y_i)$. Applying the induction hypothesis to $f$ restricted to $X'\times Y$ yields $y'_0$ with $\alpha<\min_{x\in X'} f(x,y'_0)$. Hence $\alpha<\min_{x\in X}\max\big(f(x,y'_0),f(x,y_n)\big)$, and Lemma 1 gives $y_0\in Y$ with $\alpha<\min_{x\in X} f(x,y_0)$. $\square$

<a id="pdf-3f7c8a3e445e-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.86 -->
**Proof of the theorem.** The inequality $\sup_{y\in Y}\min_{x\in X} f(x,y)\le\min_{x\in X}\sup_{y\in Y} f(x,y)$ is obvious. For the reverse, let $a$ be any real number with $a<\min_{x\in X}\sup_{y\in Y} f(x,y)$, and set $X_y=\{x\in X: f(x,y)\le a\}$ for each $y\in Y$. Then $\bigcap_{y\in Y} X_y$ is empty, so there exist finitely many $y_1,\dots,y_n\in Y$ such that (continued next page)…

<a id="pdf-3f7c8a3e445e-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.88 -->
**Proof (continued).** …$\bigcap_i X_{y_i}$ is empty, i.e. $a<\min_{x\in X}\max_i f(x,y_i)$. By Lemma 2 there is $y_0$ with $a<\min_{x\in X} f(x,y_0)$, hence $a<\sup_{y\in Y}\min_{x\in X} f(x,y)$. Therefore $\min_{x\in X}\sup_{y\in Y} f(x,y)\le\sup_{y\in Y}\min_{x\in X} f(x,y)$, completing the proof. $\square$

<a id="pdf-3f7c8a3e445e-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.96 -->
**Acknowledgement.** The author thanks Professor W. Takahashi for his advice.

<a id="pdf-3f7c8a3e445e-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->
**References.**

- [1] K. Fan, *Sur un théorème minimax*, C.R. Acad. Sci. Paris 259 (1964), 3925–3928.
- [2] M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958), 171–176.
- [3] W. Takahashi, *Nonlinear variational inequalities and fixed point theorems*, J. Math. Soc. Japan 28 (1976), 168–181.
- [4] F. Terkelsen, *Some minimax theorems*, Math. Scand. 31 (1972), 405–413.
