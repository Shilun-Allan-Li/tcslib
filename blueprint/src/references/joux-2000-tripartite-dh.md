<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# A One Round Protocol for Tripartite Diffie–Hellman

Antoine Joux. In W. Bosma (ed.), *Algorithmic Number Theory, ANTS-IV*, LNCS 1838,
pp. 385–393, Springer, 2000 (publisher copy, 9 pages; tag `Jou00`).

**Scope.** Only the passages that the pairing campaign uses are transcribed (DW-7; pairing
ruling Q12): the bilinearity and non-degeneracy of the pairings at the end of §2, the protocol
of §3, and the security discussion of §5. The PDF is not committed. Anchors use the physical
PDF page (`p003` is printed page 387, `p004` is 388, `p007` is 391, `p008` is 392). The scoped
raw extraction is `joux-2000-tripartite-dh.raw.md`. Mathematics is set in LaTeX; the wording
is the paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-dd423b93a7e2-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Section 2, the Weil pairing (p. 387).** Using these notions, we can now define the Weil
pairing: it is a bilinear function from the torsion group $E[n]$ to the multiplicative group
$\mu_n$ of $n$-th roots of unity in some extension of $\mathbb F_p$, say $\mathbb F_{p^k}$.
Given two $n$-torsion points $P$ and $Q$, we compute their pairing $e_n(P,Q)$ by finding two
functions $f_P$ and $f_Q$ such that $\mathrm{div}(f_P)=n(P)-n(O)$ and
$\mathrm{div}(f_Q)=n(Q)-n(O)$, and by evaluating:

$$
e_n(P,Q)=f_P(Q)/f_Q(P).
$$

This pairing $e_n : E[n]\times E[n]\to\mu_n$ is bilinear and non-degenerate. This means that
$e_n(aP,bQ)=e_n(P,Q)^{ab}$ and that for some values of $P$ and $Q$, we have
$e_n(P,Q)\neq 1$. We can easily see that given a point $X$ "independent" from $P$ and $Q$, we
can reduce the discrete logarithm problem $Q=\lambda P$ on the elliptic curve to the discrete
logarithm problem $e_n(Q,X)=e_n(P,X)^{\lambda}$ in $\mathbb F_{p^k}$.

<a id="pdf-dd423b93a7e2-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->

**Section 2, the Tate pairing (p. 387).** The variant of the Tate pairing described in [3] is
more complicated, since it operates on divisors instead of points. The Tate pairing operates
on $n$-fold divisors, i.e. divisors $D$ such that $nD$ is principal, it takes values in
$\mu_n$ and it is bilinear and non-degenerate. Given two $n$-fold divisors $D_1$ and $D_2$
defined over an extension $\mathbb F_{p^k}$ that contains the $n$-th roots of unity, we find
$f_{D_1}$ and $f_{D_2}$ such that $\mathrm{div}(f_{D_1})=nD_1$ and
$\mathrm{div}(f_{D_2})=nD_2$. The Tate pairing of $D_1$ and $D_2$ is then defined as:

$$
t_n(D_1,D_2)=f_{D_1}(D_2)^{(p^k-1)/n}.
$$

This pairing is also bilinear and non-degenerate. Moreover, for the purpose of discrete
logarithm reduction, the Tate pairing $t_n(D_1,D_2)$ can easily be transformed into a pairing
that involves points. One can simply fix two points $R$ and $S$, and remark that
$t_n((\lambda P)-(O),(R)-(S))=t_n((P)-(O),(R)-(S))^{\lambda}$.

For more details about the properties and definitions of the Weil and Tate pairing, we refer
the reader to [8,3,4].

<a id="pdf-dd423b93a7e2-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.95 -->

## 3 A Tripartite Diffie–Hellman Protocol

**Section 3, the protocol idea and $F_W$ (p. 387).** In this section, we want to build an
analog of the Diffie–Hellman protocol, that involves three participants $A$, $B$ and $C$,
requires a single pass of communications and allows the construction of a common secret
$K_{A,B,C}$. By a single pass of communication, we mean that each participant is allowed to
talk once and broadcast some data to the other two. The main idea is as in ordinary
Diffie–Hellman, we start from some elliptic curve $E$ and some point $P$. Then $A$, $B$ and
$C$ each chose a random number ($a$, $b$ or $c$) and they respectively compute $P_A=aP$,
$P_B=bP$ and $P_C=cP$ and broadcast these values. Then they respectively compute
$F(a,P_B,P_C)$, $F(b,P_A,P_C)$ and $F(c,P_A,P_B)$, where the function $F$ is chosen in a way
that ensures that these numbers will be equal and that this common value $K_{A,B,C}$ will be
hard to compute given $P_A$, $P_B$ and $P_C$. The problem now is to find such an $F$.

Using the Weil pairing, it is seems very easy to define such an $F$ using the following
formula:

$$
F_W(x,P,Q)=e_n(P,Q)^{x}.
$$

<a id="pdf-dd423b93a7e2-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Section 3, one point fails, two points and $F_T$ (p. 388).** With this definition, one can
easily check that:

$$
F_W(a,P_B,P_C)=F_W(b,P_A,P_C)=F_W(c,P_A,P_B)=F_W(1,P,P)^{abc}.
$$

However, this function is not satisfying because $e_n(P,P)=1$ and thus $K_{A,B,C}$ is a
constant. Nevertheless, the basic idea is quite sound and can in fact be implemented if we use
two independent points $P$, and $Q$ and if we have the three participants compute and
broadcast $(P_A,Q_A)$, $(P_B,Q_B)$ and $(P_C,Q_C)$. Then $A$, $B$ and $C$ can respectively
compute $F_W(a,P_B,Q_C)=F_W(a,Q_B,P_C)$, $F_W(b,P_A,Q_C)=F_W(b,Q_A,P_C)$ and
$F_W(c,P_A,Q_B)=F_W(c,Q_A,P_B)$. Moreover, all these values are equal and thanks to the
independence of $P$ and $Q$, they are not constant.

Moreover, using two points $P$ and $Q$, it is easy to use the Tate pairing instead of the Weil
pairing, and to define another function $F$ as:

$$
F_T(x,D_1,D_2)=t_n(D_1,D_2)^{x}.
$$

Then $A$, $B$ and $C$ can respectively compute:

$$
\begin{aligned}
F_T(a,(P_B)-(Q_B),(P_C+Q_C)-(O)) &= F_T(a,(P_C)-(Q_C),(P_B+Q_B)-(O)),\\
F_T(b,(P_A)-(Q_A),(P_C+Q_C)-(O)) &= F_T(b,(P_C)-(Q_C),(P_A+Q_A)-(O)),\\
F_T(c,(P_B)-(Q_B),(P_A+Q_A)-(O)) &= F_T(c,(P_A)-(Q_A),(P_B+Q_B)-(O)).
\end{aligned}
$$

Because of the bilinearity of the pairing, all these numbers are equal and because of the
non-degeneracy, their common value

$$
F_T(1,(P)-(Q),(P+Q)-(O))^{abc}
$$

is not independent from the choice of $a$, $b$ and $c$.

<a id="pdf-dd423b93a7e2-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

**Section 3, summary of the protocol (p. 388).** Since $F_T$ is based on the Tate pairing, it
will be faster to evaluate then $F_W$ (see the general remark about the efficiency of the Tate
pairing versus that of the Weil pairing in [4]). Finally, our tripartite Diffie–Hellman
protocol can be summarized as follows:

| Alice | Bob | Charlie |
|---|---|---|
| Choose $a$ | Choose $b$ | Choose $c$ |
| Compute $(P_A,Q_A)$ | Compute $(P_B,Q_B)$ | Compute $(P_C,Q_C)$ |

Broadcast $P_A,P_B,P_C$ and $Q_A,Q_B,Q_C$. Compute the common key as:

| Alice | Bob | Charlie |
|---|---|---|
| $F_T(a,(P_B)-(Q_B),(P_C+Q_C)-(O))$ | $F_T(b,(P_A)-(Q_A),(P_C+Q_C)-(O))$ | $F_T(c,(P_B)-(Q_B),(P_A+Q_A)-(O))$ |

*Transcription note.* In the printed table the three key formulas are staggered on three
lines, one per participant; they are set here as one row.

<a id="pdf-dd423b93a7e2-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

## 5 Security Issues

**Section 5, security issues (pp. 391–392).** Clearly in order to be secure the tripartite
Diffie–Hellman described here requires the discrete logarithm on the chosen elliptic curve to
be hard, and the discrete logarithm in the finite field $\mathbb F_{p^k}$ to be hard. Since we
placed ourselves in the cases where either the MOV or the FR reduction applies, the hardness of
the elliptic curve discrete log implies the hardness of the finite field discrete log and we
can remove the second condition. This is a simple restatement of the fact that when the finite
field discrete log, then to solve the elliptic curve discrete log we simply transport the
problem in the finite field using the pairing and then solve the problem in the finite field.
However, it is not known whether the elliptic curve discrete logarithm on a weak curve is as
hard as the discrete logarithm in the corresponding finite field (in the sense of the MOV or FR
reduction). In fact, this is a very interesting open problem. Moreover, as in the
Diffie–Hellman case this is not the whole story, some Diffie–Hellman like problem and
Diffie–Hellman like decision problem should be hard in order to get security.

*Transcription note.* The page break (p. 391 to p. 392) falls after "the hardness of the
elliptic"; the passage is kept as one block.

<a id="pdf-dd423b93a7e2-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 5, the decision problem on pairing curves (p. 392).** Quite amusingly, we should
note that on curves where either the MOV or FR reduction applies, the usual Diffie–Hellman
decision problem is mostly easy. Remember that the usual Diffie–Hellman problem is given a
quadruple $(g,g^a,g^b,g^c)$ to decide whether $c=ab$. This problem can also be expressed with
the following formulation which is slightly different. Given a quadruple $(g,g^a,h,h^b)$,
decide whether $a=b$. Now on an elliptic curve where the MOV reduction applies, we can easily
test for a quadruple $(P,aP,Q,bQ)$ whether $a=b$, it suffices to compute $e_n(aP,Q)$ and
$e_n(P,bQ)$ and to compare them. This test works as soon as $P$ and $Q$ are independent (i.e.
when $e_n(P,Q)\neq 1$). Of course, in the FR case, such a test also exists. More precisely, one
can test for the equality of $t_n((aP)-(O),(\lambda Q)-(Q))$ and
$t_n((P)-(O),(\lambda bQ)-(bQ))$, where $\lambda$ is essentially any constant number (some
values of $\lambda$ are excluded, for example $\lambda=1$ is not allowed). Note than when $P$
and $Q$ are not independent, the test usually doesn't work, thus some cases of the usual
Diffie–Hellman decision problem are still hard on these elliptic curves.

With the current knowledge of elliptic curves, we believe that this system is secure in
practice as soon as the discrete logarithm in $\mathbb F_{p^k}$ is hard. For the supersingular
case ($k=2$), we think that $p$ should be a 512 bits prime. In the trace 2 case ($k=1$), we
recommend to choose a 1024 bits prime. Moreover, the usual precautions should be taken, i.e.
some large prime $q$ should divide the order of the elliptic curve, all the points involved in
the computation should be of order $q$, and we should use the pairing $e_q$ or $t_q$.
