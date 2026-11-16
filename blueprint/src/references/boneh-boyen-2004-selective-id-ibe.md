<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles

Dan Boneh and Xavier Boyen. Cryptology ePrint Archive, Report 2004/172, full version dated
December 2004 (20 pages; tag `BB04`); extended abstract in *EUROCRYPT 2004*, LNCS 3027,
pp. 223–238. The ePrint numbering is used throughout.

**Scope.** Only the passages that the pairing campaign uses are transcribed (DW-7; pairing
ruling Q12): §2.1–§3.1 (IBE and HIBE, the selective-identity game, Definitions 2.1–2.2,
bilinear groups, BDH and Decision BDH, Definition 3.1), §4.1–§4.2 (the HIBE construction and
Theorem 4.1 with its proof) and §4.4 (arbitrary identities). The PDF is not committed. Physical
and printed pages coincide. The scoped raw extraction is
`boneh-boyen-2004-selective-id-ibe.raw.md`. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-63c1c7b0817f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

## 2 Preliminaries

**Section 2, opening (p. 2).** Before presenting our results we briefly review the definition
of security for an IBE system. We also review the definition of groups equipped with a
bilinear map.

<a id="pdf-63c1c7b0817f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Section 2.1, IBE and HIBE systems (pp. 2–3).** Recall that an Identity Based Encryption
system (IBE) consists of four algorithms [Sha84, BF01]: **Setup**, **KeyGen**, **Encrypt**,
**Decrypt**. The **Setup** algorithm generates system parameters, denoted by *params*, and a
master key *master-key*. The **KeyGen** algorithm uses the master key to generate the private
key corresponding to a given identity. The encryption algorithm encrypts messages for a given
identity (using the system parameters) and the decryption algorithm decrypts ciphertexts using
the private key. In a Hierarchical IBE [HL02, GS02] identities are vectors. A vector of
dimension $\ell$ represents an identity at depth $\ell$. Algorithm **KeyGen** takes as input
an identity $\mathrm{ID}=(I_1,\dots,I_\ell)$ at depth $\ell$ and the private key
$d_{\mathrm{ID}|_{\ell-1}}$ of the parent identity
$\mathrm{ID}|_{\ell-1}=(I_1,\dots,I_{\ell-1})$ at depth $\ell-1$. It outputs the private key
$d_{\mathrm{ID}}$ for identity $\mathrm{ID}$. We refer to the master-key as the private key at
depth $0$ and note that an IBE system is an HIBE where all identities are at depth $1$.

<a id="pdf-63c1c7b0817f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Section 2.1, the selective-identity game (p. 3).** Boneh and Franklin [BF01, BF03] define
chosen ciphertext security for IBE systems under a chosen identity attack. In their model the
adversary is allowed to adaptively chose the public key it wishes to attack (the public key on
which it will be challenged). Canetti, Halevi, and Katz [CHK03, CHK04] define a weaker notion of
security in which the adversary commits ahead of time to the public key it will attack. We
refer to this notion as *selective identity, chosen ciphertext secure IBE* (IND-sID-CCA). More
precisely, selective identity IBE and HIBE security is defined using the following game:

- **Init:** The adversary outputs an identity $\mathrm{ID}^*$ where it wishes to be
  challenged.
- **Setup:** The challenger runs the **Setup** algorithm. It gives the adversary the resulting
  system parameters *params*. It keeps the *master-key* to itself.
- **Phase 1:** The adversary issues queries $q_1,\dots,q_m$ where query $q_i$ is one of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds by running
    algorithm **KeyGen** to generate the private key $d_i$ corresponding to the public key
    $\langle\mathrm{ID}_i\rangle$. It sends $d_i$ to the adversary.
  - Decryption query $\langle C_i\rangle$ for identity $\mathrm{ID}^*$ or any prefix of
    $\mathrm{ID}^*$. The challenger responds by running algorithm **KeyGen** to generate the
    private key $d$ corresponding to $\mathrm{ID}^*$ (or the relevant prefix thereof as
    requested). It then runs algorithm **Decrypt** to decrypt the ciphertext $C_i$ using the
    private key $d$. It sends the resulting plaintext to the adversary.

  These queries may be asked adaptively, that is, each query $q_i$ may depend on the replies
  to $q_1,\dots,q_{i-1}$.
- **Challenge:** Once the adversary decides that Phase 1 is over it outputs two equal length
  plaintexts $M_0,M_1\in\mathcal M$ on which it wishes to be challenged. The challenger picks a
  random bit $b\in\{0,1\}$ and sets the challenge ciphertext to
  $C=\mathbf{Encrypt}(\textit{params},\mathrm{ID}^*,M_b)$. It sends $C$ as the challenge to
  the adversary.
- **Phase 2:** The adversary issues additional queries $q_{m+1},\dots,q_n$ where $q_i$ is one
  of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds as in Phase 1.
  - Decryption query $\langle C_i\rangle\neq\langle C\rangle$ for $\mathrm{ID}^*$ or any prefix
    of $\mathrm{ID}^*$. The challenger responds as in Phase 1.

  These queries may be asked adaptively as in Phase 1.
- **Guess:** Finally, the adversary outputs a guess $b'\in\{0,1\}$. The adversary wins if
  $b=b'$.

We refer to such an adversary $\mathcal A$ as an IND-sID-CCA adversary. We define the
advantage of the adversary $\mathcal A$ in attacking the scheme $\mathcal E$ as

$$
\mathrm{Adv}_{\mathcal E,\mathcal A}=\left|\Pr[b=b']-\frac12\right|
$$

The probability is over the random bits used by the challenger and the adversary.

*Transcription note.* The `-layout` extraction drops the vertical bars; the page image
(checked at 150 dpi) shows the absolute value $\left|\Pr[b=b']-\tfrac12\right|$.

<a id="pdf-63c1c7b0817f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Definition 2.1.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$-selective identity, adaptive chosen ciphertext secure if for any
$t$-time IND-sID-CCA adversary $\mathcal A$ that makes at most $q_{ID}$ chosen private key
queries and at most $q_C$ chosen decryption queries we have that
$\mathrm{Adv}_{\mathcal E,\mathcal A}<\epsilon$. As shorthand, we say that $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$ IND-sID-CCA secure.

**Semantic Security.** As usual, we define selective identity, chosen plaintext security for
an IBE system as in the preceding game, except that the adversary is not allowed to issue any
decryption queries. The adversary may still issue adaptive private key queries.

<a id="pdf-63c1c7b0817f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

**Definition 2.2.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},\epsilon)$-selective identity, chosen plaintext secure if $\mathcal E$ is
$(t,q_{ID},0,\epsilon)$-selective identity, chosen ciphertext secure. As shorthand, we say that
$\mathcal E$ is $(t,q_{ID},\epsilon)$ IND-sID-CPA secure.

<a id="pdf-63c1c7b0817f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.95 -->

**Section 2.2, bilinear groups (p. 4).** We briefly review the necessary facts about bilinear
maps and bilinear map groups [Jou00, Mil04]. We use the following notation:

1. $\mathbb G$ and $\mathbb G_1$ are two (multiplicative) cyclic groups of prime order $p$;
2. $g$ is a generator of $\mathbb G$.
3. $e$ is a bilinear map $e:\mathbb G\times\mathbb G\to\mathbb G_1$.

Let $\mathbb G$ and $\mathbb G_1$ be two groups as above. A bilinear map is a map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ with the following properties:

1. Bilinearity: for all $u,v\in\mathbb G$ and $a,b\in\mathbb Z$, we have
   $e(u^a,v^b)=e(u,v)^{ab}$.
2. Non-degeneracy: $e(g,g)\neq 1$.

We say that $\mathbb G$ is a bilinear group if the group action in $\mathbb G$ can be computed
efficiently and there exists a group $\mathbb G_1$ and an efficiently computable bilinear map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ as above. Note that $e(\,,\,)$ is symmetric since
$e(g^a,g^b)=e(g,g)^{ab}=e(g^b,g^a)$.

Throughout the paper, for a prime order group $\mathbb G$ we use $\mathbb G^*$ to denote the set
$\mathbb G\setminus\{1_{\mathbb G}\}$ where $1_{\mathbb G}$ is the identity of $\mathbb G$.

<a id="pdf-63c1c7b0817f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->

## 3 Complexity Assumptions

**Section 3 and Section 3.1, BDH and Decision BDH (pp. 4–5).** Let $\mathbb G$ be a bilinear
group of prime order $p$. We review the standard Bilinear Diffie-Hellman (BDH) assumption and
define the Bilinear Diffie-Hellman Inversion (BDHI) assumption.

The BDH problem [Jou00, SOK00, BF01] in $\mathbb G$ is as follows: given a tuple
$g,g^a,g^b,g^c\in\mathbb G$ as input, output $e(g,g)^{abc}\in\mathbb G_1$. An algorithm
$\mathcal A$ has advantage $\epsilon$ in solving BDH in $\mathbb G$ if

$$
\Pr\left[\mathcal A(g,g^a,g^b,g^c)=e(g,g)^{abc}\right]\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, and the random bits used by $\mathcal A$. Similarly, we say
that an algorithm $\mathcal B$ that outputs $b\in\{0,1\}$ has advantage $\epsilon$ in solving
the *decision* BDH problem in $\mathbb G$ if

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, the random choice of $T\in\mathbb G_1$, and the random bits
consumed by $\mathcal B$. We refer to the distribution on the left as $\mathcal P_{\mathrm{BDH}}$
and the distribution on the right as $\mathcal R_{\mathrm{BDH}}$.

*Transcription note.* The `-layout` extraction drops the vertical bars, but the page image
(checked at 130 dpi) shows an absolute value around the difference, as transcribed. This
differs from `PairingCryptographyPlan.md` ("Where the papers' formulations differ", item 6),
which says the decision advantage of §3.1 is written without one; that record should be
corrected (the draft's choice is unaffected: it uses the absolute difference of acceptance
probabilities, which is the same number).

<a id="pdf-63c1c7b0817f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Definition 3.1.** We say that the (Decision) $(t,\epsilon)$-BDH assumption holds in
$\mathbb G$ if no $t$-time algorithm has advantage at least $\epsilon$ in solving the
(Decision) BDH problem in $\mathbb G$.

Occasionally we drop the $t$ and $\epsilon$ and refer to the BDH and Decision BDH assumptions in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

## 4 Efficient Selective Identity IBE and HIBE Based on BDH Without Random Oracles

**Section 4 and Section 4.1, opening (p. 5).** We construct an efficient HIBE system that is
selective identity secure without random oracles based on the Decision BDH assumption. In
particular, this implies an efficient selective identity, chosen ciphertext secure IBE based on
Decision BDH without random oracles.

Let $\mathbb G$ be a bilinear group of prime order $p$ (the security parameter determines the
size of $\mathbb G$). Let $e:\mathbb G\times\mathbb G\to\mathbb G_1$ be the bilinear map. For
now, we assume public keys (ID) of depth $\ell$ are vectors of elements in $\mathbb Z_p^{\ell}$.
We write $\mathrm{ID}=(I_1,\dots,I_\ell)\in\mathbb Z_p^{\ell}$. The $j$-th component
corresponds to the identity at level $j$. We later extend the construction to public keys over
$\{0,1\}^*$ by first hashing each component $I_j$ using a collision resistant hash
$H:\{0,1\}^*\to\mathbb Z_p$. We also assume messages to be encrypted are elements in
$\mathbb G_1$. The HIBE system works as follows:

<a id="pdf-63c1c7b0817f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 4.1, the HIBE construction (p. 6).**

**Setup**$(\ell)$: To generate system parameters for an HIBE of maximum depth $\ell$, select a
random generator $g$ in $\mathbb G^*$, a random $\alpha\in\mathbb Z_p$, and set
$g_1=g^{\alpha}$. Next, pick random elements $h_1,\dots,h_\ell\in\mathbb G$ and a random element
$g_2\in\mathbb G$. The public parameters *params* and the secret *master-key* are given by

$$
\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell),\qquad \textit{master-key}=g_2^{\alpha}
$$

For $j=1,\dots,\ell$, we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function:
$F_j(x)=g_1^{x}h_j$.

**KeyGen**$(d_{\mathrm{ID}|_{j-1}},\mathrm{ID})$: To generate the private key
$d_{\mathrm{ID}}$ for an identity $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$ of depth
$j\le\ell$, pick random $r_1,\dots,r_j\in\mathbb Z_p$ and output

$$
d_{\mathrm{ID}}=\left(g_2^{\alpha}\cdot\prod_{k=1}^{j}F_k(I_k)^{r_k},\ g^{r_1},\dots,g^{r_j}\right)
$$

Note that the private key for ID can be generated just given a private key for
$\mathrm{ID}|_{j-1}=(I_1,\dots,I_{j-1})\in\mathbb Z_p^{j-1}$, as required. Indeed, let
$d_{\mathrm{ID}|_{j-1}}=(d_0,\dots,d_{j-1})$ be the private key for $\mathrm{ID}|_{j-1}$. To
generate $d_{\mathrm{ID}}$ pick a random $r_j\in\mathbb Z_p$ and output
$d_{\mathrm{ID}}=(d_0\cdot F_j(I_j)^{r_j},d_1,\dots,d_{j-1},g^{r_j})$.

**Encrypt**$(\textit{params},\mathrm{ID},M)$: To encrypt a message $M\in\mathbb G_1$ under the
public key $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$, pick a random $s\in\mathbb Z_p$ and
output

$$
C=\left(e(g_1,g_2)^{s}\cdot M,\ g^{s},\ F_1(I_1)^{s},\dots,F_j(I_j)^{s}\right)
$$

Note that $e(g_1,g_2)$ can be precomputed once and for all so that encryption does not require
any pairing computations. Alternatively, $e(g_1,g_2)$ can be included in the system
parameters, in which case $g_2$ can be dropped.

**Decrypt**$(d_{\mathrm{ID}},C)$: Consider an identity $\mathrm{ID}=(I_1,\dots,I_j)$. To decrypt
a given ciphertext $C=(A,B,C_1,\dots,C_j)$ using the private key
$d_{\mathrm{ID}}=(d_0,d_1,\dots,d_j)$, output

$$
A\cdot\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}=M
$$

Indeed, for a valid ciphertext, we have

$$
\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}
=\frac{\prod_{k=1}^{j}e(F_k(I_k),g)^{s r_k}}
{e(g,g_2)^{s\alpha}\prod_{k=1}^{j}e(g,F_k(I_k))^{s r_k}}
=\frac{1}{e(g_1,g_2)^{s}}
$$

<a id="pdf-63c1c7b0817f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->

**Section 4.2, opening and Theorem 4.1 (p. 6).** The HIBE system above is reminiscent of the
Gentry-Silverberg HIBE which is only known to be secure in the random oracle model.
Surprisingly, our choice of functions $F_1,\dots,F_\ell$ enables us to prove security without
random oracles. We prove security of our HIBE system under the standard Decision BDH assumption
in $\mathbb G$.

**Theorem 4.1.** Suppose the $(t,\epsilon)$-Decision BDH assumption holds in $\mathbb G$. Then
the previously defined $\ell$-HIBE system is $(t',q_S,\epsilon)$-selective identity, chosen
plaintext (IND-sID-CPA) secure for arbitrary $\ell$ and $q_S$, and any
$t'<t-\Theta(\tau\,\ell\,q_S)$ where $\tau$ is the maximum time for an exponentiation in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, the simulator's setup (p. 7).** Suppose $\mathcal A$ has advantage
$\epsilon$ in attacking the HIBE system. We build an algorithm $\mathcal B$ that solves the
Decision BDH problem in $\mathbb G$. Algorithm $\mathcal B$ is given as input a random 5-tuple
$(g,g^a,g^b,g^c,T)$ that is either sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) or from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform and independent in
$\mathbb G_1$). Algorithm $\mathcal B$'s goal is to output $1$ if $T=e(g,g)^{abc}$ and $0$
otherwise. Set $g_1=g^a$, $g_2=g^b$, $g_3=g^c$. Algorithm $\mathcal B$ works by interacting
with $\mathcal A$ in a selective identity game as follows:

**Initialization.** The selective identity game begins with $\mathcal A$ first outputting an
identity $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)\in\mathbb Z_p^{k}$ of depth $k\le\ell$ that it
intends to attack. If necessary, $\mathcal B$ appends random elements in $\mathbb Z_p$ to
$\mathrm{ID}^*$ so that $\mathrm{ID}^*$ is a vector of length $\ell$.

**Setup.** To generate the system parameters, algorithm $\mathcal B$ picks
$\alpha_1,\dots,\alpha_\ell\in\mathbb Z_p$ at random and defines
$h_j=g_1^{-I^*_j}g^{\alpha_j}\in\mathbb G$ for $j=1,\dots,\ell$. It gives $\mathcal A$ the
system parameters $\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell)$. Note that the corresponding
master key, which is unknown to $\mathcal B$, is $g_2^{a}=g^{ab}\in\mathbb G$. As before, for
$j=1,\dots,\ell$ we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function

$$
F_j(x)=g_1^{x}h_j=g_1^{x-I^*_j}g^{\alpha_j}
$$

<a id="pdf-63c1c7b0817f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 1 (p. 7).** $\mathcal A$ issues up to $q_S$ private key queries.
Consider a query for the private key corresponding to
$\mathrm{ID}=(I_1,\dots,I_u)\in\mathbb Z_p^{u}$ where $u\le\ell$. The only restriction is that
ID is not a prefix of $\mathrm{ID}^*$. Let $j$ be the smallest index such that
$I_j\neq I^*_j$. Necessarily $1\le j\le u$. To respond to the query, algorithm $\mathcal B$
first derives a private key for the identity $(I_1,\dots,I_j)$ from which it then constructs a
private key for the requested identity $\mathrm{ID}=(I_1,\dots,I_j,\dots,I_u)$. Algorithm
$\mathcal B$ picks random elements $r_1,\dots,r_j\in\mathbb Z_p$ and sets

$$
d_0=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\prod_{v=1}^{j}F_v(I_v)^{r_v},\quad
d_1=g^{r_1},\quad\dots,\quad d_{j-1}=g^{r_{j-1}},\quad
d_j=g_2^{\frac{-1}{I_j-I^*_j}}g^{r_j}
$$

We claim that $(d_0,d_1,\dots,d_j)$ is a valid random private key for $(I_1,\dots,I_j)$. To
see this, let $\tilde r_j=r_j-b/(I_j-I^*_j)$. Then we have that

$$
g_2^{\frac{-\alpha_j}{I_j-I^*_j}}F_j(I_j)^{r_j}
=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j}
=g_2^{a}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j-\frac{b}{I_j-I^*_j}}
=g_2^{a}F_j(I_j)^{\tilde r_j}
$$

It follows that the private key $(d_0,d_1,\dots,d_j)$ defined above satisfies

$$
d_0=g_2^{a}\cdot\Bigl(\prod_{v=1}^{j-1}F_v(I_v)^{r_v}\Bigr)\cdot F_j(I_j)^{\tilde r_j},\quad
d_1=g^{r_1},\ \dots,\ d_{j-1}=g^{r_{j-1}},\quad d_j=g^{\tilde r_j}
$$

where $r_1,\dots,r_{j-1},\tilde r_j$ are uniform in $\mathbb Z_p$. This matches the definition
for a private key for $(I_1,\dots,I_j)$. Hence, $(d_0,d_1,\dots,d_j)$ is a valid private key for
$(I_1,\dots,I_j)$. Algorithm $\mathcal B$ derives a private key for the requested ID from the
private key $(d_0,d_1,\dots,d_j)$ and gives $\mathcal A$ the result.

*Transcription note.* The exponents are stacked fractions in the PDF, flattened by the
extraction; they were read from the page image (150 dpi) as $-\alpha_j/(I_j-I^*_j)$ and
$-1/(I_j-I^*_j)$. The PDF sets identities in an upright font ($\mathrm I_j$); plain $I_j$ is
used here.

<a id="pdf-63c1c7b0817f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->

**Proof of Theorem 4.1, Challenge (p. 7).** When $\mathcal A$ decides that Phase 1 is over, it
outputs two messages $M_0,M_1\in\mathbb G_1$ on which it wishes to be challenged. Algorithm
$\mathcal B$ picks a random bit $b\in\{0,1\}$ and responds with the ciphertext
$C=(M_b\cdot T,\ g_3,\ g_3^{\alpha_1},\dots,g_3^{\alpha_k})$. Since $F_i(I^*_i)=g^{\alpha_i}$ for
all $i$, we have that

$$
C=\left(M_b\cdot T,\ g^{c},\ F_1(I^*_1)^{c},\dots,F_k(I^*_k)^{c}\right)
$$

Hence, if $T=e(g,g)^{abc}=e(g_1,g_2)^{c}$ then $C$ is a valid encryption of $M_b$ under the
public key $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)$. On the other hand, when $T$ is uniform and
independent in $\mathbb G_1$ (when the input 5-tuple is sampled from
$\mathcal R_{\mathrm{BDH}}$) then $C$ is independent of $b$ in the adversary's view.

<a id="pdf-63c1c7b0817f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 2, Guess and the advantage (p. 8).**

**Phase 2.** $\mathcal A$ continues to issue queries not issued in Phase 1. Algorithm
$\mathcal B$ responds as before.

**Guess.** Finally, $\mathcal A$ outputs a guess $b'\in\{0,1\}$. Algorithm $\mathcal B$
concludes its own game by outputting a guess as follows. If $b=b'$ then $\mathcal B$ outputs
$1$ meaning $T=e(g,g)^{abc}$. Otherwise, it outputs $0$ meaning $T\neq e(g,g)^{abc}$.

When the input 5-tuple is sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) then $\mathcal A$'s view is identical to its view in a real attack game and
therefore $\mathcal A$ must satisfy $\left|\Pr[b=b']-1/2\right|>\epsilon$. On the other hand,
when the input 5-tuple is sampled from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform in
$\mathbb G_1$) then $\Pr[b=b']=1/2$. Therefore, with $g$ uniform in $\mathbb G^*$, $a,b,c$
uniform in $\mathbb Z_p$, and $T$ uniform in $\mathbb G_1$ we have that

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|
\ge\left|\left(\frac12\pm\epsilon\right)-\frac12\right|=\epsilon
$$

as required. This completes the proof of Theorem 4.1.

*Transcription note.* The page image (150 dpi) shows absolute-value bars on both sides, as
transcribed.

<a id="pdf-63c1c7b0817f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 4.4, arbitrary identities (p. 8).** We can extend our HIBE above to handle identities
$\mathrm{ID}=(I_1,\dots,I_\ell)$ with $I_j\in\{0,1\}^*$ (as opposed to $I_j\in\mathbb Z_p$) by
first hashing each $I_j$ using a collision resistant hash function $H:\{0,1\}^*\to\mathbb Z_p$
prior to key generation and encryption. A standard argument shows that if the scheme above is
selective identity, chosen ciphertext secure then so is the scheme with the additional hash
function. We note that there is no need for a full domain hash into $\mathbb Z_p$; for example,
a collision resistant hash function $H:\{0,1\}^*\to\{1,\dots,2^b\}$ where $2^b<p$ is sufficient
for the security proof.
