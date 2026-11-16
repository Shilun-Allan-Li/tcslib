<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Lattice-Based FHE as Secure as PKE

Zvika Brakerski and Vinod Vaikuntanathan. *ITCS 2014*, pp. 1–12; IACR ePrint 2013/541, PDF
created 28 August 2013 (21 pages; tag `BV14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): the leveled-FHE footnote and Theorem 1.1 of §1, the
decomposition routines of §2.3, §2.5 (homomorphic encryption, Definitions 2.12–2.13,
Theorem 2.14), all of §3 (the scheme `NCCrypt`, Definition 3.1, Lemmas 3.2–3.3, Proposition 3.4,
Claims 3.4.1–3.4.2, width-5 permutation branching programs, Equations (4)–(6), Theorem 3.5,
Lemma 3.6, Theorem 3.7), the statement of Lemma 4.4, and Corollary 4.5 with the key-size remark
of §4.2. §2.1, §2.2, §2.4 (the randomization lemmas 2.9–2.11) and §4.1 are not transcribed; the
phase-5 Lean replaces their probabilistic bounds by worst-case ones. The PDF is not committed.
Physical and printed pages coincide. The scoped raw extraction is
`brakerski-vaikuntanathan-2014-fhe.raw.md`. Mathematics is set in LaTeX; the paper's
sans-serif procedure names are written $\mathsf{NCCrypt.Keygen}$ etc. The wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-eab2d1667a8e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->

**Section 1, footnote 1: leveled FHE and circular security (p. 1).** Here, and in the rest of the
introduction, when we say FHE, we mean a leveled FHE scheme that can evaluate circuits of any
a-priori bounded polynomial depth. The only known way to achieve non-leveled FHE schemes is to
make a circular security assumption, in addition.

<a id="pdf-eab2d1667a8e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->

**Theorem 1.1.** For every $\epsilon>0$, there exists a leveled fully homomorphic encryption
scheme based on the $\mathsf{DLWE}_{n,q,\alpha}$ assumption ($n$-dimensional decisional LWE
modulo $q$, with discrete Gaussian noise with parameter $\alpha$), where
$\alpha=1/\tilde O(n^{\epsilon}\cdot\sqrt{n\log(q)})$.

Thus, the scheme is secure based on either the quantum worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$, or the classical worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

*Transcription note.* The extraction drops the $\epsilon$ glyphs and scatters the tildes; the
statement is read from the layout. It is context only (the phase-6 plan does not formalize
worst-case lattice factors).

<a id="pdf-eab2d1667a8e-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->

**Section 2.3, vector decomposition (pp. 5–6).** We show how to decompose vectors in a way that
makes their norm smaller, and yet preserves certain inner products. Our notation is generally
adopted from [BGV12].

*Vector Decomposition.* We often break vectors into their bit representations as defined below:

- $\mathsf{BitDecomp}_q(\mathbf x)$: For $\mathbf x\in\mathbb Z^n$, let $w_{i,j}\in\{0,1\}$ be
  such that $\mathbf x[i]=\sum_{j=0}^{\lceil\log q\rceil-1}2^j\cdot w_{i,j}\pmod q$. Output the
  vector
  $(w_{1,\lceil\log q\rceil-1},\dots,w_{1,0},\dots,w_{n,\lceil\log q\rceil-1},\dots,w_{n,0})\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.
- $\mathsf{PowersOfTwo}_q(\mathbf y)$: For $\mathbf y\in\mathbb Z^n$, output
  $\bigl[(2^{\lceil\log q\rceil-1}\mathbf y[1],\dots,2\mathbf y[1],\mathbf y[1],\dots,2^{\lceil\log q\rceil-1}\cdot\mathbf y[n],\dots,2\mathbf y[n],\mathbf y[n])\bigr]_q\in\mathbb Z_q^{n\cdot\lceil\log q\rceil}$.

We will usually omit the subscript $q$ when it is clear from the context.

**Claim 2.7.** For all $q\in\mathbb N$ and $\mathbf x,\mathbf y\in\mathbb Z^n$, it holds that

$$
\langle\mathbf x,\mathbf y\rangle=\langle\mathsf{BitDecomp}_q(\mathbf x),\mathsf{PowersOfTwo}_q(\mathbf y)\rangle\pmod q.
$$

Additionally, we define the procedure Flatten following [GSW13], along with the procedure
Combine. Let
$\mathbf g=(2^{\lceil\log(q)\rceil-1},2^{\lceil\log(q)\rceil-2},\dots,4,2,1)\in\mathbb Z^{\lceil\log q\rceil}$
and let $\mathbf G:=\mathbf g\otimes\mathbf I_n\in\mathbb Z^{n\times(n\cdot\lceil\log q\rceil)}$
denote the tensor product of $\mathbf g$ with the $n$-by-$n$ identity matrix $\mathbf I_n$.

- $\mathsf{Combine}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $[\mathbf G\cdot\mathbf z]_q\in\mathbb Z_q^n$.
- $\mathsf{Flatten}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $\mathsf{BitDecomp}_q(\mathsf{Combine}(\mathbf z))\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.

**Claim 2.8.** For all $q\in\mathbb N$, and $\mathbf x,\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$,
it holds that

$$
\langle\mathsf{PowersOfTwo}(\mathbf x),\mathbf z\rangle=\langle\mathsf{PowersOfTwo}(\mathbf x),\mathsf{Flatten}(\mathbf z)\rangle\pmod q.
$$

*Transcription note.* BV14 orders bits most significant first, unlike GSW13. In Claim 2.8 the
printed domain of $\mathbf x$ is as transcribed (the claim is used with
$\mathbf x\in\mathbb Z^{n}$). Confidence is lowered because sub- and superscripts are flattened
in the extraction.

<a id="pdf-eab2d1667a8e-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.5, homomorphic encryption and bootstrapping (pp. 7–8).** We now define homomorphic
encryption and introduce Gentry's bootstrapping theorem. Our definitions are mostly taken from
[BV11, BGV12].

A homomorphic (public-key) encryption scheme
$\mathsf{HE}=(\mathsf{HE.Keygen},\mathsf{HE.Enc},\mathsf{HE.Dec},\mathsf{HE.Eval})$ is a
quadruple of ppt algorithms as follows ($\kappa$ is the security parameter):

- **Key generation** $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$: Outputs a public
  encryption key $pk$, a public evaluation key $evk$ and a secret decryption key $sk$.²
- **Encryption** $c\leftarrow\mathsf{HE.Enc}_{pk}(\mu)$: Using the public key $pk$, encrypts a
  single bit message $\mu\in\{0,1\}$ into a ciphertext $c$.
- **Decryption** $\mu\leftarrow\mathsf{HE.Dec}_{sk}(c)$: Using the secret key $sk$, decrypts a
  ciphertext $c$ to recover the message $\mu\in\{0,1\}$.
- **Homomorphic evaluation** $c_f\leftarrow\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell)$: Using the
  evaluation key $evk$, applies a function $f:\{0,1\}^\ell\to\{0,1\}$ to $c_1,\dots,c_\ell$, and
  outputs a ciphertext $c_f$.

Footnote 2: We adopt the terminology of [BV11] that treats the evaluation key as a separate
entity from the public key.

A homomorphic encryption scheme is said to be secure if it is semantically secure (note that the
adversary is given both $pk$ and $evk$).

Homomorphism w.r.t depth-bounded circuits and full homomorphism are defined next:

<a id="pdf-eab2d1667a8e-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Definition 2.12 (compactness and full homomorphism).** A homomorphic encryption scheme is
*compact* if its decryption circuit is independent of the evaluated function. A compact scheme is
(pure) *fully homomorphic* if it can evaluate any efficiently computable function. The scheme is
*leveled fully homomorphic* if it takes $1^L$ as additional input in key generation, and can only
evaluate depth $L$ Boolean circuits.

Gentry's bootstrapping theorem shows how to go from limited amount of homomorphism to full
homomorphism. This method has to do with the augmented decryption circuit.

<a id="pdf-eab2d1667a8e-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Definition 2.13.** Consider a homomorphic encryption scheme $\mathsf{HE}$. Let $(sk,pk,evk)$ be
properly generated keys and let $\mathcal C$ be the set of properly decryptable ciphertexts. Then
the set of *augmented decryption functions*, $\{f_{c_1,c_2}\}_{c_1,c_2\in\mathcal C}$ is defined
by $f_{c_1,c_2}(x)=\overline{\mathsf{HE.Dec}_x(c_1)\wedge\mathsf{HE.Dec}_x(c_2)}$. Namely, the function
that uses its input as secret key, decrypts $c_1,c_2$ and returns the NAND of the results.

*Transcription note.* The bar over the conjunction (NAND) is visible in the page image
(150 dpi), not in the extraction, which shows a plain $\wedge$.

<a id="pdf-eab2d1667a8e-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->

**Theorem 2.14 (bootstrapping [Gen09b, Gen09a]).** The bootstrapping theorem is thus as
follows. A scheme that can homomorphically evaluate its family of augmented decryption circuits
can be transformed into a leveled fully homomorphic encryption scheme with the same decryption
circuit, ciphertext space and public key.

Furthermore, if the aforementioned scheme is also weak circular secure (remains secure even
against an adversary who gets encryptions of the bits of the secret key), then it can be made into
a pure fully homomorphic encryption scheme.

<a id="pdf-eab2d1667a8e-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->

## 3 Our FHE Scheme

**Section 3, opening, and Section 3.1, opening (p. 8).** In this section, we describe an FHE
scheme secure under a polynomial LWE assumption which, using known reductions [Reg05, Pei09],
translates to the worst-case hardness of solving various lattice problems to within polynomial
approximation factors. We start with the basic encryption scheme in Section 3.1, and describe
"proto-homomorphic" addition and multiplication subroutines in Section 3.2. Departing from the
"conventional wisdom" in FHE, our circuit evaluation procedure in Section 3.3 will not be a naive
combination of these proto-homomorphic operations, but rather a carefully designed procedure that
manages the noise growth effectively.

Finally, in Section 3.4, we put this all together to get our FHE scheme under the decisional LWE
assumption $\mathsf{DLWE}_{n,q,\alpha}$ with $\alpha=n^{-c}$ for some constant $c>0$. This
polynomial factor is rather large: thus, in Section 4, we apply a carefully designed variant of
the dimension-modulus reduction procedure of [BV11] to obtain our final FHE scheme that is secure
under the hardness of $\mathsf{DLWE}_{n,q,\alpha}$ with
$\alpha\le1/\tilde O_\kappa(n\cdot\sqrt{n\log(q)})$ which is weakest LWE hardness assumption that
underlies the (non-homomorphic) lattice-based PKE schemes [AD97, Reg04, Reg05, Pei09, BLP+13].

Our basic encryption scheme closely follows the Gentry-Sahai-Waters FHE scheme [GSW13]. We refer
the reader to Section 2.3 for the description of the vector decomposition routines PowersOfTwo,
BitDecomp and Flatten used in the scheme below.

<a id="pdf-eab2d1667a8e-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, the scheme $\mathsf{NCCrypt}$ (p. 9).**

*System Parameters.* Let $n$ be the LWE dimension and $q$ be an LWE modulus. Define
$N:=(n+1)\cdot\lceil\log q\rceil$. Let $d$ denote the maximal homomorphism depth that is allowed
by the scheme. Let $\chi$ be an error distribution over $\mathbb Z$. Typically $\chi$ will be a
discrete Gaussian $D_{\mathbb Z,\alpha q}$ for
$\alpha=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot4^d)$. Recall that we identify $\mathbb Z_q$ with
the set $(-q/2,q/2]\cap\mathbb Z$.

- $\mathsf{NCCrypt.Keygen}(1^n,q,4^d)$: Sample a vector $\mathbf s\xleftarrow{\$}\mathbb Z_q^n$.
  Let $m\triangleq(n+1)\cdot(\log q+O(1))$. Sample $\mathbf A\xleftarrow{\$}\mathbb Z_q^{m\times n}$
  and $\mathbf e\xleftarrow{\$}\chi^m$. Compute $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$,
  and define

  $$
  \mathbf P:=[\mathbf b\,\|-\mathbf A]\in\mathbb Z_q^{m\times(n+1)}.
  $$

  Output $sk=\mathbf s$ and $pk=evk=\mathbf P$.

  We describe public-key as well as secret-key encryption algorithms. Looking ahead, we remark
  that a secret-key encryption of $\mu$ is somewhat less "noisy" than a public-key encryption of
  $\mu$.
- $\mathsf{NCCrypt.PubEnc}(pk,\mu)$: To encrypt a bit $\mu\in\{0,1\}$, using the public key
  $pk=\mathbf P$, we let $\mathbf R\xleftarrow{\$}\{0,1\}^{N\times m}$, and output the ciphertext

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.SecEnc}(sk,\mu)$: A symmetric encryption of a bit $\mu\in\{0,1\}$, using the
  secret key $sk=\mathbf s$, is performed by sampling
  $\mathbf A\xleftarrow{\$}\mathbb Z_q^{N\times n}$ and $\mathbf e\xleftarrow{\$}\chi^N$,
  computing $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$, and defining

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}\left([\mathbf b\,\|-\mathbf A]\right)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.Dec}(sk,\mathbf C)$: Let $\mathbf c$ be the second row of $\mathbf C$. We use
  standard Regev decryption on $\mathbf c$. Namely, we output $\mu^*=0$ if
  $\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|<q/8$, and $\mu^*=1$
  otherwise.

*Transcription note.* The absolute value in $\mathsf{NCCrypt.Dec}$ is visible in the page image
(115 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.1, correctness; Definition 3.1 and Lemma 3.2 (p. 9).** In order to show correctness
of this scheme, we analyze the noise magnitude of ciphertexts produced by both the public-key and
secret-key encryption algorithms. As we will show shortly, for ciphertexts $\mathbf C$ produced by
either encryption algorithm, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf e\pmod q
$$

for a noise vector $\mathbf e$ of "small magnitude". This motivates our definition of the noise in
the ciphertext $\mathbf C$ with respect to a secret key vector $\mathbf s$ and a message $\mu$ as
follows.

**Definition 3.1.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$, we define

$$
\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)\triangleq\bigl\|(\mathbf C-\mu\mathbf I)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q\bigr\|_\infty
$$

The significance of this definition is captured by the following claims. The first claim shows
that any ciphertext with small noise is decrypted correctly.

**Lemma 3.2.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$ such that $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$,

$$
\mathsf{NCCrypt.Dec}(\mathbf s,\mathbf C)=\mu
$$

<a id="pdf-eab2d1667a8e-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Proof of Lemma 3.2 (p. 10).** Since $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\eta+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q
$$

where $\|\eta\|_\infty<q/8$. Thus, for the second row of $\mathbf C$ it holds that

$$
\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle=\eta+2^{\lceil\log(q)\rceil-2}\cdot\mu\pmod q
$$

where $|\eta|<q/8$. Thus, when $\mu=0$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|=|\eta|<q/8
$$

When $\mu=1$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|\ge q/4-|\eta|\ge q/8
$$

since $q/4\le2^{\lceil\log(q)\rceil-2}<q/2$. This shows correctness of decryption for ciphertexts
with small noise.

*Transcription note.* The vertical bars around $[\cdot]_q$ in the two displays are visible in the
page image (130 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->

**Section 3.1, fresh noise; Lemma 3.3 and its proof (p. 10).** The next claim demonstrates
parameter settings for which the (public key and secret key) encryption algorithms produce
ciphertexts with small noise.

**Lemma 3.3.** Let $n$ be the LWE dimension, $q$ be the LWE modulus and $\chi=D_{\mathbb Z,\alpha q}$ be the discrete Gaussian
distribution. Then, for every $\mathbf s\in\mathbb Z_q^n$ and $\mu\in\{0,1\}$,

- for $\mathbf C_{pub}\leftarrow\mathsf{NCCrypt.PubEnc}(pk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{pub})=\tilde O_\kappa(\alpha q\cdot\sqrt m)$.
- for $\mathbf C_{sec}\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{sec})=\tilde O_\kappa(\alpha q)$.

with all but negligible (in $\kappa$) probability over the coins of $\mathsf{NCCrypt.Keygen}$.

In particular, we have correctness of decryption for the public key encryption for
$\alpha<1/\tilde\Omega_\kappa(\sqrt m)$, and for the secret key encryption for
$\alpha<1/\tilde\Omega_\kappa(1)$.

**Proof of Lemma 3.3.** We first show the analysis for the public-key encryption.

$$
\begin{aligned}
\mathbf C_{pub}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf P\cdot(1,\mathbf s)^T+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}
$$

Thus, by Proposition 2.3,

$$
\mathsf{noise}(\mathbf C_{pub})=\|\mathbf R\cdot\mathbf e\|_\infty=\tilde O_\kappa(\sqrt m\cdot\alpha q)
$$

This is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(\sqrt m)$.

The analysis for the secret key encryption follows analogously, except that

$$
\mathbf C_{sec}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
$$

Thus,

$$
\mathsf{noise}(\mathbf C_{sec})=\|\mathbf e\|_\infty=\tilde O_\kappa(\alpha q)
$$

which is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(1)$.

*Transcription note.* The tildes and radicals are flattened in the extraction; confidence is
lowered for that reason.

<a id="pdf-eab2d1667a8e-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.1, security and complexity of decryption; Proposition 3.4 (p. 11).**

*Security.* Semantic security of the scheme follows from the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$, similarly to Regev's encryption scheme (see [Reg05, BV11, GSW13]
for similar arguments).

*Complexity of Decryption.* Our decryption algorithm is essentially the same as the decryption
algorithm in Regev's encryption scheme, the complexity of which has been thoroughly studied in the
context of FHE. The following is an immediate corollary from [BV11, Lemma 4.1].

**Proposition 3.4.** There exists a constant $c_{\mathsf{dec}}$ such that the decryption circuit
of the scheme $\mathsf{NCCrypt}$, with parameters $n,q$, has depth at most
$c_{\mathsf{dec}}\cdot\log(n\log q)$.

*Transcription note.* In the 39-page full version of [BV11] used for this campaign
(`brakerski-vaikuntanathan-2011-fhe.md`) the decryption-depth lemma is numbered Lemma 4.5;
"[BV11, Lemma 4.1]" is BV14's reference.

<a id="pdf-eab2d1667a8e-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.2, proto-homomorphic operations; addition and Claim 3.4.1 (p. 11).** We now describe
proto-homomorphic addition and multiplication algorithms which will be used in Section 3.3 for
homomorphic circuit evaluation. Departing from the "conventional wisdom" in FHE, our circuit
evaluation procedure will not be a naive combination of homomorphic addition and multiplication,
but a carefully designed procedure that manages the noise growth effectively. To further stress
the fact that we do not intend for these procedures to be used independently, we call them
proto-homomorphic operations.

*Proto-Homomorphic Addition.* This is a simple addition of the ciphertext matrices.

- $\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$: Output
  $\mathbf C_+:=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)$.

Jumping ahead, we note that in our use of $\mathsf{NCCrypt.ProtoAdd}$ in Section 3.3, both
$\mathbf C_1$ and $\mathbf C_2$ will be encryptions of bits, and at most one of them will be an
encryption of $1$. The following claim analyzes the noise growth in homomorphic addition.

**Claim 3.4.1 (Noise Growth in $\mathsf{NCCrypt.ProtoAdd}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\mathbb Z$ and
$\mathbf C_1,\mathbf C_2\in\{0,1\}^{N\times N}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2))
\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

**Proof.** Let $\mathbf C_+\leftarrow\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$. We note
that

$$
\begin{aligned}
\mathbf C_+\cdot\mathsf{PowersOfTwo}(1,\mathbf s)&=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf C_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf e_1+\mathbf e_2)+(\mu_1+\mu_2)\cdot\mathbf I
\end{aligned}
$$

Thus, by the definition of $\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathbf C_+)\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

*Transcription note.* The last line of the display ends in "$\cdot\,\mathbf I$" as printed (the
intended term is $(\mu_1+\mu_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)$).

<a id="pdf-eab2d1667a8e-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 3.2, multiplication; Claim 3.4.2 (p. 12).** *Homomorphic Multiplication.* This is
essentially a multiplication of the ciphertext matrices, except that we randomize the first
ciphertext.

- $\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$:
  - Randomize $\mathbf C_1\in\{0,1\}^{N\times N}$ into a matrix
    $\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ by replacing each row $\mathbf c$ in
    $\mathbf C_1$ by the row
    $\widetilde{\mathbf c}\leftarrow\mathsf{BitDecomp}(\mathsf{Rand}(pk,\mathsf{Combine}(\mathbf c)))$
    where $\mathsf{Rand}$ is the LWE randomization procedure from Section 2.4.
  - Output $\mathbf C_\times\leftarrow\mathsf{Flatten}\bigl(\widetilde{\mathbf C}_1\cdot\mathbf C_2\bigr)$.

Jumping ahead, we remark that when we use $\mathsf{NCCrypt.ProtoMult}$ in our homomorphic circuit
evaluation in Section 3.3, the first ciphertext will be an "evaluated ciphertext" (namely, a
result of previous homomorphic evaluations), whereas the second ciphertext will be a "fresh
ciphertext" (namely an output of the *secret key* encryption algorithm).

The first new idea in this work is that while the order of the arguments does not matter in
homomorphic addition, the homomorphic multiplication algorithm $\mathsf{NCCrypt.ProtoMult}$ is
inherently asymmetric, since it is essentially the (non-commutative) matrix multiplication
operation. This asymmetry turns out to be the key to achieving improved noise growth, as
Claim 3.4.2 below will demonstrate.

**Claim 3.4.2 (Noise Growth in $\mathsf{NCCrypt.ProtoMult}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\{0,1\}$ and $\mathbf C_1\in\{0,1\}^{N\times N}$ and
$\mathbf C_2\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu_2)$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathsf{NCCrypt.ProtoMult}(\mathbf C_1,\mathbf C_2))
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

with all but negligible probability over the randomness of $\mathsf{NCCrypt.Keygen}$,
$\mathsf{NCCrypt.SecEnc}$ and $\mathsf{NCCrypt.ProtoMult}$.

**Remark.** In words, Claim 3.4.2 says that if $\mu_2\in\{0,1\}$ (as will be the case in our
homomorphic circuit evaluation in Section 3.3), the noise in $\mathbf C_\times$ is at most the
noise in $\mathbf C_1$, plus a fixed additive term. What's more, if $\mu_2=0$, then the noise in
$\mathbf C_\times$ is independent of that in $\mathbf C_1$! *These two facts are the key new ideas
that enable our main result.*

<a id="pdf-eab2d1667a8e-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Proof of Claim 3.4.2 (pp. 12–13).** Let
$\mathbf C_\times\leftarrow\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$. Note that

$$
\begin{aligned}
\mathbf C_\times\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}(\widetilde{\mathbf C}_1\cdot\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf e_2+\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf C}_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot(\widetilde{\mathbf e}_1+\mu_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=(\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf e}_1)+\mu_1\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}\tag{1}
$$

Since $\mathbf e_2\leftarrow D^N_{\mathbb Z,\alpha q}$ and each row of
$\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ is the result of $\mathsf{Rand}$, by Lemma 2.11,
we have

$$
\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty\le\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{2}
$$

with all but negligible probability. Also, by lemma 2.10, we have

$$
\|\widetilde{\mathbf e}_1\|_\infty\le\|\mathbf e_1\|_\infty+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{3}
$$

with all but negligible probability.

Putting together Eq. (1),(2) and (3), we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathbf C_\times)
\le\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty+|\mu_2|\cdot\|\widetilde{\mathbf e}_1\|_\infty
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

which finishes the proof.

<a id="pdf-eab2d1667a8e-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

**Section 3.3, homomorphic evaluation of circuits: opening (p. 13).** We now describe how to
homomorphically evaluate a Boolean circuit $\Psi$ with two-input NAND gates that takes $\ell$
inputs, and has depth $d$. In particular, our scheme will be able to evaluate circuits of depth
$c\cdot\log n$ (for any constant $c$) under a polynomial LWE assumption, namely
$\mathsf{DLWE}_{n,q,\chi}$ where $\chi=D_{\mathbb Z,\alpha}$ and $\alpha=1/n^{\Theta(c)}$. Since
the depth of the decryption circuit is
$c_{\mathsf{dec}}\cdot\log(n\log(q))\le2c_{\mathsf{dec}}\cdot\log(n)$ (for some constant
$c_{\mathsf{dec}}>0$), the scheme is bootstrappable, and by the bootstrapping theorem
(Theorem 2.14), we get a leveled FHE scheme under the same assumption.

To evaluate a circuit, our scheme first turns it into a width-5 permutation branching program
[BDFP86, Bar89], a model of computation that we describe below.

<a id="pdf-eab2d1667a8e-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->

**Section 3.3, width-5 permutation branching programs (pp. 13–14).** A permutation branching
program $\Pi$ of length $L$ with input space $\{0,1\}^\ell$ is a sequence of $L$ tuples of the form
$\bigl(\mathsf{var}(t),\sigma_{t,0},\sigma_{t,1}\bigr)$ where

- $\mathsf{var}:[L]\to[\ell]$ is a function that associates the $t$-th tuple with an input bit
  $x_{\mathsf{var}(t)}$.
- $\sigma_{j,0}$ and $\sigma_{j,1}$ are permutations on 5 elements. We will think of $\sigma_{j,0}$
  and $\sigma_{j,1}$ as bijective functions from the set $\{1,2,3,4,5\}$ to itself.

The computation of the program $\Pi$ on input $\mathbf x=(x_1,\dots,x_\ell)$ proceeds as follows.
The state of the computation at any point in time $t$ is a number $\zeta_t\in\{1,2,3,4,5\}$.
Computation starts with the initial state $\zeta_0=1$. The state $\zeta_t$ is computed
recursively as

$$
\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})
$$

Finally, after $L$ steps, our state is $\zeta_L$. The output of the computation is $1$ if
$\zeta_L=1$, and $0$ otherwise.

To manage the growth of noise in homomorphic evaluation, we need to work with bits rather than
numbers. Thus, we prefer to represent the state $\zeta_t\in\{1,2,3,4,5\}$ by a 0-1 vector
$\mathbf v_t$ which is the unit vector $\mathbf u_{\zeta_t}$ in 5 dimensions.

The computation then proceeds as follows. The idea is that $\mathbf v_t[i]=1$ if and only if
$\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})=i$. Turning this around, $\mathbf v_t[i]=1$ if and only
if either:

- $\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=0$; or
- $\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=1$.

The following formula captures this condition. For $t=1,\dots,L$, and $i\in\{1,2,3,4,5\}$, we
have:

$$
\begin{aligned}
\mathbf v_t[i]&:=\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]\cdot x_{\mathsf{var}(t)}\\
&=\mathbf v_{t-1}[\gamma_{t,i,0}]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\gamma_{t,i,1}]\cdot x_{\mathsf{var}(t)}
\end{aligned}\tag{4}
$$

where $\gamma_{t,i,0}\triangleq\sigma_{t,0}^{-1}(i)$ and $\gamma_{t,i,1}\triangleq\sigma_{t,1}^{-1}(i)$
are constants that are publicly computable given the description of the branching program. It is
this form that we will work with in our homomorphic evaluation.

The important property that we will use is that circuits of depth $d$ can be simulated by
branching programs of depth $L=4^d$.

*Transcription note.* "$\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})$" is as printed (checked
against the page image); the intended permutation is $\sigma_{t,x_{\mathsf{var}(t)}}$, selected by
the value of the input bit, as Equation (4) shows.

<a id="pdf-eab2d1667a8e-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Theorem 3.5 (Barrington's Theorem [Bar89]).** Every Boolean NAND circuit $\Psi$ that acts on
$\ell$ inputs and has depth $d$ can be computed by a width-5 permutation branching program $\Pi$ of
length $4^d$. Given the description of the circuit $\Psi$, the description of the branching
program $\Pi$ can be computed in $\mathrm{poly}(\ell,4^d)$ time.

<a id="pdf-eab2d1667a8e-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.3, homomorphic evaluation $\mathsf{NCCrypt.Eval}(\Psi,\mathbf C_1,\dots,\mathbf C_\ell)$,
Equations (5)–(6) (p. 14).** The homomorphic evaluation procedure will first convert the depth-$d$
circuit $\Psi$ into a width-5 permutation branching program $\Pi$ of length $L=4^d$.

- **[Initialization]** We will maintain the encrypted state of the computation of the branching
  program for every step $t$. We denote this by
  $\mathbf V_t=(\mathbf V_{t,1},\mathbf V_{t,2},\mathbf V_{t,3},\mathbf V_{t,4},\mathbf V_{t,5})$,
  where each $\mathbf V_t[i]\in\{0,1\}^{N\times N}$ will be an encryption of $\mathbf v_t[i]$.
  - We initialize the state as follows. Compute $\mathbf V_{0,i}:=\mathbf v_0[i]\cdot\mathbf I$.
    Note that $\mathbf V_{0,i}$ is in fact a valid encryption of the bit $\mathbf v_0[i]$ with zero
    noise.
  - We also compute encryptions of the complements of the input bits, for convenience. That is,
    set $\bar{\mathbf C}_k:=\mathbf I-\mathbf C_k$. Note that $\bar{\mathbf C}_k$ is an encryption
    of $\bar x_k=1-x_k$ with the same noise as $\mathbf C_k$.
- **[Evaluation]** The evaluation proceeds iteratively for $t=1,\dots,L$, where $L$ is the length
  of the branching program $\Pi$. Assuming that we have
  $\mathbf V_{t-1}:=(\mathbf V_{t-1,1},\mathbf V_{t-1,2},\dots,\mathbf V_{t-1,5})$, the encryption
  of the state of the branching program computation at time $t-1$, we compute
  $\mathbf V_t:=(\mathbf V_{t,1},\mathbf V_{t,2},\dots,\mathbf V_{t,5})$ by homomorphically
  evaluating Eq. (4) above.

  That is, for $i\in\{1,2,3,4,5\}$, we compute

  $$
  \begin{aligned}
  \mathbf V_{t,i}:=\mathsf{NCCrypt.ProtoAdd}\Bigl(&\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr),&&(5)\\
  &\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)&&(6)
  \end{aligned}
  $$
- **[Output]** Upon finishing the evaluation stage, we have
  $\mathbf V_L:=(\mathbf V_{L,1},\mathbf V_{L,2},\dots,\mathbf V_{L,5})$. Output $\mathbf V_{L,1}$
  as the result of the homomorphic evaluation.

We now show that the scheme correctly evaluates circuits.

*Transcription note.* In Equations (5)–(6) $\gamma_0,\gamma_1$ abbreviate
$\gamma_{t,i,0},\gamma_{t,i,1}$ of Equation (4).

<a id="pdf-eab2d1667a8e-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Lemma 3.6 (Correctness of Homomorphic Evaluation).** Let $n$ be the LWE dimension, $q$ the LWE
modulus, $\Psi$ be any Boolean circuit of depth $d$, and

$$
\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})
$$

For every $x_1,\dots,x_\ell\in\{0,1\}$, every Boolean circuit $\Psi$ of depth at most $d$, and
every secret key $sk$, letting $\mathbf C_k\leftarrow\mathsf{NCCrypt.SecEnc}(sk,x_k)$ be the
*secret key* encryptions of the inputs, and
$\mathbf C_\Psi\leftarrow\mathsf{NCCrypt.Eval}(evk,\Psi,\mathbf C_1,\dots,\mathbf C_k)$ be the
evaluated ciphertext, we have:

$$
\mathsf{NCCrypt.Dec}(sk,\mathbf C_\Psi)=\Psi(x_1,\dots,x_\ell)
$$

with overwhelming probability over the coin tosses of all the algorithms. $\mathsf{NCCrypt.Eval}$
runs in time $\mathrm{poly}(4^d,\ell,n,\log q)$.

Note that we stated the correctness of homomorphic evaluation on ciphertexts produced by the
secret-key encryption algorithm $\mathsf{NCCrypt.SecEnc}$. A similar lemma can be shown in the case
of public-key encryption, if $\alpha$ is smaller by a factor of $\sqrt{n\log q}$. However, in our
"optimal FHE" scheme in Section 4, we will only need to invoke this lemma with secret-key
encryption.

*Transcription note.* "$\mathbf C_1,\dots,\mathbf C_k$" in the evaluated ciphertext is as printed
($\mathbf C_1,\dots,\mathbf C_\ell$ is meant).

<a id="pdf-eab2d1667a8e-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Proof of Lemma 3.6 (p. 15).** It is easy to see that each step of the homomorphic evaluation
algorithm, given by Eq. (5), simulates the execution of the branching program, given by Eq. (4).
It remains to bound the noise growth during $\mathsf{NCCrypt.Eval}$. We show this by induction.

In the sequel, we will abbreviate the noise function $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)$ to
$\mathsf{noise}(\mathbf C)$ since the secret key is fixed throughout the evaluation, and the message
$\mu$ is clear from the context.

Clearly, $\mathsf{noise}(\mathbf V_{0,i})=0$, since they $\mathbf V_{0,i}$ are just the messages,
with no noise. Assume, as the inductive hypothesis, that for all $i\in\{1,2,3,4,5\}$,

$$
\mathsf{noise}(\mathbf V_{t-1,i})=(t-1)\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

We will now bound $\mathsf{noise}(\mathbf V_{t,i})$ for all $i\in\{1,2,3,4,5\}$. Note that

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr)\Bigr)
+\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)\\
&\le|1-x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_0})+|x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_1})+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

where the second inequality holds by Claim 3.4.2 since all the ciphertexts encrypt bits,
$\mathbf C_{\mathsf{var}(t)}$ is a fresh secret-key encryption, and $\bar{\mathbf C}_{\mathsf{var}(t)}$
contains exactly the same noise as $\mathbf C_{\mathsf{var}(t)}$.

Since exactly one of $x_{\mathsf{var}(t)}$ and $1-x_{\mathsf{var}(t)}$ is non-zero, we have

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\max(\mathsf{noise}(\mathbf V_{t-1,\gamma_0}),\mathsf{noise}(\mathbf V_{t-1,\gamma_1}))+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\\
&\le t\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

by the inductive hypothesis.

Thus, in particular,

$$
\mathsf{noise}(\mathbf V_\Psi)=\mathsf{noise}\bigl(\mathbf V_{L,1}\bigr)\le4^d\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})<q/8
$$

by our setting of the parameter $\alpha$.

*Transcription note.* The second inequality applies Claim 3.4.2 to the two ProtoMult calls, but
the claim has one additive term per call, so the two calls give two such terms; the printed bound
keeps one $\tilde O$ term, which absorbs the factor 2. In the phase-5 Lean's worst-case form
(fresh ciphertext on the left) the step costs an additive $2N\beta$.

<a id="pdf-eab2d1667a8e-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->

**Section 3.4, achieving fully homomorphic encryption; Theorem 3.7 (p. 16).** We know by
Lemma 3.4 that the depth of the decryption circuit of $\mathsf{NCCrypt}$ is
$c_{\mathsf{dec}}\cdot\log(n\log q)=c_{\mathsf{dec}}\log N$ for some constant
$c_{\mathsf{dec}}>0$. Setting the depth $d=c\log N$ for some constant $c>c_{\mathsf{dec}}$ in
Lemma 3.6 and $\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})$ gives us a bootstrappable
encryption scheme. By the bootstrapping theorem (Theorem 2.14), this can be turned into a leveled
FHE scheme, without additional assumptions. We state this theorem below:

**Theorem 3.7.** Let $n$ be the LWE dimension, $q$ be the LWE modulus,
$N:=(n+1)\cdot\lceil\log q\rceil$, and let $c>c_{\mathsf{dec}}$ be a large enough constant (where
$c_{\mathsf{dec}}$ is the decryption depth constant from Proposition 3.4), and

$$
\alpha\le1/\tilde\Theta_\kappa\bigl((n\log q)^{2c+1/2}\bigr)
$$

Then, there is a leveled FHE scheme that is secure under the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$.

In the next section, we will use a variant of the dimension-modulus reduction of [BV11], the
effect of which will be to reduce the constant $c$ above to a very small $\epsilon\to0$, thus
achieving a value of $\alpha$ that matches the best known lattice-based PKE schemes.

*Transcription note.* "Lemma 3.4" in the first sentence is as printed (Proposition 3.4 is meant).
Confidence is lowered because the radicals and tildes are flattened in the extraction.

<a id="pdf-eab2d1667a8e-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.95 -->

**Lemma 4.4.** Let $\alpha(n)=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot n^{\epsilon})$, and let
$q(n)\ge\tilde O(\sqrt n/\alpha(n))$. Consider a set of keys generated by
$(sk,pk,evk)\leftarrow\mathsf{DimReduced.Keygen}(1^k)$, and recall that $sk=(\mathbf s_0,\mathbf s_L)$.
Let $K_i\leftarrow\mathsf{DimReduced.SecEnc}_{sk}(\mathsf{BitDecomp}(\mathbf s_0)[i])$. Namely,
$K_i$ is the symmetric encryption of the $i$th bit of $\mathbf s_0$.

Let $f$ be an augmented decryption circuit as per Definition 2.13. Namely, let
$\mathbf c,\mathbf c'\in\mathbb Z_p^k$ and $\mu,\mu'\in\{0,1\}$ be such that

$$
[\langle\mathbf c,\mathbf s_0\rangle]_p=\mu\cdot\tau p+e,
$$

where $|e|<p/8$, and similarly for $\mathbf c'$. The function $f$ is the function that on input
$x$, treats $x$ as a secret key and decrypts $\mathbf c,\mathbf c'$, and outputs the NAND of their
decryptions.

Let

$$
\mathbf c_0\leftarrow\mathsf{DimReduced.Eval}_{evk}(f,K_1,K_2,\dots),
$$

and note that this is syntactically well defined since $f$ can be represented as a Boolean circuit
of depth $c_{\mathsf{dec}}\cdot\log(k\log(q(k)))+1$.

Then with all but $\mathrm{negl}(\kappa)$ probability,

$$
[\langle\mathbf c_0,\mathbf s_0\rangle]_p=\mu^*\cdot\tau p+e_f,
$$

where $\mu^*=\overline{(\mu\wedge\mu')}$, $|e_f|<p/8$ are as above.

*Transcription note.* The statement is given for the shape of the bootstrapping step (the
evaluation key holds secret-key encryptions $K_i$ of the bits of the secret key; the augmented
decryption circuit has depth $c_{\mathsf{dec}}\cdot\log(\cdot)+1$). $\tau=2^{\lceil\log(q_L)\rceil-2}/q_L$
is defined just before the lemma (p. 18). The radicals and the bar over $(\mu\wedge\mu')$ were
checked against the page image (130 dpi).

<a id="pdf-eab2d1667a8e-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->

**Section 4.2, Corollary 4.5 and the key-size remark (p. 20).** Finally, we derive the worst-case
lattice approximation factor based on Corollary 2.6. We recall that a bootstrappable homomorphic
encryption scheme implies a leveled FHE scheme under the same assumptions, and a pure FHE scheme
with an additional circular security assumption.

**Corollary 4.5.** For all $\epsilon>0$, there exist:

- A bootstrappable homomorphic encryption scheme based on the worst-case quantum hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$ and $\mathsf{SIVP}_{\tilde O(n^{1.5+\epsilon})}$.
- A bootstrappable homomorphic encryption scheme based on the worst-case classical hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

The first (quantum) case is derived from Lemma 4.4 by setting $q(n)=\sqrt n/\alpha(n)=\mathrm{poly}(n)$,
and the second (classical) case is derived by setting $q(n)=2^{n/2}$.

*Improving Key and Ciphertext sizes.* The scheme $\mathsf{DimReduced}$ uses a ladder of LWE
instances, ranging from short $(k,p)$ to polynomially larger $(n,q)$. In the description above, the
public key of the scheme is derived from that of $\mathsf{NCCrypt}$, and therefore depends on $n$
and not on $k$. Likewise, the "input ciphertexts" (the ones before homomorphic evaluation) also
depend on $n$.

We note here that this can be fixed in such a way that only the $evk$ depends on $n$, and the rest
of the parameters are exactly the same as Regev's scheme with parameters $(k,p)$. This is done in a
standard way (used e.g. in [BV11]) as follows.

We will generate the public key as a standard Regev public key with parameters $(k,p)$, and in the
evaluation key we will encrypt the bits of the respective secret key using $\mathsf{NCCrypt}$. This
will allow to perform homomorphic operations by evaluating the augmented decryption circuit.
Namely, the ciphertexts visible to the user of the scheme will always be short, but in the process
of homomorphic evaluation, larger ciphertexts are used to accommodate the homomorphic operation,
and once it is done dimension-modulus reduction will be used to shrink the output ciphertext back
to the original size. Since this is standard practice, we omit the technical description.
