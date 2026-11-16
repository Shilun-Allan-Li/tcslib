<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: d3e95f9b9e017ea1133064bed227981ec21e38ee6fc6163eb08585dd238b0c00 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Efficient Fully Homomorphic Encryption from (Standard) LWE

Zvika Brakerski and Vinod Vaikuntanathan. *FOCS 2011*, pp. 97–106; full version, 39 pages, PDF
created 2 March 2012 (IACR ePrint 2011/344; tag `BV11`). The version facts are from the PDF's
first page ("A preliminary version appeared in Proceedings of the 52nd IEEE Foundations of
Computer Science, 2011") and its creation date; the ePrint number is from BV14's bibliography.

**Scope.** Only the passages that the phase-6 plan uses are transcribed (DW-7; GSW rulings,
addendum): §3.1 (the syntax of homomorphic encryption, Definitions 3.1–3.6), §3.2 (Definition 3.7,
Theorems 3.1–3.2, Definition 3.8 weak circular security, Lemma 3.3), and §4.5 (Lemma 4.5, the
decryption-depth lemma, with its proof; Lemma 4.6; Corollary 4.7). The PDF is not committed.
Anchors use the physical PDF page; the printed page is one less (`p013` is printed page 12). The
scoped raw extraction is `brakerski-vaikuntanathan-2011-fhe.raw.md`. Mathematics is set in LaTeX;
the wording is the paper's. Notes marked *Transcription note* are not part of the source.

**Numbering.** BV14 cites the decryption-depth result as "[BV11, Lemma 4.1]" (BV14,
Proposition 3.4). In this full version it is **Lemma 4.5**; Lemma 4.1 does not occur here (§4
has Theorem 4.1, security). Citations in TCSlib use this version's numbering.

<a id="pdf-d3e95f9b9e01-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

## 3 Homomorphic Encryption: Definitions and Tools

**Section 3 and Section 3.1, opening; key generation (printed p. 11).** In this section we discuss
the definition of homomorphic encryption and its properties as well as some related subjects. We
start by defining homomorphic and fully homomorphic encryption in Section 3.1. Then, in Section 3.2
we discuss Gentry's bootstrapping theorem.

We note that there are a number of ways to define homomorphic encryption and to describe the
bootstrapping theorem. We chose the definitions that best fit the constructions and we urge even
the knowledgeable reader to go over them so as to avoid confusion in interpreting our results.

We now define homomorphic encryption and its desired properties. Throughout this section (and this
work) we use $\kappa$ to indicate the security parameter. In addition, all schemes in this paper
encrypt bit-by-bit and therefore our definitions only refer to this case. The generalization to an
arbitrary message space is immediate.

A homomorphic (public-key) encryption scheme
$\mathsf{HE}=(\mathsf{HE.Keygen},\mathsf{HE.Enc},\mathsf{HE.Dec},\mathsf{HE.Eval})$ is a quadruple
of ppt algorithms as follows.

- **Key generation.** The algorithm $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$ takes a
  unary representation of the security parameter and outputs a public encryption key $pk$, a
  public evaluation key $evk$ and a secret decryption key $sk$.

<a id="pdf-d3e95f9b9e01-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

**Section 3.1, encryption, decryption, evaluation (printed p. 12).**

- **Encryption.** The algorithm $c\leftarrow\mathsf{HE.Enc}_{pk}(\mu)$ takes the public key $pk$ and
  a single bit message $\mu\in\{0,1\}$ and outputs a ciphertext $c$.
- **Decryption.** The algorithm $\mu^*\leftarrow\mathsf{HE.Dec}_{sk}(c)$ takes the secret key $sk$
  and a ciphertext $c$ and outputs a message $\mu^*\in\{0,1\}$.
- **Homomorphic evaluation.** The algorithm
  $c_f\leftarrow\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell)$ takes the evaluation key $evk$, a
  function $f:\{0,1\}^\ell\to\{0,1\}$ and a set of $\ell$ ciphertexts $c_1,\dots,c_\ell$, and
  outputs a ciphertext $c_f$.

  The representation of the function $f$ is an important issue. Since the representation can vary
  between schemes, we leave this issue outside of this syntactic definition. We remark, however,
  that in this work, $f$ will be represented by an arithmetic circuit over $GF(2)$.

We note that while one can treat the evaluation key as a part of the public key, as has been done in
the literature so far, we feel that there is an expository value to treating it as a separate
entity and to distinguishing between the public elements that are used for encryption and those
that are used only for homomorphic evaluation.

The only security notion we consider in this chapter is semantic security, namely security w.r.t.
passive adversaries. We use its widely known formulation as IND-CPA security, defined as follows.

<a id="pdf-d3e95f9b9e01-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->

**Definition 3.1 (CPA security).** A scheme $\mathsf{HE}$ is IND-CPA secure if for any polynomial
time adversary $\mathcal A$ it holds that

$$
\mathrm{Adv}_{\mathrm{CPA}}[\mathcal A]\triangleq\bigl|\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]-\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]\bigr|=\mathrm{negl}(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$.

In fact, based on the best known about lattices, the schemes we present in this paper will be secure
against even stronger adversaries. In order for our reductions to make sense for such adversaries as
well, we also consider a parameterized version of CPA security. There, we allow the adversary to run
in time $t$ (which is typically super-polynomial) and succeed with probability $\epsilon$ (which is
typically sub-polynomial).

*Transcription note.* Both probabilities are printed with $\mathsf{HE.Enc}_{pk}(0)$ (checked
against the page image, 110 dpi); the second is meant to be $\mathsf{HE.Enc}_{pk}(1)$. The same
holds in Definition 3.2.

<a id="pdf-d3e95f9b9e01-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->

**Definition 3.2 ($(t,\epsilon)$-CPA security).** A scheme $\mathsf{HE}$ is $(t,\epsilon)$-IND-CPA
secure if for any adversary $\mathcal A$ that runs in time $t$ for $t=t(\kappa)$ it holds that

$$
\mathrm{Adv}_{\mathrm{CPA}}[\mathcal A]\triangleq\bigl|\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]-\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]\bigr|\le\epsilon=\epsilon(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$.

We move on to define the homomorphism property. Note that we do not define the "correctness" of the
scheme as a separate property, but rather (some form of) correctness will follow from our
homomorphism properties.

We start by defining $\mathcal C$-homomorphism, which is homomorphism with respect to a specified
class $\mathcal C$ of functions. This notion is sometimes also referred to as "somewhat
homomorphism".

<a id="pdf-d3e95f9b9e01-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->

**Definition 3.3 ($\mathcal C$-homomorphism).** Let $\mathcal C=\{\mathcal C_\kappa\}_{\kappa\in\mathbb N}$
be a class of functions (together with their respective representations). A scheme $\mathsf{HE}$ is
$\mathcal C$-homomorphic (or, homomorphic for the class $\mathcal C$) if for any sequence of
functions $f_\kappa\in\mathcal C_\kappa$ and respective inputs $\mu_1,\dots,\mu_\ell\in\{0,1\}$
(where $\ell=\ell(\kappa)$), it holds that

$$
\Pr\left[\mathsf{HE.Dec}_{sk}(\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell))\neq f(\mu_1,\dots,\mu_\ell)\right]=\mathrm{negl}(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$ and $c_i\leftarrow\mathsf{HE.Enc}_{pk}(\mu_i)$.

<a id="pdf-d3e95f9b9e01-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 3.1, remarks; Definitions 3.4–3.6 (printed p. 13).** We point out two important
properties that the above definition *does not* require. First of all, we do not require that the
ciphertexts $c_i$ are decryptable themselves, only that they become decryptable after homomorphic
evaluation.¹⁷ Secondly, we do not require that the output of $\mathsf{HE.Eval}$ can undergo
additional homomorphic evaluation.¹⁸

Before we define full homomorphism, let us define the notion of *compactness*.

**Definition 3.4 (compactness).** A homomorphic scheme $\mathsf{HE}$ is compact if there exists a
polynomial $s=s(\kappa)$ such that the output length of $\mathsf{HE.Eval}(\cdots)$ is at most $s$
bits long (regardless of $f$ or the number of inputs).

Note that a $\mathcal C$-homomorphic scheme is not necessarily compact.

We give the minimal definition of fully homomorphic encryption, which suffices for most
applications.

**Definition 3.5 (fully homomorphic encryption).** A scheme $\mathsf{HE}$ is fully homomorphic if it
is both compact and homomorphic for the class of all arithmetic circuits over $GF(2)$.

As in the definition of $\mathcal C$ homomorphism, one can require that the outputs of
$\mathsf{HE.Eval}$ can again be used as inputs for homomorphic evaluation ("multi-hop
homomorphism"). Indeed, all known schemes have this additional property. However, due to the
complexity of the formal definition in this case, we refrain from describing a formal definition.

An important relaxation of fully homomorphic encryption is the following.

**Definition 3.6 (leveled fully homomorphic encryption).** A leveled fully homomorphic encryption
scheme is a homomorphic scheme where the $\mathsf{HE.Keygen}$ gets an additional input $1^L$ (now
$(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa,1^L)$) and the resulting scheme is homomorphic
for all depth-$L$ binary arithmetic circuits. The bound $s(\kappa)$ on the ciphertext length must
remain independent of $L$.

In most cases, the only parameter of the scheme that becomes dependent on $L$ is the bit-length of
the evaluation key $evk$.

Footnote 17: Jumping ahead, while this may seem strange at first, this notion of somewhat
homomorphism is all that is really required in order to bootstrap into full homomorphism and it
also makes our schemes easier to describe. Lastly, note that one can always perform a "blank"
homomorphic operation and then decrypt, so functionality is not hurt. Footnote 18: This is termed
"1-hop homomorphism" in [GHV10a].

<a id="pdf-d3e95f9b9e01-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.2, Gentry's bootstrapping technique; Definition 3.7 (printed p. 13).** In this section
we formally define the notion of a bootstrappable encryption scheme and present Gentry's
bootstrapping theorem [Gen09b, Gen09a] which implies that a bootstrappable scheme can be converted
into a fully homomorphic one.

**Definition 3.7 (bootstrappable encryption scheme).** Let $\mathsf{HE}$ be
$\mathcal C$-homomorphic, and Let $f_{\mathsf{add}}$ and $f_{\mathsf{mult}}$ be the the augmented
decryption functions of the scheme defined as

$$
f^{c_1,c_2}_{\mathsf{add}}(s)=\mathsf{HE.Dec}_s(c_1)\ \mathit{XOR}\ \mathsf{HE.Dec}_s(c_2)
\qquad\text{and}\qquad
f^{c_1,c_2}_{\mathsf{mult}}(s)=\mathsf{HE.Dec}_s(c_1)\ \mathit{AND}\ \mathsf{HE.Dec}_s(c_2).
$$

Then $\mathcal E$ is bootstrappable if

$$
\bigl\{f^{c_1,c_2}_{\mathsf{add}},f^{c_1,c_2}_{\mathsf{mult}}\bigr\}_{c_1,c_2}\subseteq\mathcal C.
$$

Namely, the scheme can homomorphically evaluate $f_{\mathsf{add}}$ and $f_{\mathsf{mult}}$.

*Transcription note.* BV11 bootstraps with the XOR/AND pair; BV14 (Definition 2.13) uses NAND.
"$\mathcal E$" in "Then $\mathcal E$ is bootstrappable" is as printed ($\mathsf{HE}$ is meant).

<a id="pdf-d3e95f9b9e01-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Section 3.2, Theorems 3.1–3.2, Definition 3.8, Lemma 3.3 (printed p. 14).** We describe two
variants of Gentry's bootstrapping theorem. The first implies leveled fully homomorphic encryption
but requires no additional assumption; where the second makes an additional (weak) circular
security assumption and achieves the stronger (non-leveled) variant of Definition 3.5.

The first variant follows.

**Theorem 3.1 ([Gen09b, Gen09a]).** Let $\mathsf{HE}$ be a bootstrappable scheme, then there exists a
leveled fully homomorphic encryption scheme as per Definition 3.6.

Specifically, the leveled homomorphic scheme is such that only the length of the evaluation key
depends on the level $L$. All other parameters of the scheme are distributed identically regardless
of the value of $L$.

For the second variant, we need to define circular security.

**Definition 3.8 (weak circular security).** A public key encryption scheme
$(\mathsf{Gen},\mathsf{Enc},\mathsf{Dec})$ is weakly circular secure if it is IND-CPA secure even for
an adversary with auxiliary information containing encryptions of all secret key bits:
$\{\mathsf{Enc}_{pk}(sk[i])\}_i$.

Namely, no polynomial time adversary can distinguish an encryption of $0$ from an encryption of $1$
even given the additional information.

We can now state the second theorem.

**Theorem 3.2 ([Gen09b, Gen09a]).** Let $\mathsf{HE}$ be a bootstrappable scheme that is also weakly
circular secure. Then there is a fully homomorphic encryption scheme as per Definition 3.5.

Finally, we want to make a statement regarding the ciphertext length of a bootstrapped scheme. The
following is implicit in [Gen09b, Gen09a].

**Lemma 3.3.** If a scheme $\mathsf{FH}$ is obtained from applying either Theorem 3.1 or Theorem 3.2
to a bootstrappable scheme $\mathsf{HE}$, then both $\mathsf{FH.Enc}$ and $\mathsf{FH.Eval}$ produce
ciphertexts of the same length as $\mathsf{HE.Eval}$ (regardless of the length of the ciphertext
produced by $\mathsf{HE.Enc}$).

<a id="pdf-d3e95f9b9e01-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.95 -->

**Section 4.5, bootstrapping and full homomorphism; Lemma 4.5 (printed p. 28).** We now show how to
apply Gentry's bootstrapping theorem (Theorems 3.1, 3.2) to achieve full homomorphism. In order to
do this, we first need to bound the complexity of an augmented decryption circuit. Since our
decryption is essentially a computation of inner product, we bound the complexity of this operation.

**Lemma 4.5.** Let $(\hat{\mathbf v},\hat w)\in\mathbb Z_p^k\times\mathbb Z_p$. There exists an
arithmetic circuit with fan-in 2 gates and $O(\log k+\log\log p)$ depth, that on input
$\hat{\mathbf s}\in\mathbb Z_p^k$ (in binary representation) computes

$$
(\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\pmod p)\pmod 2.
$$

<a id="pdf-d3e95f9b9e01-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.95 -->

**Proof of Lemma 4.5 (printed p. 28).** We let $\hat{\mathbf s}[i]^{(j)}$ denote the $j$th bit of the
binary representation of $\hat{\mathbf s}[i]\in\mathbb Z_p$. We notice that

$$
\begin{aligned}
\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle
&=\hat w-\sum_{i=1}^{k}\hat{\mathbf s}[i]\hat{\mathbf v}[i]\pmod p\\
&=\hat w-\sum_{i=1}^{k}\sum_{j=0}^{\lfloor\log p\rfloor}\hat{\mathbf s}[i]^{(j)}\cdot(2^j\cdot\hat{\mathbf v}[i])\pmod p.
\end{aligned}
$$

Therefore computing $\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\pmod p$ is equivalent to
summing up $k(1+\lfloor\log p\rfloor)+1$ numbers in $\mathbb Z_p$, and then taking the result modulo
$p$. The summation (over the integers) can be done in depth $O(\log k+\log\log p)$. In order to take
modulo $p$, one needs to subtract, in parallel, all possible multiples of $p$ (there are at most
$O(k\log p)$ options) and check if the result is in $\mathbb Z_p$. This requires depth
$O(\log k+\log\log p)$ again. Then a selection tree of depth $O(\log k+\log\log p)$ is used to
choose the correct result. Once this is done, outputting the least significant bit implements the
final modulo 2 operation.

The total depth is thus $O(\log k+\log\log p)$ as required.

<a id="pdf-d3e95f9b9e01-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.95 -->

**Lemma 4.6 and Corollary 4.7 (printed p. 28).** We can now apply the bootstrapping theorem to obtain
a fully homomorphic scheme.

**Lemma 4.6.** There exists $C\in\mathbb N$ such that setting $n=k^{C/\epsilon}$ and the rest of the
parameters as in Theorem 4.2, BTS is bootstrappable as per Definition 3.7.

**Proof.** Lemma 4.5 guarantees that the decryption circuit is in $\mathrm{Arith}[O(\log k),1]$ (note
that $\log\log p=o(\log k)$), since the augmented decryption circuit just adds 1 to the depth, it
follows that the augmented decryption circuits are also in $\mathrm{Arith}[O(\log k),1]$.

Theorem 4.2, on the other hand, guarantees homomorphism for any
$\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$ function. Taking a large enough $C$, it will hold
that $\mathrm{Arith}[O(\log k),1]\subseteq\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$ and the
lemma follows.

Finally, we conclude that there exists an LWE based fully homomorphic encryption based on
Theorem 4.1 and Lemma 4.6.

**Corollary 4.7.** There exists a leveled fully homomorphic encryption based on the
$\mathsf{DLWE}_{n,q,\chi}$ and $\mathsf{DLWE}_{k,p,\hat\chi}$ assumptions.

Furthermore, if BTS is weakly circular secure (see Definition 3.8), then there exists a fully
homomorphic encryption based on the same assumptions.

*Transcription note.* In Lemma 4.6 and its proof the extraction drops the $\epsilon$ glyphs and the
radical; they were checked against the page image (130 dpi): $n=k^{C/\epsilon}$,
$\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$. Lemma 4.5's decryption
outputs the least significant bit of $\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\bmod p$
(BV11's BTS scheme encrypts in the low-order bit), unlike GSW's rounding to the nearer of $0$ and
$\lfloor q/2\rfloor$; the depth argument (iterated addition, then reduction modulo $p$ by parallel
subtraction and a selection tree) is the part the phase-6 plan uses.
