<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Faster Bootstrapping with Polynomial Error

Jacob Alperin-Sheriff and Chris Peikert. *CRYPTO 2014*, LNCS 8616, pp. 297–314; IACR ePrint
2014/094, version dated June 13, 2014 (18 pages; tag `AP14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): §2.2 (symmetric groups and permutation matrices), §3
(the GSW variant: Claim 3.1, Equation (3.1), the scheme, Definitions 3.2–3.3, Claim 3.4,
Lemma 3.5, Corollary 3.6), §4.1–§4.2 (HEPerm, Equation (4.1), Lemma 4.1, Corollary 4.2), and
from §5 the specification, the procedures, Theorem 5.1, the security paragraph and Lemma 5.2
(the phase-6 cross-check). The PDF is not committed. Anchors use the physical PDF page; the
printed page is one less (`p008` is printed page 7). The scoped raw extraction is
`alperin-sheriff-peikert-2014-bootstrapping.raw.md`. Mathematics is set in LaTeX; the
paper's operators are written $\boxplus$ (homomorphic addition), $\boxdot$ (homomorphic
multiplication) and ⧇ (homomorphic composition, printed as a boxed small circle). The wording
is the paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-cecd346d2e87-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.2, symmetric groups and $\mathbb Z_q$-embeddings (printed p. 6).** Here we recall
some basic facts about symmetric groups, which can be found in most abstract algebra textbooks,
e.g., [Jac12]. Let $S_r$ denote the symmetric group of order $r$, i.e., the group of
permutations (bijections) $\pi:\{1,\dots,r\}\to\{1,\dots,r\}$ with function composition as the
group operation. The group $S_r$ is isomorphic to the multiplicative group of $r$-by-$r$
permutation matrices (i.e., 0-1 matrices with exactly one nonzero element in each row and each
column), via the map that associates $\pi\in S_r$ with the permutation matrix
$\mathbf P_\pi=[\mathbf e_{\pi(1)}\ \mathbf e_{\pi(2)}\ \cdots\ \mathbf e_{\pi(r)}]$, where
$\mathbf e_i\in\{0,1\}^r$ is the $i$th standard basis vector. For the remainder of this work we
identify permutations with their associated permutation matrices.

The additive cyclic group $(\mathbb Z_r,+)$ embeds into the symmetric group $S_r$ via the
injective homomorphism that sends the generator $1\in\mathbb Z_r$ to the "cyclic shift"
permutation $\pi\in S_r$, defined as $\pi(i)=i+1$ for $1\le i<r$ and $\pi(r)=1$.³ Clearly, this
embedding and its inverse can be computed efficiently. Notice also that the permutation matrices
in the image of this embedding can be represented more compactly by just their first column,
because the remaining columns are just the successive cyclic shifts of this column. Similarly,
such permutation matrices can be multiplied in only $O(r^2)$ operations, since we only need to
multiply one matrix by the first column of the other.

For our efficient bootstrapping algorithm, we need to efficiently embed a group
$(\mathbb Z_q,+)$, for some sufficiently large $q$ of our choice, into a symmetric group of order
much smaller than $q$ (e.g., polylogarithmic in $q$). This can be done as follows: suppose that
$q=r_1r_2\cdots r_t$, where the $r_i$ are pairwise coprime. Then by the Chinese Remainder
Theorem, the ring $\mathbb Z_q$ is isomorphic to the direct product of rings
$\mathbb Z_{r_1}\times\mathbb Z_{r_2}\times\cdots\times\mathbb Z_{r_t}$, and hence their additive
groups are isomorphic as well. Combining this with the group embeddings of $(\mathbb Z_{r_i},+)$
into $S_{r_i}$, we have an (efficient) group embedding from $(\mathbb Z_q,+)$ into
$S_{r_1}\times S_{r_2}\times\cdots\times S_{r_t}$.⁴

Importantly for our purposes, $q$ can be exponentially large in terms of $\max_i r_i$ above.
This can be shown using lower bounds on the second Chebyshev function

$$
\psi(x):=\sum_{p^k\le x}\log p=\log\Bigl(\prod_{p\le x}p^{\lfloor\log_p x\rfloor}\Bigr),
$$

where the first summation is over all prime powers $p^k\le x$, and the second is over all
primes $p\le x$; note that $p^{\lfloor\log_p x\rfloor}$ is the largest power of $p$ not exceeding
$x$. Therefore, the product $q$ of all maximal prime powers $r_i=p^{\lfloor\log_p x\rfloor}\le x$
is $\exp(\psi(x))$. Asymptotically, it is known that $\psi(x)=x\pm O(x/\log x)$, and we also have
the nonasymptotic bound $\psi(x)\ge 3x/4$ for all $x\ge 7$ [Sch76, Theorem 11]. In summary:

**Lemma 2.2.** For all $x\ge 7$, the product of all maximal prime powers $r_i\le x$ is at least
$\exp(3x/4)$.

For any given lower bound $q_0\ge 191>\exp(21/4)$, we can therefore efficiently find a
$q\ge q_0$ whose maximal prime-power divisors are all at most $x=\frac43\log q_0\ge 7$.

Footnote 3: This is just a special case of Cayley's theorem, which says that any group $G$
embeds into the symmetric group $S_{|G|}$. Footnote 4: The latter group can be seen as a
subgroup of $S_r$ for $r=\sum_i r_i$, but it will be more efficient to retain the product
structure.

<a id="pdf-cecd346d2e87-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

## 3 GSW Cryptosystem

**Section 3, opening (printed p. 6).** Here we present a variant of the Gentry-Sahai-Waters
homomorphic encryption scheme [GSW13] (hereafter called GSW), which we believe is simpler to
understand at a technical level. We also give a tighter analysis of its error growth under
homomorphic operations.

<a id="pdf-cecd346d2e87-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 3.1, background; Claim 3.1 and Equation (3.1) (printed p. 7).** We first recall some
standard background (see, e.g., [MP12] for further details). For a modulus $q$, let
$\ell=\lceil\log_2 q\rceil$ and define the "gadget" (column) vector
$\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell}$. Note that the penultimate entry
$2^{\ell-2}$ of $\mathbf g$ is in the interval $[q/4,q/2)$ mod $q$. It will be convenient to use
the following randomized "decomposition" function.

**Claim 3.1 (Adapted from [MP12]).** There is a randomized, efficiently computable function
$\mathbf g^{-1}:\mathbb Z_q\to\mathbb Z^{\ell}$ such that $\mathbf x\leftarrow\mathbf g^{-1}(a)$
is subgaussian with parameter $O(1)$, and always satisfies $\langle\mathbf g,\mathbf x\rangle=a$.

Briefly, the algorithm described in the claim works as follows (though for our application it is
not necessary to understand its internals): let $\mathbf S\in\mathbb Z^{\ell\times\ell}$ be the
basis of the lattice
$\Lambda^\perp(\mathbf g^t)=\{\mathbf z\in\mathbb Z^\ell:\langle\mathbf g,\mathbf z\rangle=0\in\mathbb Z_q\}$
as constructed in [MP12], whose Gram-Schmidt vectors all have Euclidean norm $O(1)$. Given
$a\in\mathbb Z_q$, run a randomized version of the nearest-plane algorithm [Bab85] with basis
$\mathbf S$ to sample from the coset
$\Lambda^\perp_a(\mathbf g^t)=\{\mathbf x:\langle\mathbf g,\mathbf x\rangle=a\}$, where in each
iteration of the algorithm we choose the coefficient of the $i$th basis vector to have
expectation zero over $\{c_i-1,c_i\}$ for an appropriate $c_i\in\frac1q\mathbb Z\cap[0,1)$. In
particular, the coefficient is subgaussian with parameter $\sqrt{2\pi}$ given any fixed values
of the previous coefficients. The final output $\mathbf x$ is the linear combination of the
(orthogonal) Gram-Schmidt vectors of $\mathbf S$ with these coefficients, and is therefore
subgaussian with parameter $O(1)$.

For vectors and matrices over $\mathbb Z_q$, define the randomized function
$\mathbf G^{-1}:\mathbb Z_q^{n\times m}\to\mathbb Z^{n\ell\times m}$ by applying
$\mathbf g^{-1}$ independently to each entry. Notice that for any
$\mathbf A\in\mathbb Z_q^{n\times m}$, if $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf A)$ then
$\mathbf X$ has subgaussian parameter $O(1)$ and

$$
\mathbf G\cdot\mathbf X=\mathbf A,\qquad\text{where }\mathbf G=\mathbf g^t\otimes\mathbf I_n
=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell}\tag{3.1}
$$

is the block matrix with $n$ copies of $\mathbf g^t$ as diagonal blocks, and zeros elsewhere.

*Transcription note.* Under the standard Kronecker convention $\mathbf g^t\otimes\mathbf I_n$
and $\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)=\mathbf I_n\otimes\mathbf g^t$ differ by a
column permutation; the printed text gives both (Gate 41 audit, roadmap section). The Lean
follows the block-diagonal description.

<a id="pdf-cecd346d2e87-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 3.2, cryptosystem and homomorphic operations: parameters and the two differences
(printed pp. 7–8).** The GSW scheme is parameterized by a dimension $n$, a modulus $q$ with
$\ell=\lceil\log_2 q\rceil$, and some error distribution $\chi$ over $\mathbb Z$ which we assume
to be subgaussian. Formally, the message space is the ring of integers $\mathbb Z$, though for
bootstrapping we only work with ciphertexts encrypting messages in
$\{0,1\}\subset\mathbb Z$. The ciphertext space is
$\mathcal C=\mathbb Z_q^{n\times n\ell}$. For simplicity we present just a symmetric-key scheme,
which is sufficient for our purposes (it can be converted to a public-key or even
attribute-based scheme, as described in [GSW13]).

Our GSW variant differs from the original scheme described in [GSW13] in two main ways:

1. In [GSW13], a ciphertext is a square binary matrix $\mathbf C\in\{0,1\}^{n\ell}$, a secret key
   is a "structured" mod-$q$ vector $\mathbf s\in\mathbb Z_q^{n\ell}$ (having large entries), and
   $\mathbf s$ is an "approximate mod-$q$ eigenvector" of $\mathbf C$, in the sense that
   $\mathbf s^t\mathbf C\approx\mu\mathbf s^t\pmod q$, where $\mu\in\mathbb Z$ is the message.

   In our variant, a ciphertext is a rectangular mod-$q$ matrix
   $\mathbf C\in\mathbb Z_q^{n\times n\ell}$, a secret key is some (unstructured, short) integer
   vector $\mathbf s\in\mathbb Z^n$, and
   $\mathbf s^t\mathbf C\approx\mu\cdot\mathbf s^t\mathbf G\pmod q$, i.e., $\mathbf s$ and
   $\mathbf G^t\mathbf s$ are corresponding left- and right- "approximate singular vectors" of
   $\mathbf C$.

   The difference between these two variants turns out to be purely syntactic, in that we can
   efficiently and "losslessly" switch between them (without needing the secret key). However,
   we believe that our variant leads to simpler notation and easier-to-understand operations and
   analysis.
2. The second difference is more substantial: our homomorphic multiplication procedure uses the
   *randomized* $\mathbf G^{-1}(\cdot)$ operation from Claim 3.1. This yields a few important
   advantages, such as a very tight and simple error analysis using subgaussianity (see
   Lemma 3.5), and the ability to *completely re-randomize* the error in a ciphertext (see
   Corollary 3.6).

*Transcription note.* "$\{0,1\}^{n\ell}$" for the square matrix is as printed (an
$n\ell\times n\ell$ matrix is meant).

<a id="pdf-cecd346d2e87-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.2, the scheme (printed p. 8).** We now describe the scheme formally.

- $\mathsf{GSW.Gen}()$: choose $\bar{\mathbf s}\leftarrow\chi^{n-1}$ and output secret key
  $\mathbf s=(\bar{\mathbf s},1)\in\mathbb Z^n$.
- $\mathsf{GSW.Enc}((\bar{\mathbf s},1),\mu\in\mathbb Z)$: choose
  $\bar{\mathbf C}\leftarrow\mathbb Z_q^{(n-1)\times n\ell}$ and $\mathbf e\leftarrow\chi^m$, let
  $\mathbf b^t=\mathbf e^t-\bar{\mathbf s}^t\bar{\mathbf C}\pmod q$, and output the ciphertext

  $$
  \mathbf C=\begin{pmatrix}\bar{\mathbf C}\\ \mathbf b^t\end{pmatrix}+\mu\mathbf G\in\mathcal C,
  $$

  where $\mathbf G$ is as defined in Equation (3.1). Notice that
  $\mathbf s^t\mathbf C=\mathbf e^t+\mu\cdot\mathbf s^t\mathbf G\pmod q$.
- $\mathsf{GSW.Dec}(\mathbf s,\mathbf C\in\mathcal C)$: let $\mathbf c$ be the penultimate
  column of $\mathbf C$, and output $\mu=\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$, where
  $\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$ indicates whether its argument is closer modulo $q$
  to $0$ or to $2^{\ell-2}$ (the penultimate entry of $\mathbf g$).⁵
- **Homomorphic addition** is defined as $\mathbf C_1\boxplus\mathbf C_2=\mathbf C_1+\mathbf C_2$.
- **Homomorphic multiplication** is defined as
  $\mathbf C_1\boxdot\mathbf C_2\leftarrow\mathbf C_1\cdot\mathbf G^{-1}(\mathbf C_2)$, and is
  *right associative*. Notice that this is a randomized procedure, because $\mathbf G^{-1}$ is
  randomized.

The IND-CPA security of the scheme follows immediately from the assumed hardness of
$\mathsf{LWE}_{n-1,q,\chi}$, where the entries of the secret are drawn from the error
distribution $\chi$ (which is no easier than for a uniformly random secret; see [ACPS09,
Lemma 2]). This is because a fresh ciphertext is just $\mu\mathbf G$ plus a matrix of $n\ell$
independent LWE samples under secret $\bar{\mathbf s}$, which are pseudorandom by assumption and
hence hide $\mu\mathbf G$.

Footnote 5: Note that we can decrypt messages in $\mathbb Z\cap[-\frac q2,\frac q2)$, or any
other canonical set of representatives of $\mathbb Z_q$, by "decoding" $\mathbf s^t\mathbf C$ to
the nearest multiple of $\mathbf s^t\mathbf G$. The above decryption algorithm will be
sufficient for our purposes.

*Transcription note.* "$\mathbf e\leftarrow\chi^m$" is as printed; with $n\ell$ columns,
$m=n\ell$ is meant.

<a id="pdf-cecd346d2e87-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Definition 3.2.** We say that a ciphertext $\mathbf C$ is *designed* to encrypt message
$\mu\in\mathbb Z$ (under a secret key $\mathbf s$) if it is a fresh encryption of $\mu$, or if
$\mathbf C=\mathbf C_1\boxplus\mathbf C_2$ where $\mathbf C_1,\mathbf C_2$ are respectively
designed to encrypt $\mu_1,\mu_2\in\mathbb Z$ and $\mu=\mu_1+\mu_2$, or similarly for homomorphic
multiplication.

<a id="pdf-cecd346d2e87-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->

**Definition 3.3.** We say that a ciphertext $\mathbf C$ that is designed to encrypt
$\mu\in\mathbb Z$ (under $\mathbf s$) has *error* vector $\mathbf e^t\in\mathbb Z^{n\ell}$ if
$\mathbf s^t\mathbf C-\mu\cdot\mathbf s^t\mathbf G=\mathbf e^t\pmod q$.

For convenience later on, we also say the matrix $\mu\mathbf G$ is designed to encrypt $\mu$, and
has error $\mathbf 0$. (This is essentially implied by the above definitions, since $\mu\mathbf G$
is indeed a fresh encryption of $\mu$, assuming that zero is in the support of $\chi$.) The next
claim on the correctness of decryption follows immediately from the fact that
$\mathbf s=(\bar{\mathbf s},1)$ and the penultimate column of $\mathbf G$ is
$(0,\dots,0,2^{\ell-2})$, where $2^{\ell-2}\in[q/4,q/2)\bmod q$.

<a id="pdf-cecd346d2e87-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->

**Claim 3.4.** If $\mathbf C$ is designed to encrypt some $\mu\in\{0,1\}\subset\mathbb Z$, and has
error vector $\mathbf e^t$ whose penultimate coordinate has magnitude less than $q/8$, then
$\mathsf{GSW.Dec}(\mathbf s,\mathbf C)$ correctly outputs $\mu$.

We now analyze the behavior of the error terms under homomorphic operations.

<a id="pdf-cecd346d2e87-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 3.5.** Suppose $\mathbf C_1,\mathbf C_2$ are respectively designed to encrypt
$\mu_1,\mu_2\in\mathbb Z$ and have error vectors $\mathbf e_1^t,\mathbf e_2^t$. Then
$\mathbf C_1\boxplus\mathbf C_2$ has error vector $\mathbf e_1^t+\mathbf e_2^t$, and
$\mathbf C_1\boxdot\mathbf C_2$ has error vector $\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t$,
where $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf C_2)$ is the matrix used in the evaluation of
$\boxdot$. In particular, for any values of $\mathbf C_i,\mathbf e_i,\mu_i$, the latter error
vector is of the form $\mathbf e^t+\mu_1\mathbf e_2^t$, where the entries of $\mathbf e$ are
independent and subgaussian with parameter $O(\|\mathbf e_1\|)$.

Importantly, the error in $\mathbf C_1\boxdot\mathbf C_2$ is quasi-additive and asymmetric with
respect to the errors in $\mathbf C_1,\mathbf C_2$: while the first error vector
$\mathbf e_1^t$ is multiplied by a short (subgaussian) matrix $\mathbf X$, the second error
vector $\mathbf e_2^t$ is only multiplied by the (scalar) message $\mu_1$, which we will ensure
remains in $\{0,1\}$.

<a id="pdf-cecd346d2e87-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Proof of Lemma 3.5.** The first claim is immediate, by linearity. For the second claim, because
$\mathbf G\cdot\mathbf X=\mathbf C_2$ we have

$$
\begin{aligned}
\mathbf s^t(\mathbf C_1\boxdot\mathbf C_2)&=\mathbf s^t\mathbf C_1\cdot\mathbf X\\
&=(\mathbf e_1^t+\mu_1\cdot\mathbf s^t\mathbf G)\mathbf X\\
&=\mathbf e_1^t\mathbf X+\mu_1(\mathbf e_2^t+\mu_2\cdot\mathbf s^t\mathbf G)\\
&=(\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t)+\mu_1\mu_2\cdot\mathbf s^t\mathbf G.
\end{aligned}
$$

<a id="pdf-cecd346d2e87-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->

**Section 3.3, chains (printed p. 9).** As observed in [BV14], the asymmetric noise growth
allows for performing a long chain of homomorphic multiplications while only incurring a
polynomial-factor error growth, because $\boxdot$ is defined to be right associative. For
convenience of analysis, in such a chain we always include the fixed ciphertext $\mathbf G$,
which is designed to encrypt $\mu=1$ and has zero error, as the rightmost ciphertext in the
chain. This ensures that the error vector of the output ciphertext is subgaussian and essentially
independent of the errors in the input ciphertexts (apart from their lengths), which leads to a
simpler and tighter analysis. (In [BV14] a weaker independence guarantee was achieved by a
separate "partial re-randomization" procedure, which requires additional public key material.)

**Corollary 3.6.** Suppose that $\mathbf C_i$ for $i\in[k]$ are respectively designed to
encrypt $\mu_i\in\{0,\pm1\}$ and have error vectors $\mathbf e_i^t$. Then for any fixed values of
these variables,

$$
\mathbf C\leftarrow\mathop{\boxdot}_{i\in[k]}\mathbf C_i\boxdot\mathbf G
=\mathbf C_1\boxdot(\mathbf C_2\boxdot(\cdots(\mathbf C_k\boxdot\mathbf G)\cdots))
$$

has an error vector whose entries are mutually independent and subgaussian with parameter
$O(\|\mathbf e\|)$, where $\mathbf e^t=(\mathbf e_1^t,\dots,\mathbf e_k^t)\in\mathbb Z^{kn\ell}$
is the concatenation of the individual error vectors.

**Proof.** By Lemma 3.5, the error vector in $\mathbf C$ is $\sum_i\mathbf e_i^t\mathbf X_i$,
where each $\mathbf e_i^t\mathbf X_i$ is a fresh independent vector that has mutually
independent coordinates and is subgaussian with parameter $O(\|\mathbf e_i\|)$. The claim then
follows by Pythagorean additivity.

<a id="pdf-cecd346d2e87-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->

## 4 Homomomorphic Encryption for Symmetric Groups

**Section 4, opening (printed p. 9).** Brakerski and Vaikuntanathan [BV14] showed how to use the
GSW encryption scheme to homomorphically compose permutations of five elements (i.e., to
homomorphically compute the group operation in the symmetric group $S_5$) with small additive
noise growth; the use of $S_5$ comes from its essential role in Barrington's theorem [Bar86]. In
[BV14], the homomorphic composition of permutations is intertwined with the evaluation of a
branching program given by Barrington's theorem. Here we give, as a "first-class object," a
homomorphic cryptosystem for any symmetric group $S_r$. The ability to use several different
small values of $r$, along with a homomorphic equality test that we design, will be central to
our bootstrapping algorithm.

*Transcription note.* The section title is printed "Homomomorphic" (sic).

<a id="pdf-cecd346d2e87-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 4.1, HEPerm: encryption, composition (Equation (4.1)) and equality test (printed
p. 10).** We now describe our (symmetric-key) homomorphic encryption scheme for symmetric groups,
called HEPerm. Let $\mathcal C$ denote the ciphertext space for an appropriate instantiation of
the GSW scheme, which we treat as a "black box." A secret key $sk$ for HEPerm is simply a secret
key for the GSW scheme.

- $\mathsf{HEPerm.Enc}(sk,\pi\in S_r)$: let
  $\mathbf P=(p_{i,j})\in\{0,1\}^{r\times r}$ be the permutation matrix associated with $\pi$.
  Output an entry-wise encryption of $\mathbf P$, i.e., the ciphertext

  $$
  \mathbf C=(c_{i,j})\in\mathcal C^{r\times r},\quad\text{where }c_{i,j}\leftarrow\mathsf{Enc}(sk,p_{i,j}).
  $$

(Decryption follows in the obvious manner.) As with the GSW system, we say that a ciphertext
$\mathbf C\in\mathcal C^{r\times r}$ is *designed* to encrypt a permutation $\pi\in S_r$ (or its
permutation matrix $\mathbf P_\pi$) if its $\mathcal C$-entries are designed to encrypt the
corresponding entries of $\mathbf P_\pi$. For convenience, we let
$\mathbf J\in\mathcal C^{r\times r}$ denote the ciphertext that encrypts the identity permutation
with zero noise, which is built in the expected way from the fixed zero-error GSW ciphertexts
that encrypt $0$ and $1$.

We now show how to homomorphically compute two operations: the standard composition operation
for permutations, and an equality test.

**Homomorphic composition $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$:** on ciphertexts
$\mathbf C^\pi=(c^\pi_{i,j}),\mathbf C^\sigma=(c^\sigma_{i,j})\in\mathcal C^{r\times r}$
encrypting permutations $\pi,\sigma\in S_r$ respectively, we compute one encrypting the
permutation $\pi\circ\sigma$ by homomorphically evaluating the naïve matrix-multiplication
algorithm.⁶ That is, output $\mathbf C=(c_{i,j})\in\mathcal C^{r\times r}$ where

$$
c_{i,j}\leftarrow\mathop{\boxplus}_{\ell\in[r]}\bigl(c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}\bigr)\in\mathcal C.\tag{4.1}
$$

Just like $\boxdot$, we define ⧇ to be right associative.

**Homomorphic equality test $\mathsf{Eq?}(\mathbf C^\pi=(c^\pi_{i,j}),\sigma\in S_r)$:** given a
ciphertext encrypting some permutation $\pi\in S_r$ and a permutation $\sigma\in S_r$ (in the
clear), output a ciphertext $c\in\mathcal C$ encrypting $1$ if $\pi=\sigma$ and $0$ otherwise, as

$$
c\leftarrow\mathop{\boxdot}_{i\in[r]}c^\pi_{\sigma(i),i}\boxdot g,
$$

where $g\in\mathcal C$ denotes the fixed zero-error encryption of $1$. (Recall that $\boxdot$ is
right associative.)

Observe that for the above two operations, the GSW ciphertext(s) in the output are designed to
encrypt the appropriate $\{0,1\}$-message. For Compose this is simply by correctness of the
matrix-multiplication algorithm. For Eq? this is because the output ciphertext is designed to
encrypt $1$ if and only if every $c_{\sigma(i),i}$ is designed to encrypt $1$, which is the case
if and only if $\mathbf C^\pi$ is in fact designed to encrypt $\sigma$. All that remains is to
analyze the behavior of the error terms, which we do next.

Footnote 6: Note that asymptotically faster algorithms (e.g., Strassen's) do not appear suitable
here, because the intermediate steps of these algorithms can result in values having magnitude
greater than one, which can cause the error in the ciphertexts to grow much faster. In any case,
this will not matter much in our application, since $r$ will be small.

<a id="pdf-cecd346d2e87-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 4.2, analysis; Lemma 4.1 (printed p. 11).** Recalling that the GSW scheme is
parameterized by $n$ and $q$, denote its space of error vectors by $\mathcal E=\mathbb Z^m$ where
$m=n\lceil\log_2 q\rceil$. The Euclidean norm on $\mathcal E^r=\mathbb Z^{mr}$ is defined in the
expected way. In what follows it is often convenient to consider vectors and matrices over
$\mathcal E$, i.e., each entry is itself a (row) vector in $\mathcal E=\mathbb Z^m$, and we
switch between $\mathcal E^{h\times w}$ and $\mathbb Z^{h\times wm}$ as is convenient.

The following lemma describes the behavior of errors under the homomorphic composition
operation ⧇. Note that working with vectors and matrices over $\mathcal E$ lets us write a
statement that is syntactically very similar to the one from Lemma 3.5, with a very similar
proof.

**Lemma 4.1.** Let $\mathbf C^\pi,\mathbf C^\sigma\in\mathcal C^{r\times r}$ respectively be
designed to encrypt permutation matrices $\mathbf P_\pi,\mathbf P_\sigma\in\{0,1\}^{r\times r}$
with error matrices $\mathbf E_\pi,\mathbf E_\sigma\in\mathcal E^{r\times r}$. Then for any fixed
values of these variables, $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$ has error matrix
$\mathbf E+\mathbf P_\pi\cdot\mathbf E_\sigma\in\mathcal E^{r\times r}$, where the
$\mathbb Z$-entries of $\mathbf E$ are mutually independent, and those in its $i$th row are
subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, where $\mathbf e^\pi_i$ is the $i$th row of
$\mathbf E_\pi$.

**Proof.** Let $\mathbf C\leftarrow\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$. It suffices to show that
for all $i,j$, its $(i,j)$th entry $c_{i,j}\in\mathcal C$ has error

$$
\mathbf e_{i,j}+\mathbf e^\sigma_{\pi^{-1}(i),j}\in\mathcal E=\mathbb Z^m,
$$

where all the $\mathbb Z$-entries of all the $\mathbf e_{i,j}\in\mathbb Z^m$ are mutually
independent and subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, and $\mathbf e^\sigma_{\ell,j}$
is the $(\ell,j)$th entry of $\mathbf E_\sigma$. This follows directly from Equation (4.1) and
Lemma 3.5: the error in each ciphertext $c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}$ is
$p^\pi_{i,\ell}\cdot\mathbf e^\sigma_{\ell,j}$ plus a fresh vector whose entries are independent and
subgaussian with parameter $O(\|\mathbf e^\pi_{i,\ell}\|)$. Since $p^\pi_{i,\ell}=1$ for
$\ell=\pi^{-1}(i)$ and $0$ otherwise, the claim follows by Pythagorean additivity of independent
subgaussians.

<a id="pdf-cecd346d2e87-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 4.2, chains of compositions; Corollary 4.2 (printed p. 11).** Similarly to a
multiplication chain of GSW ciphertexts, we can perform a
(right-associative) chain of compositions while incurring only small error growth. For
convenience of analysis, we always include the fixed zero-error ciphertext
$\mathbf J\in\mathcal C^{r\times r}$ (which encrypts the identity permutation) as the rightmost
ciphertext in the chain. The following corollary follows directly from Lemma 4.1 in the same way
that Corollary 3.6 follows from Lemma 3.5.

**Corollary 4.2.** Suppose that $\mathbf C_i\in\mathcal C^{r\times r}$ for $i\in[k]$ are
respectively designed to encrypt permutation matrices $\mathbf P_i\in\{0,1\}^{r\times r}$ and
have error matrices $\mathbf E_i\in\mathcal E^{r\times r}$. Then for any fixed values of these
variables,

$$
\mathbf C\leftarrow\mathop{\text{⧇}}_{i\in[k]}\mathbf C_i\ \text{⧇}\ \mathbf J
=\mathbf C_1\ \text{⧇}\ (\mathbf C_2\ \text{⧇}\ (\cdots(\mathbf C_k\ \text{⧇}\ \mathbf J)\cdots))
$$

has an error matrix whose $\mathbb Z$-entries are mutually independent, and those in its $i$th
row are subgaussian with parameter $O(\|\mathbf e_i\|)$, where
$\mathbf e_i^t\in\mathcal E^{kr}$ is the $i$th row of the concatenated error matrices
$[\mathbf E_1\mid\cdots\mid\mathbf E_k]$.

Finally, since the $\mathsf{Eq?}$ procedure simply performs a chain of (right-associative)
multiplications of GSW ciphertexts, Corollary 3.6 applies.

<a id="pdf-cecd346d2e87-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

## 5 Bootstrapping

**Section 5 and Section 5.1, specification and usage (printed p. 12).** We now describe our
bootstrapping procedure.

We start by specifying the abstract preconditions and output guarantees of our bootstrapping
algorithm, and describe how to use it (with some additional pre- and post-processing) to
bootstrap known LWE-based encryption schemes.

The scheme to be bootstrapped must have binary ciphertexts in $\{0,1\}^d$ and secret keys in
$\mathbb Z_q^d$ for some dimension $d$ and modulus $q$ that should be made as small as possible
($q,d=\tilde O(\lambda)$ are possible), and a decryption function of the form
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$ for some
arbitrary function $f:\mathbb Z_q\to\{0,1\}$. We rely on an appropriate instantiation of the GSW
cryptosystem, as described in further detail in Section 5.2 below.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$ takes as input a secret key vector
  $\mathbf s\in\mathbb Z_q^d$ from the scheme to be bootstrapped, and a secret key $sk$ for GSW. It
  outputs a bootstrapping key $bk$, which appropriately encrypts $\mathbf s$ under $sk$.
- $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$ takes as input the bootstrapping key $bk$ and a
  ciphertext vector $\mathbf c\in\{0,1\}^d$ (which decrypts under the secret key $\mathbf s$). It
  outputs a GSW ciphertext which decrypts (under $sk$) to the same bit as $\mathbf c$ does (under
  $\mathbf s$), but with less error.

<a id="pdf-cecd346d2e87-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 5.1, pre- and post-processing (printed p. 13).** We can bootstrap all known LWE-based
bit-encryption schemes using the above algorithms as follows. In all LWE-based encryption
schemes, decryption can be expressed as a "rounded inner product"
$\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$ for some appropriate rounding function
$\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$, as required. Note that a GSW ciphertext can
trivially be put in this form by just taking its penultimate column (see $\mathsf{GSW.Dec}$ in
Section 3.2). As for the other conditions we need (binary ciphertexts and small $d,q$), LWE
encryption schemes are not always presented in a way that fulfills them, but fortunately there
are standard transformations that do so, as we now describe. (See [BV11, BLP+13] for further
details.)

First, since we do not need to perform any further homomorphic operations on the ciphertext, we
can use dimension- and modulus-reduction [BV11] to get a ciphertext $\bar{\mathbf c}$ (over
$\mathbb Z_q$) of dimension $\tilde O(\lambda)$ and modulus $q=\tilde O(\lambda)$, while
preserving correct decryption. These steps can be implemented with $2^\lambda$ security under
conventional lattice assumptions.⁷ Then, we can obtain a binary ciphertext $\mathbf c$ using
"bit decomposition:" let $\mathbf G$ be as defined in Section 3.1, and for the ciphertext
$\bar{\mathbf c}$ over $\mathbb Z_q$ under secret key $\bar{\mathbf s}$, let $\mathbf c$ be a
$\{0,1\}$-vector such that $\mathbf G\mathbf c=\bar{\mathbf c}$, and let
$\mathbf s=\mathbf G^t\bar{\mathbf s}$ so that
$\langle\mathbf s,\mathbf c\rangle=\langle\bar{\mathbf s},\bar{\mathbf c}\rangle\in\mathbb Z_q$.
(The secret key $\mathbf s$ is therefore the one we need to provide to $\mathsf{BootGen}$.)

After bootstrapping, the output is a GSW ciphertext $\mathbf C$ encrypted under $sk$ (which is
just an integer vector). If desired, we can convert this ciphertext back to one for the original
LWE cryptosystem, simply by taking the penultimate column of $\mathbf C$. We can also key-switch
from $sk$ back to the original secret key $\mathbf s$. (As usual in bootstrapping, going "full
circle" in this way requires an appropriate circular security assumption.)

Footnote 7: To make the modulus quasi-linear, we need to use randomized (subgaussian) rounding in
the modulus-reduction step.

<a id="pdf-cecd346d2e87-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 5.2, procedures: parameters and $\mathsf{BootGen}$ (printed p. 13).** Our algorithms
rely on instantiations of GSW and HEPerm with parameters $n,Q,\chi$. Importantly, the ciphertext
modulus $Q$ is not the modulus $q$ of the scheme we are bootstrapping, but rather some $Q\gg q$
that is sufficiently larger than the error in Bootstrap's output ciphertext. Let $\mathcal C$
denote the GSW ciphertext space.

Our procedures need $q$ to be of the form $q=\prod_{i\in[t]}r_i$ where the $r_i$ are small and
powers of distinct primes (and hence pairwise coprime). Specifically, using Lemma 2.2 we can
choose $q=\tilde O(\lambda)$ to be large enough by letting it be the product of all maximal
prime-powers $r_i$ that are bounded by $O(\log\lambda)$, of which there are
$t=O(\log\lambda/\log\log\lambda)$. Let $\phi$ be the group embedding of
$(\mathbb Z_q,+)\cong(\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t},+)$ into
$S=S_{r_1}\times\cdots\times S_{r_t}$ described in Section 2.2, and let $\phi_i$ denote the $i$th
component of this embedding, i.e., the one from $\mathbb Z_q$ into $S_{r_i}$.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$: given secret key $\mathbf s\in\mathbb Z_q^d$
  for the scheme to be bootstrapped and a secret key $sk$ for HEPerm, embed each coordinate
  $s_j\in\mathbb Z_q$ of $\mathbf s$ as $\phi(s_j)\in S$ and encrypt the components under HEPerm.
  That is, generate and output the bootstrapping key

  $$
  bk=\{\mathbf C_{i,j}\leftarrow\mathsf{HEPerm.Enc}(sk,\phi_i(s_j)):i\in[t],j\in[d]\}.
  $$

  Recalling that we are working with embeddings of $\mathbb Z_{r_i}$, each
  $\mathbf C_{i,j}\in\mathcal C^{r_i}$ can be represented as a tuple of $r_i$ GSW ciphertexts
  encrypting an indicator vector (see Section 4.3). Because $t,r_i=O(\log\lambda)$ and
  $d=\tilde O(\lambda)$, the bootstrapping key consists of $\tilde O(\lambda)$ GSW ciphertexts.

<a id="pdf-cecd346d2e87-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->

**Section 5.2, $\mathsf{Bootstrap}$: Inner Product and Round, Equations (5.1)–(5.2) (printed
pp. 13–14).** $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$: given a binary ciphertext
$\mathbf c\in\{0,1\}^d$, do the following:

**Inner Product:** Homomorphically compute an encryption of

$$
v=\langle\mathbf s,\mathbf c\rangle=\sum_{j\,:\,c_j=1}s_j\in\mathbb Z_q
$$

using the encryptions of the $s_j\in\mathbb Z_q$ as embedded into the permutation group $S$, via
a chain of compositions. Formally, for each $i\in[t]$ compute (recalling that ⧇ is right
associative, and $\mathbf J$ is the fixed HEPerm encryption of the identity permutation)

$$
\mathbf C_i\leftarrow\mathop{\text{⧇}}_{j\text{ s.t. }c_j=1}\mathbf C_{i,j}\ \text{⧇}\ \mathbf J.\tag{5.1}
$$

Again, because we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathbf C_i\in\mathcal C^{r_i}$.

**Round:** Homomorphically map $v\in\mathbb Z_q$ to $f(v)\in\mathbb Z_2=\{0,1\}$: for each
$x\in\mathbb Z_q$ such that $f(x)=1$, homomorphically test whether $v\stackrel?=x$ by
homomorphically multiplying the GSW ciphertexts resulting from all the equality tests
$v\stackrel?=x\pmod{r_i}$. Then homomorphically sum the results of all the $v\stackrel?=x$ tests.

Formally, compute and output the GSW ciphertext (recalling that $\boxdot$ is right associative,
and $\mathbf G$ is the fixed GSW encryption of $1$)

$$
\mathbf C\leftarrow\mathop{\boxplus}_{x\in\mathbb Z_q\text{ s.t. }f(x)=1}
\Bigl(\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G\Bigr).\tag{5.2}
$$

Note that since we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathsf{Eq?}(\mathbf C_i,\phi_i(x))$ is just some GSW ciphertext component of
$\mathbf C_i\in\mathcal C^{r_i}$ (see Section 4.3).

Because $t,r_i=O(\log\lambda)$ and $d=\tilde O(\lambda)$ and by Equations (5.1) and (5.2),
Bootstrap performs $\tilde O(\lambda)$ homomorphic multiplications and additions on GSW
ciphertexts.

<a id="pdf-cecd346d2e87-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Theorem 5.1.** The above bootstrapping scheme can be instantiated to be correct (with
overwhelming probability) and secure assuming that the decisional Shortest Vector Problem
(GapSVP) and Shortest Independent Vectors Problem (SIVP) are (quantumly) hard to approximate in
the worst case to within $\tilde O(n^2\lambda)$ factors on $n$-dimensional lattices.

Because all known (quantum) algorithms for $\mathrm{poly}(n)$-factor approximations to GapSVP
and SIVP on $n$-dimensional lattices take $2^{\Omega(n)}$ time, for $2^\lambda$ hardness we can
take $n=\Theta(\lambda)$, yielding a final approximation factor of $\tilde O(n^3)$. This comes
quite close to the $O(n^{3/2+\epsilon})$ factors obtained in [BV14], but without any expensive
"dimension leveraging:" we use GSW ciphertexts of dimension only $n=O(\lambda)$, rather than
some large polynomial in $\lambda$. Alternatively, at the cost of a larger dimension
$n=\lambda^{1/\epsilon}$, but without using the successive dimension-reduction procedure from
[BV14], we can obtain factors as small as $\tilde O(n^{2+\epsilon})$ for any constant
$\epsilon>0$.

The remainder of this subsection is devoted to proving the above theorem.

<a id="pdf-cecd346d2e87-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Section 5.3, security (printed p. 14).** If the HEPerm key $sk$ is generated independently of
$\mathbf s$, then IND-CPA security of the bootstrapping key follows immediately from the security
of HEPerm, hence from LWE with parameters $n-1,Q,\chi$, and finally from worst-case lattice
problems. (We instantiate these parameters below to obtain the claimed approximation factors.) As
usual, if the keys are not independent, then we need to make an appropriate circular security
assumption. (To date, such an assumption is the only known way to obtain unbounded FHE.)

<a id="pdf-cecd346d2e87-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.95 -->

**Lemma 5.2 (Correctness).** For $bk\leftarrow\mathsf{BootGen}(\mathbf s,sk)$, the GSW ciphertext
$\mathbf C\leftarrow\mathsf{Bootstrap}(bk,\mathbf c)$ is designed to encrypt
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$.

**Proof.** First, by construction the HEPerm ciphertext $\mathbf C_{i,j}$ is designed to encrypt
$\phi_i(s_j)$. Therefore, because $\phi_i:\mathbb Z_q\to S_{r_i}$ is a group homomorphism, the
ciphertext $\mathbf C_i$ as defined in Equation (5.1) is designed to encrypt
$\phi_i(\sum_{j:c_j=1}s_j)=\phi_i(\langle\mathbf s,\mathbf c\rangle)=\phi_i(v)$. By correctness
of Eq? and the isomorphism $\mathbb Z_q\cong\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t}$
given by Chinese Remainder Theorem, the homomorphic product
$\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G$ is designed to
encrypt $1$ if and only if $v=x$. Finally, because the homomorphic sum is taken over every
$x\in\mathbb Z_q$ such that $f(x)=1$, it is designed to encrypt $1$ if and only if $f(v)=1$.
