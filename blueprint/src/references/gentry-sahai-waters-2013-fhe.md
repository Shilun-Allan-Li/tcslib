<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based

Craig Gentry, Amit Sahai and Brent Waters. *CRYPTO 2013*, LNCS 8042, pp. 75–92; full version
IACR ePrint 2013/340, version dated 8 June 2013 (25 pages; tag `GSW13`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan cite are
transcribed (DW-7; GSW ruling Q14): the bootstrapping remark of §1.2, §1.3.1–§1.3.4, §2.3, and
§3.1–§3.4. The PDF is not committed. Physical and printed pages coincide. The scoped raw
extraction is `gentry-sahai-waters-2013-fhe.raw.md`. Mathematics is set in LaTeX (the paper's
arrows over vectors are kept as $\vec v$); the wording is the paper's. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-8edb94cfd852-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Section 1.2, bootstrapping and circular security (p. 4).** As with all current FHE schemes
without bootstrapping, the parameters and per-gate complexity of evaluation depend on the
multiplicative depth $L$ of the circuit. "Bootstrapping" [Gen09], together with an assumption
of circular security, remains the only known way of making these performance metrics
independent of $L$, and while the overhead of bootstrapping is high, it becomes an attractive
option once $L$ passes some threshold. However, our scheme loses some of its advantages once
bootstrapping is used. First, to apply bootstrapping, the evaluator needs to obtain the user's
secret key encrypted under its public key – in effect, an evaluation key – and therefore we no
longer achieve identity-based/attribute-based FHE in this context. Second, this encrypted
secret key has quasi-cubic size in our scheme, and while this can be mitigated by public key
compression techniques [CNT12], it eliminates the space complexity advantages of our scheme.
Essentially, bootstrapping returns us to the realm of "unnatural" operations, with all of its
disadvantages. It remains a fascinating open problem to find some "natural" alternative to
bootstrapping, and (relatedly) to achieve "pure" FHE without an assumption of circular
security.

<a id="pdf-8edb94cfd852-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

## 1.3 An Overview of Our FHE Scheme

**Section 1.3 and Section 1.3.1, homomorphic operations (pp. 4–5).** Our main insight is that we
can achieve LWE-based homomorphic encryption where homomorphic addition and multiplication
correspond directly to matrix addition and multiplication.

Let us skip key generation and encryption for the moment, and jump directly to the homomorphic
operations (and decryption).

In our scheme, for some modulus $q$ and dimension parameter $N$ to be specified later, a
ciphertext $C$ is a $N\times N$ matrix over $\mathbb Z_q$, with "small" entries (much smaller
than $q$) and the secret key $\vec v$ is a $N$-dimensional vector over $\mathbb Z_q$ with at
least one "big" coefficient $v_i$. We restrict the message $\mu$ to be a "small" integer. We
say $C$ encrypts $\mu$ when $C\cdot\vec v=\mu\cdot\vec v+\vec e$, where $\vec e$ is a "small"
error vector. To decrypt, we extract the $i$-th row $C_i$ from $C$, compute
$x\leftarrow\langle C_i,\vec v\rangle=\mu\cdot v_i+e_i$, and output $\mu=\lfloor x/v_i\rceil$.
In a nutshell, the essence of our scheme is that the secret key $\vec v$ is an approximate
eigenvector of the ciphertext matrix $C$, and the message $\mu$ is the eigenvalue.

Now, let us see why matrix addition and multiplication are correct homomorphic operations.
Suppose $C_1$ and $C_2$ encrypt $\mu_1$ and $\mu_2$ in that
$C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ for small $\vec e_i$. Let $C^+=C_1+C_2$ and
$C^\times=C_1\cdot C_2$. For addition, we have
$C^+\cdot\vec v=(\mu_1+\mu_2)\cdot\vec v+(\vec e_1+\vec e_2)$, where the error likely has grown
a little, as usual in FHE schemes. But assuming the error is still "small", the sum of the
ciphertext matrices encrypts the sum of the messages. For multiplication, we have

$$
\begin{aligned}
C^\times\cdot\vec v&=C_1\cdot(\mu_2\cdot\vec v+\vec e_2)
=\mu_2\cdot(\mu_1\cdot\vec v+\vec e_1)+C_1\cdot\vec e_2
=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2\\
&=\mu_1\cdot\mu_2\cdot\vec v+\text{small}
\end{aligned}
$$

where the final error vector is hopefully "small", since $\mu_2$, $C_1$, $\vec e_1$, and
$\vec e_2$ are all small. If so, the product of the ciphertext matrices encrypts the product of
the messages. Interestingly, $C_2\cdot C_1$ is also an encryption of $\mu_1\cdot\mu_2$, even
though matrix multiplication is not commutative.

To simplify further, it might be helpful to imagine an error-free version of the scheme, where
$C_i\cdot\vec v=\mu_i\cdot\vec v$ exactly. In this case, the key $\vec v$ is an (exact)
eigenvector of ciphertext matrices, and the message $\mu_i$ is the eigenvalue. In general, if
matrices $C_1$ and $C_2$ have a common eigenvector $\vec v$ with eigenvalues $\mu_1$ and
$\mu_2$, then $C_1\cdot C_2$ and $C_2\cdot C_1$ have eigenvector $\vec v$ with eigenvalue
$\mu_1\cdot\mu_2$.

<a id="pdf-8edb94cfd852-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Section 1.3.1, end (p. 5).** Of course, in our scheme, the secret key $\vec v$ is only an
approximate eigenvector, not an exact one. Introducing error is necessary to base the security
of our scheme on LWE. The cost of making $\vec v$ only an approximate eigenvector is that
certain terms in our scheme must be "small" to ensure that homomorphic operations do not
disrupt the essential form of the ciphertexts. We call our new approach to LWE-based
(homomorphic) encryption the approximate eigenvector method.

<a id="pdf-8edb94cfd852-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

**Section 1.3.2, bounding the error and somewhat homomorphic encryption (p. 5).** Although we
have not fully specified the scheme, let us go ahead and estimate how homomorphic it is. The
scheme above works correctly until the coefficients of the error vector begin to approach $q$
in magnitude. How many homomorphic operations can we perform before that happens?

Suppose $C_1$ and $C_2$ are $B$-bounded ciphertexts, in the sense that $\mu_i$ and the
coefficients of $C_i$ and $\vec e_i$ all have magnitude at most some bound $B$. Then, $C^+$ is
$2B$-bounded, and $C^\times$ is $(N+1)B^2$-bounded. In short, the error level grows worse than
$B^{2^L}$, doubly exponentially with the multiplicative depth $L$ of the circuit being
evaluated. Alternatively, if one wants to consider the degree (rather than depth) of functions
that can be evaluated, if we evaluate a multivariate polynomial $P(x_1,\dots,x_t)$ of total
degree $d$, on $B$-bounded ciphertexts as input, the final ciphertext is
$|P|(N+1)^{d-1}B^{d}$-bounded, where $|P|$ is the $\ell_1$-norm of $P$'s coefficient vector.
Taking $q$ to comfortably exceed this bound, we (roughly) can evaluate polynomials of degree
$\log_{NB}q$. Since $q/B$ must be subexponential (at most) in $N$ for security reasons, our
scheme-so-far can only evaluate polynomials of (sublinear) polynomial degree in $N$ (only
logarithmic depth). In short, our scheme-so-far is a somewhat homomorphic encryption (SWHE)
scheme [Gen09] that can evaluate log-depth or polynomial degree. Though not yet fully
homomorphic, it is by far the most homomorphic LWE-based encryption scheme that uses only
"natural" homomorphic operations.

*Transcription note.* The superscripts $(N+1)B^2$ and $B^{2^L}$ are flattened in the
extraction and were checked against the page image (140 dpi); $\log_{NB}q$ is read from the
layout.

<a id="pdf-8edb94cfd852-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->

**Section 1.3.3, flattening ciphertexts and fully homomorphic encryption (pp. 5–6).** To obtain
a leveled FHE scheme that can evaluate circuits of polynomial depth without bootstrapping or
techniques like relinearization, we need to ensure better bounds on the growth of the error. Let
us say that a ciphertext $C$ is $B$-strongly-bounded if its associated $\mu$ and the
coefficients of $C$ all have magnitude at most $1$, while the coefficients of its $\vec e$ all
have magnitude at most $B$. If we evaluate a NAND gate on $B$-strongly-bounded ciphertexts
$C_1,C_2$ to obtain a new ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ (where $I_N$ is the
$N$-dimensional identity matrix), then the message remains in $\{0,1\}$, and the coefficients of
$C_3$'s error vector have magnitude at most $(N+1)B$. If we could somehow additionally ensure
that $C_3$'s coefficients have magnitude at most $1$ so that strong-boundedness is preserved,
then we could evaluate a circuit of depth $L$ while keeping the error magnitude at most
$(N+1)^{L}B$. Setting $q/B$ to be subexponential in $N$, we could evaluate a circuit of
polynomial depth rather than merely polynomial degree. In short, we would have a leveled FHE
scheme.

Here we describe a operation called ciphertext flattening that keeps ciphertexts strongly
bounded, so that we obtain leveled FHE.

Flattening uses some simple transformations from [BV11b, BGV12, Bra12] that modify vectors
without affecting dot products. Let $\vec a,\vec b$ be vectors of some dimension $k$ over
$\mathbb Z_q$. Let $\ell=\lfloor\log_2 q\rfloor+1$ and $N=k\cdot\ell$. Let
$\mathrm{BitDecomp}(\vec a)$ be the $N$-dimensional vector
$(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, where $a_{i,j}$ is the $j$-th bit
in $a_i$'s binary representation, bits ordered least significant to most significant. For
$\vec a'=(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, let
$\mathrm{BitDecomp}^{-1}(\vec a')=(\sum 2^j\cdot a_{1,j},\dots,\sum 2^j\cdot a_{k,j})$ be the
inverse of BitDecomp, but well-defined even when the input is not a $0/1$ vector. For
$N$-dimensional $\vec a'$, let
$\mathrm{Flatten}(\vec a')=\mathrm{BitDecomp}(\mathrm{BitDecomp}^{-1}(\vec a'))$, a
$N$-dimensional vector with $0/1$ coefficients. When $A$ is a matrix, let
$\mathrm{BitDecomp}(A)$, $\mathrm{BitDecomp}^{-1}$, or $\mathrm{Flatten}(A)$ be the matrix
formed by applying the operation to each row of $A$ separately. Finally, let
$\mathrm{Powersof2}(\vec b)=(b_1,2b_1,\dots,2^{\ell-1}b_1,\dots,b_k,2b_k,\dots,2^{\ell-1}b_k)$, a
$N$-dimensional vector. Here are some obvious facts:

- $\langle\mathrm{BitDecomp}(\vec a),\mathrm{Powersof2}(\vec b)\rangle=\langle\vec a,\vec b\rangle$.
- For any $N$-dimensional $\vec a'$,
  $\langle\vec a',\mathrm{Powersof2}(\vec b)\rangle
  =\langle\mathrm{BitDecomp}^{-1}(\vec a'),\vec b\rangle
  =\langle\mathrm{Flatten}(\vec a'),\mathrm{Powersof2}(\vec b)\rangle$.

An interesting feature of Flatten is that it makes the coefficients of a vector or matrix
small, without affecting its product with $\mathrm{Powersof2}(\vec b)$, and without knowing
$\vec b$.

To facilitate ciphertext flattening, we give a special form to our secret key $\vec v$.
Specifically, we set $\vec v=\mathrm{Powersof2}(\vec s)$ for some secret vector $\vec s$ (to be
specified later). This form is consistent with our earlier requirement that $\vec v$ have some
big coefficient $v_i$ for decryption; indeed, since $\vec v$'s coefficients go up by
$\lfloor\log_2 q\rfloor$ powers of 2, it must have a big coefficient suitable to recover
$\mu\in\{0,1\}$.

Now, for any $N\times N$ matrix $C$, we have $\mathrm{Flatten}(C)\cdot\vec v=C\cdot\vec v$. So,
after we compute an initial ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ for the NAND gate, we
set $C^{\mathrm{NAND}}=\mathrm{Flatten}(C_3)$ to obtain a ciphertext that has $0/1$
coefficients and is strongly bounded. Thus, we obtain leveled FHE without relinearization, under
a fixed approximate eigenvector secret key.

*Transcription note.* The page break (p. 5 to p. 6) falls inside the definition of
$\mathrm{Flatten}$; the subsection is kept as one block. The sums in
$\mathrm{BitDecomp}^{-1}$ run over $j$ (the extraction prints the $\sum$ signs on a separate
line).

<a id="pdf-8edb94cfd852-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 1.3.4, key generation, encryption, and reduction to LWE (p. 6).** Let us finally
circle back to key generation and encryption. We want to base security on LWE. So, for key
generation, we generate an LWE instance. For suitable parameters $q$, $n$,
$m=O(n\log q)$, an LWE instance over $\mathbb Z_q$ consists of a $m\times(n+1)$ matrix $A$ such
that there exists a $(n+1)$-dimensional vector $\vec s$ whose first coefficient is $1$ where
$\vec e=A\cdot\vec s$ is a "small" error vector. (See Section 2 for a formal definition of LWE.)
In our scheme, $A$ is public and $\vec s$ is secret. We set our approximate eigenvector to be
$\vec v=\mathrm{Powersof2}(\vec s)$, a vector of dimension $N=(n+1)\cdot\ell$ for
$\ell=\lfloor\log_2 q\rfloor+1$.

To encrypt $\mu\in\mathbb Z_q$, the encrypter generates a random $N\times m$ matrix $R$ with
$0/1$ entries, and sets $C=\mathrm{Flatten}(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A))$, where
$I_N$ is the $N$-dimensional identity matrix. Since Flatten does not affect the product with
$\vec v$, we have:

$$
C\cdot\vec v=\mu\cdot\vec v+\mathrm{BitDecomp}(R\cdot A)\cdot\vec v
=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+\text{small}
$$

Flatten ensures that the coefficients of $C$ are small, and therefore that $C$ has the proper
form of a ciphertext that permits our homomorphic operations. Decryption works as mentioned
previously.

To show that security is based on LWE, it is now enough to show that $C$ is statistically
independent of $\mu$ when $A$ is a uniformly random $m\times(n+1)$ matrix over $\mathbb Z_q$.
Let $C'=\mathrm{BitDecomp}^{-1}(C)$. Recall that $C$ is Flatten'd, and so
$C=\mathrm{Flatten}(C)=\mathrm{BitDecomp}(C')$. Therefore, $C$ reveals nothing more than $C'$.
But $C'=\mathrm{BitDecomp}^{-1}(\mu\cdot I_N)+R\cdot A$, and $R\cdot A$ is statistically uniform
by the leftover hash lemma when $m=O(n\log q)$ is chosen appropriately.

<a id="pdf-8edb94cfd852-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 2.3, other preliminaries (p. 8).** For $n$, $q$, and
$\ell=\lfloor\log q\rfloor+1$, we define the procedures BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten and Powersof2 as described in the Introduction. $I_N$ denotes the $N$-dimensional
identity matrix.

<a id="pdf-8edb94cfd852-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

## 3 Our LWE-Based FHE Scheme

**Section 3.1, basic encryption scheme: opening and Setup (p. 8).** Here, we formally describe
our basic encryption scheme (without homomorphic operations). This description matches the
description outlined in the Introduction. In our description, we split up KeyGen into three
parts Setup, SecretKeyGen and PublicKeyGen. We provide two decryption algorithms Dec and MPDec.
Dec is sufficient to recover the message $\mu$ when it is in a small space (e.g., $\{0,1\}$).
MPDec is an algorithm by Micciancio and Peikert [MP12] that can recover any
$\mu\in\mathbb Z_q$.

- $\mathrm{Setup}(1^\lambda,1^L)$: Choose a modulus $q$ of $\kappa=\kappa(\lambda,L)$ bits,
  lattice dimension parameter $n=n(\lambda,L)$, and error distribution
  $\chi=\chi(\lambda,L)$ appropriately for LWE that achieves at least $2^\lambda$ security
  against known attacks. Also, choose parameter $m=m(\lambda,L)=O(n\log q)$. Let
  $\textit{params}=(n,q,\chi,m)$. Let $\ell=\lfloor\log q\rfloor+1$ and $N=(n+1)\cdot\ell$.

<a id="pdf-8edb94cfd852-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, SecretKeyGen, PublicKeyGen, Enc, Dec, MPDec (p. 9).**

- $\mathrm{SecretKeyGen}(\textit{params})$: Sample $\vec t\leftarrow\mathbb Z_q^{n}$. Output
  $sk=\vec s\leftarrow(1,-t_1,\dots,-t_n)\in\mathbb Z_q^{n+1}$. Let
  $\vec v=\mathrm{Powersof2}(\vec s)$.
- $\mathrm{PublicKeyGen}(\textit{params},sk)$: Generate a matrix
  $B\leftarrow\mathbb Z_q^{m\times n}$ uniformly and a vector $\vec e\leftarrow\chi^m$. Set
  $\vec b=B\cdot\vec t+\vec e$. Set $A$ to be the $(n+1)$-column matrix consisting of $\vec b$
  followed by the $n$ columns of $B$. Set the public key $pk=A$. (Remark: Observe that
  $A\cdot\vec s=\vec e$.)
- $\mathrm{Enc}(\textit{params},pk,\mu)$: To encrypt a message $\mu\in\mathbb Z_q$, sample a
  uniform matrix $R\in\{0,1\}^{N\times m}$ and output the ciphertext $C$ given below.

  $$
  C=\mathrm{Flatten}\bigl(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A)\bigr)\in\mathbb Z_q^{N\times N}.
  $$
- $\mathrm{Dec}(\textit{params},sk,C)$: Observe that the first $\ell$ coefficients of
  $\vec v$ are $1,2,\dots,2^{\ell-1}$. Among these coefficients, let $v_i=2^i$ be in
  $(q/4,q/2]$. Let $C_i$ be the $i$-th row of $C$. Compute
  $x_i\leftarrow\langle C_i,\vec v\rangle$. Output $\mu'=\lfloor x_i/v_i\rceil$.
- $\mathrm{MPDec}(\textit{params},sk,C)$ (for $q$ a power of 2): Observe that $q=2^{\ell-1}$
  and the first $\ell-1$ coefficients of $\vec v$ are $1,2,\dots,2^{\ell-2}$, and therefore if
  $C\cdot\vec v=\mu\cdot\vec v+\text{small}$, then the first $\ell-1$ coefficients of
  $C\cdot\vec v$ are $\mu\cdot\vec g+\text{small}$, where $\vec g=(1,2,\dots,2^{\ell-2})$.
  Recover $\mathrm{LSB}(\mu)$ from $\mu\cdot 2^{\ell-2}+\text{small}$, then recover the
  next-least-significant-bit from $(\mu-\mathrm{LSB}(\mu))\cdot 2^{\ell-3}+\text{small}$, etc.
  (See [MP12] for the general $q$ case.)

Dec is a BitDecomp'd version of Regev's decryption procedure, applied to one row of the
ciphertext, which is a BitDecomp'd Regev ciphertext. (The extra rows will come into play in the
homomorphic operations). If $C$ is properly generated, then by the elementary properties of
BitDecomp and Powersof2, we have

$$
C\cdot\vec v=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+R\cdot\vec e.
$$

Dec only uses the $i$-th coefficient of the above expression, which is
$x_i=\mu\cdot v_i+\langle R_i,\vec e\rangle$. The error $\langle R_i,\vec e\rangle$ has
magnitude at most $\|\vec e\|_1$. In general, if $x_i=\mu\cdot v_i+e'$ for some error $e'$ of
magnitude at most $q/8$, and if $v_i\in(q/4,q/2]$, then $x_i/v_i$ differs from $\mu$ by at most
$(q/8)/v_i<1/2$, and Dec uses rounding to output the correct value of $\mu$. (In the basic
scheme, we set $\chi$ to ensure that the error is so bounded with overwhelming probability.)

For the basic scheme (without homomorphic operations), one can take $n$ to be quasi-linear in
the security parameter $\lambda$ and $\kappa=O(\log n)$. When allowing homomorphic operations,
$L$ represents the circuit complexity of the functions that the scheme correctly evaluates
(roughly, $L$ is the multiplicative depth); we provide a detailed analysis later of how $L$
affects the other parameters.

<a id="pdf-8edb94cfd852-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.2, security (pp. 9–10).** Observe that
$\mathrm{BitDecomp}^{-1}(C)=\mu\cdot G+R\cdot A$, where
$G=\mathrm{BitDecomp}^{-1}(I_N)$ is (the transpose of) the "primitive matrix" used by Micciancio
and Peikert [MP12] in their construction of lattice trapdoors, and the rows of $R\cdot A$ are
simply Regev [Reg05] encryptions of $0$ for dimension $n$. Assuming
$\mathrm{BitDecomp}^{-1}(C)$ hides $\mu$, $C$ does as well, since $C$ can be derived by applying
BitDecomp. Thus, the security of our basic encryption scheme follows directly from the following
lemma, used to prove the security of Regev's encryption scheme [Reg05].

<a id="pdf-8edb94cfd852-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 1 (Implicit in [Reg05]).** Let $\textit{params}=(n,q,\chi,m)$ be such that the
$\mathrm{LWE}_{n,q,\chi}$ assumption holds. Then, for $m=O(n\log q)$ and $A$, $R$ as generated
above, the joint distribution $(A,R\cdot A)$ is computationally indistinguishable from uniform
over $\mathbb Z_q^{m\times(n+1)}\times\mathbb Z_q^{N\times(n+1)}$.

Concretely, it suffices to take $m>2n\log q$ [Reg05].

Like Brakerski [Bra12], we can also base security on GapSVP via a classical reduction from LWE
[Pei09, BLP+13]. Specifically, Peikert [Pei09] gives a classical reduction of GapSVP to LWE,
with the caveat that $q$ must be exponential in $n$. Brakerski notes that exponential $q$ was
unusable in previous FHE schemes, since the ratio of $q$ to the error level $B$ of "fresh"
ciphertexts cannot be exponential in $n$ for security reasons (since LLL [LLL82] could be used to
break such a scheme), and since $B$ must be very small to permit many homomorphic operations. As
in Brakerski's scheme, we do not have that problem. The error bound $B$ of fresh ciphertexts in
our scheme does not need to be small to permit many homomorphic operations; we only require
$q/B$ to be sub-exponential, and we can therefore permit $q$ to be exponential. Alternatively, we
can use a sub-exponential $q$ and base security on GapSVP via Brakerski et al.'s [BLP+13] recent
classical reduction to LWE that works even for polynomial-size moduli, with the caveat that, in
their reduction, the dimension of the GapSVP instances may be much smaller than the dimension of
the LWE instances.

<a id="pdf-8edb94cfd852-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Section 3.3, homomorphic operations: MultConst, Add, Mult (pp. 10–11).** Recall that we
already described some basic "homomorphic" operations BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten, and Powersof2. These will play an important role in analyzing the homomorphic
operations supported by our scheme. We remark that BitDecomp could alternatively decompose with
respect to bases other than 2, or according to the Chinese Remainder Theorem.

We provide additional homomorphic operations MultConst, Add, Mult, NAND as follows.

- $\mathrm{MultConst}(C,\alpha)$: To multiply a ciphertext $C\in\mathbb Z_q^{N\times N}$ by known
  constant $\alpha\in\mathbb Z_q$, set $M_\alpha\leftarrow\mathrm{Flatten}(\alpha\cdot I_N)$ and
  output $\mathrm{Flatten}(M_\alpha\cdot C)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{MultConst}(C,\alpha)\cdot\vec v&=M_\alpha\cdot C\cdot\vec v
  =M_\alpha\cdot(\mu\cdot\vec v+\vec e)=\mu\cdot(M_\alpha\cdot\vec v)+M_\alpha\cdot\vec e\\
  &=\alpha\cdot\mu\cdot\vec v+M_\alpha\cdot\vec e
  \end{aligned}
  $$

  Thus, the error increases by a factor of at most $N$, regardless of what element
  $\alpha\in\mathbb Z_q$ is used for multiplication. As in "classical" additively homomorphic
  encryption schemes, we could alternatively perform multiplication-by-constant $\alpha$ by
  recursively applying Add. But this multiplies the error size by at least $\alpha$, whereas
  MultConst increases the error by at most a factor of $N$, regardless of $\alpha$. An example
  application of MultConst is that we can perform homomorphic fast Fourier transformations
  (FFTs) natively over $\mathbb Z_q$ without error growth dependent on $q$. Previously, the
  error growth depended on the size of the field underlying the FFT [GHS12a, GHS12b],
  restricting the choice of field.
- $\mathrm{Add}(C_1,C_2)$: To add ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1+C_2)$. The correctness of this operation is immediate. Note that the
  addition of messages is over the full base ring $\mathbb Z_q$.
- $\mathrm{Mult}(C_1,C_2)$: To multiply ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1\cdot C_2)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{Mult}(C_1,C_2)\cdot\vec v&=C_1\cdot C_2\cdot\vec v
  =C_1\cdot(\mu_2\cdot\vec v+\vec e_2)+\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2\\
  &=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2
  \end{aligned}
  $$

  As in Add, the multiplication operator is over the full base field $\mathbb Z_q$. In Mult, the
  new error depends on the old errors, the ciphertext $C_1$, and the message $\mu_2$. The
  dependence on the old errors seems unavoidable (and normal for LWE-based HE schemes), and
  observe that $C_1$ contributes at most a factor $N$ blowup of error, since all components of
  $C_1$ are restricted to $\{0,1\}$. The error growth based on the message $\mu_2$, however,
  presents a concern. In general, we must address this concern by using homomorphic operations
  in a way that restricts the message space to small messages. One way to do this is to
  consider Boolean circuits using only NAND operations: this would restrict the message space to
  $\{0,1\}$. We elaborate below.

*Transcription note.* The first line of the Mult display is transcribed as printed (checked
against the page image, 140 dpi): a "$+$" stands where an "$=$" is meant, i.e. the intended
expansion is
$C_1\cdot(\mu_2\cdot\vec v+\vec e_2)=\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2$. The
second line is the correct result.

<a id="pdf-8edb94cfd852-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.3, NAND (p. 11).**

- $\mathrm{NAND}(C_1,C_2)$: To NAND ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$ that are
  known to encrypt messages $\mu_1,\mu_2\in\{0,1\}$, output $\mathrm{Flatten}(I_N-C_1\cdot C_2)$.
  Observe that:

  $$
  \mathrm{NAND}(C_1,C_2)\cdot\vec v=(I_N-C_1\cdot C_2)\cdot\vec v
  =(1-\mu_1\cdot\mu_2)\cdot\vec v-\mu_2\cdot\vec e_1-C_1\cdot\vec e_2
  $$

  Note here that the NAND homomorphic operation maintains the invariant that if the input
  messages are in $\{0,1\}$, then the output ciphertext will also encryption of $\{0,1\}$, thus
  guaranteeing small messages. Note that since $\mu_2\in\{0,1\}$, the error is increased by a
  factor of at most $N+1$.

<a id="pdf-8edb94cfd852-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.3, "Circuits" (p. 11).** By iteratively applying the homomorphic operations above,
different types of (bounded-depth) circuits may be homomorphically computed while maintaining
correctness of decryption.

The simplest case to analyze is the case of Boolean circuits computed over encryptions of
$\{0,1\}$ values. In this case, the circuit can be converted to use only NAND gates, and through
appropriate leveled application of the NAND homomorphic operation, the final ciphertext's error
will be bounded by $(N+1)^{L}\cdot B$, where $L$ is the NAND-depth of the circuit, and $B$ is the
original bound on the error of a fresh encryption of $\{0,1\}$.

More generally, with more care, we may consider arithmetic circuits over $\mathbb Z_q$ that make
use of gates that perform addition, multiplication, or multiplication by a known constant.
However, as we have seen in the case of multiplication gates, the error growth may depend on the
values being encrypted in intermediate computations. One way to deal with this is to focus on
situations where (1) all input values are known to encrypt values bounded by some value $T$, and
(2) the arithmetic circuit is chosen to guarantee that all intermediate values are also bounded
by $T'$ whenever the circuit inputs are constrained to values bounded by $T$. In such a
situation, the final ciphertext's error will be bounded by $(N+T')^{L}\cdot B$, where $L$ is the
depth of the arithmetic circuit, and $B$ is the original bound on the error of fresh encryptions
of values smaller than $T$. For example, in this way, we can homomorphically evaluate
polynomials of degree $d$ in this large-message-space variant when the initial messages are
bounded by roughly $q^{1/d}$, achieving a scheme that is "somewhat homomorphic" [Gen09]. Another
example application would be to convert encryptions of a polynomially bounded set of small values
to encryptions of binary values, by using an appropriate arithmetic circuit for the conversion.
Once converted to encryptions of binary values, a NAND-based Boolean circuit could be used for
further computations.

<a id="pdf-8edb94cfd852-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->

**Section 3.4, parameters, performance and optimizations (pp. 11–12).** Suppose that
Flatten'd ciphertexts $C_1,C_2$ encrypt $\mu_1,\mu_2\in\{0,1\}$ under approximate eigenvector
$\vec v$ with $B$-bounded error – that is, $C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ where
$|\vec e_i|_\infty\le B$. Then $C^{\mathrm{NAND}}\leftarrow\mathrm{NAND}(C_1,C_2)$ encrypts
$\mathrm{NAND}(\mu_1,\mu_2)\in\{0,1\}$ under $\vec v$ with $(N+1)B$-bounded error. As long as
$q/B>8(N+1)^{L}$, we can evaluate a depth-$L$ circuit of NANDs over $B$-bounded ciphertexts to
obtain a $q/8$-bounded ciphertext, which Dec will decrypt correctly.

As in previous LWE-based FHE schemes, $n$ (hence $N$) must increase linearly with $\log(q/B)$ to
maintain fixed $2^\lambda$ security against known attacks, so $q/B$ grows more like
$\exp(L\log L)$. We will brush such issues under the rug and view $n$ as a fixed parameter.
Choosing $\chi$ so that $B$ is not too large, and since in practice there is no reason to have
$\kappa=\log q$ grow super-linearly with $n$, we have
$\kappa=O(L\log N)=O(L(\log n+\log\kappa))=O(L\log n)$, similar to [BGV12, Bra12]. Given that the
NAND procedure is dominated by multiplication of two $N\times N$ matrices for
$N=O(n\kappa)=\tilde O(nL)$, we have the following theorem to characterize the performance of
our FHE scheme.

<a id="pdf-8edb94cfd852-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Theorem 3.** For dimension parameter $n$ and depth parameter $L$, our FHE scheme evaluates
depth-$L$ circuits of NAND gates with $\tilde O((nL)^{\omega})$ field operations per gate, where
$\omega<2.3727$ is the matrix multiplication exponent.

This compares favorably with previous LWE-based FHE schemes, which all have at least
$\tilde O(n^3L)$ field operations per gate [BV11b, BGV12, Bra12].

Theorem 3 hides some factors, both good and bad. On the good size, it hides the fact that
ciphertext matrices in our scheme have $0/1$ entries, and therefore can be multiplied faster than
if they were general matrices over $\mathbb Z_q$. In previous LWE-based FHE schemes, the field
operations involve multiplying a small number with a general number of $\mathbb Z_q$, which has
complexity $\tilde O(\kappa)=\tilde O(L)$. So, previous LWE-based FHE schemes have real
complexity $\tilde O(n^3L^2)$ whereas ours remains $\tilde O((nL)^{\omega})$. On the bad side,
Theorem 3 hides logarithmic factors in the dimension of the ciphertext matrices, since
$N=O(n\kappa)=O(nL\log n)$. We note that typically $n$ will dominate $L$, since for very deep
circuits, one would want to use Gentry's bootstrapping technique [Gen09] to make the per-gate
computation independent of $L$.

<a id="pdf-8edb94cfd852-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 3.4, bootstrapping (p. 12).** Since bootstrapping involves homomorphically evaluating
the decryption function, and since Dec is essentially Regev decryption [Reg05], bootstrapping
works as in previous LWE-based FHE schemes. In particular, we can use techniques from [BV11b] to
reduce the dimension and modulus-size of the ciphertext before bootstrapping, so that the
complexity of decryption (and hence bootstrapping) is completely independent of the depth $L$ of
the circuit that was evaluated to arrive at that ciphertext. Regev decryption can be evaluated in
$O(\log n)$ depth. Due to the logarithmic depth, one can take $q/B$ to be quasi-polynomial in
$n$, and base security on LWE for quasi-polynomial factors.
