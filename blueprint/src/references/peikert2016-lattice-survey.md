<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PRs #236 and #237; DW-7 extension (Sections 5.4.3, 6.1.2-6.1.3) awaiting Codex source review -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20, 21 and 24 of the original PDF. The added SIS passages cover
the exclusion of trivial modulus multiples and the binary collision argument. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

**DW-7 extension (2026-11-16).** The blocks on PDF pages 52–53 and 68–70 were added by the
maintainer for the GSW campaign (GSW ruling Q14; deferred item DW-7). They transcribe, from the
committed raw extraction, the passages the GSW Lean and the phase-6 plan cite: the "Gadgets"
part of §5.4.3 (the vector $\mathbf g$, $\mathbf G=\mathbf I_n\otimes\mathbf g^t$,
Equation (5.4.1) and $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$), §6.1.2
(bootstrapping and circular security) and §6.1.3 (Equations (6.1.4)–(6.1.7), decryption, NAND,
bootstrapping by right-associative chains and Barrington's theorem). Unlike the summaries above,
these blocks are transcriptions in the paper's wording, with mathematics in LaTeX; printed page
numbers are two less than the PDF page. The rest of §5.4.3 (trapdoors, Definition 5.4.4 onward)
and of §6.1.3 (fully homomorphic signatures) is not used and is not transcribed. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-1a9802b66031-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->

**Definition 4.1.1 (Short Integer Solution ($\mathrm{SIS}_{n,q,\beta,m}$)).** Given $m$ uniformly random vectors $\mathbf a_i\in\mathbb Z_q^n$, forming
the columns of a matrix $\mathbf A\in\mathbb Z_q^{n\times m}$, find a nonzero integer vector $\mathbf z\in\mathbb Z^m$ of norm $\|\mathbf z\|\le\beta$ such
that

$$
f_{\mathbf A}(\mathbf z):=\mathbf A\mathbf z=\sum_i\mathbf a_i\cdot z_i=\mathbf0\in\mathbb Z_q^n.\tag{4.1.1}
$$

<a id="pdf-1a9802b66031-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.98 -->

**Observation after Equation (4.1.1).**

Similarly, we
  must take $\beta<q$ because otherwise $\mathbf z=(q,0,\ldots,0)\in\mathbb Z^m$ would always be a legitimate (but trivial)
  solution.

<a id="pdf-1a9802b66031-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.98 -->

* Any solution for a matrix $\mathbf A$ can trivially be converted to one for any extension $[\mathbf A\mid\mathbf A']$, simply by
  appending the solution vector with zeros (which leaves the norm of the solution unchanged). In other
  words, we can ignore columns $\mathbf a_i$ as desired, so the SIS problem can only become easier as $m$ increases.
  Similarly, it can only become harder as $n$ increases.

* The norm bound $\beta$ and the number $m$ of vectors $\mathbf a_i$ must be large enough that a solution is guaranteed
  to exist. This is the case whenever $\beta\ge\sqrt{\bar m}$ and $m\ge\bar m$, where $\bar m$ is the smallest integer greater than
  $n\log q$, by a pigeonhole argument: first, by the previous observation we can assume without loss of
  generality that $m=\bar m$. Then because there are more than $q^n$ vectors $\mathbf x\in\{0,1\}^m$, there must be two
  distinct $\mathbf x,\mathbf x'$ such that $\mathbf A\mathbf x=\mathbf A\mathbf x'\in\mathbb Z_q^n$, so their difference $\mathbf z=\mathbf x-\mathbf x'\in\{0,\pm1\}^m$ is a solution of
  norm at most $\beta$.

* The above pigeonhole argument in fact shows more: the induced function family $\{f_{\mathbf A}:\{0,1\}^m\to\mathbb Z_q^n\}$
  defined in Equation (4.1.1) is *collision resistant*, assuming the hardness of the corresponding SIS
  problem. This is because a collision $\mathbf x,\mathbf x'\in\{0,1\}^m$ for $f_{\mathbf A}$ immediately yields an SIS solution for $\mathbf A$.
  (Of course the domain $\{0,1\}^m$ is somewhat arbitrary here, and can be replaced by essentially any other
  large enough set of sufficiently short integer vectors.)

<a id="pdf-1a9802b66031-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.98 -->

LWE is parameterized by positive integers $n$ and $q$, and an error distribution $\chi$ over $\mathbb Z$.

**Definition 4.2.1 (LWE distribution).** For a vector $\mathbf s\in\mathbb Z_q^n$ called the *secret*, the LWE distribution $A_{\mathbf s,\chi}$
over $\mathbb Z_q^n\times\mathbb Z_q$ is sampled by choosing $\mathbf a\in\mathbb Z_q^n$ uniformly at random, choosing $e\leftarrow\chi$, and outputting
$(\mathbf a,b=\langle\mathbf s,\mathbf a\rangle+e\bmod q)$.

*Definition 4.2.2 omitted.*

**Definition 4.2.3 (Decision-$\mathrm{LWE}_{n,q,\chi,m}$).** Given $m$ independent samples $(\mathbf a_i,b_i)\in\mathbb Z_q^n\times\mathbb Z_q$ where every
sample is distributed according to either: (1) $A_{\mathbf s,\chi}$ for a uniformly random $\mathbf s\in\mathbb Z_q^n$ (fixed for all samples), or
(2) the uniform distribution, distinguish which is the case (with non-negligible advantage).

<a id="pdf-1a9802b66031-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->

**Section 5.1, SIS hashing.** The opening paragraph recalls that the
binary matrix map of Equation (4.1.1) is collision resistant under the
hardness of the corresponding SIS problem. A collision yields the short
nonzero difference described in the earlier section.

<a id="pdf-1a9802b66031-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=1.00 -->

**Section 5.2.1, Regev public-key encryption.** The public key collects
LWE samples under a uniform common secret as columns of an augmented
matrix. Equation (5.2.1) gives the augmented matrix and Equation (5.2.2)
cancels the secret product to expose the errors. Equation (5.2.3) forms
a binary subset sum and adds the message's half-modulus codepoint to its
last coordinate. Decryption cancels the secret contribution and compares
the residual with the two codepoints modulo the modulus.

<a id="pdf-1a9802b66031-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->

**Section 5.2.1, correctness.** The accumulated integer error is the
inner product of the key error vector and the binary subset. The source
uses a quarter-modulus separation and discusses choosing the noise law
and modulus to make decryption correct with overwhelming probability.

<a id="pdf-1a9802b66031-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->

**Section 5.2.1, first security hybrid.** Compare the fixed-bit view
of the public key and ciphertext with the experiment that uses a uniform
public key. A decision-LWE test forms its challenge matrix, encrypts the
fixed bit, and runs the view distinguisher. The simulation is exact for
both challenge laws.

<a id="pdf-1a9802b66031-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=1.00 -->

**Section 5.2.1, second security hybrid.** For a uniform augmented
key matrix and an independent uniform binary subset, the leftover hash
lemma makes the seed-published matrix product close to a uniform independent
ciphertext. Adding a fixed message vector preserves that ideal uniform law.
This hybrid and the first hybrid compare the two fixed-bit views.

<a id="pdf-1a9802b66031-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.95 -->

**Section 5.4.3, gadget trapdoors: gadgets (printed p. 50).** We now turn from short bases as
generic lattice trapdoors, to the "gadget"-based trapdoors for $q$-ary SIS/LWE lattices as
developed in [MP12], building on techniques from several related works [Ajt99, AP09, PW08,
ABB10].

*Gadgets.* The first main idea is that there are special, structured matrices $\mathbf G$, called
"gadgets," for which solving SIS and LWE is easy. The simplest gadget is as follows: for a given a
modulus $q$, define the vector

$$
\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell},
$$

where $\ell=\lceil\log_2 q\rceil$.⁸ Now observe that given any $u\in\mathbb Z_q$, we can find a
short solution $\mathbf x\in\mathbb Z^m$ to

$$
\langle\mathbf g,\mathbf x\rangle=\mathbf g^t\cdot\mathbf x=u\pmod q;
$$

for example, let $\mathbf x$ correspond to the base-two representation of $u$'s canonical
representative in $\{0,\dots,q-1\}$. In other words, it is easy to solve the SIS problem with
respect to the one-row parity-check "matrix" $\mathbf g^t$. Moreover, it is easy to randomly
sample from a discrete Gaussian over the lattice coset $\mathcal L^\perp_u(\mathbf g^t)$ of
solutions.

A bit more thought reveals that solving LWE with respect to $\mathbf g^t$ is also easy. For
simplicity, suppose that $q=2^\ell$; then given any $\mathbf b^t\approx s\cdot\mathbf g^t\pmod q$
with errors in the interval $[-\frac q4,\frac q4)$, we can recover the most-significant bit of
$s\in\mathbb Z_q$ from

$$
b_\ell\approx s\cdot2^{\ell-1}=\mathrm{msb}(s)\cdot\tfrac q2\pmod q.
$$

We can then recover the next-most-significant bit of $s$ from $b_{\ell-1}\approx s\cdot2^{\ell-2}\pmod q$,
etc. (This all generalizes to non-power-of-two moduli as well, but is a bit more technically
involved.)

We extend all of the above to $n$-dimensional SIS and LWE with respect to the block-diagonal
gadget matrix

$$
\mathbf G:=\mathbf I_n\otimes\mathbf g^t=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell},
$$

just by working blockwise: for LWE, given $\mathbf b^t\approx\mathbf s^t\mathbf G=(s_1\mathbf g,\dots,s_n\mathbf g)^t$,
just recover each $s_i$ from the corresponding block of $\mathbf b$. For SIS, to find a short
solution to $\mathbf G\mathbf x=\mathbf u$ for a given $\mathbf u\in\mathbb Z_q^n$, just find short
solutions to $\mathbf g^t\cdot\mathbf x_i=u_i$ for each entry $u_i$ and concatenate the results. It
is convenient to express this operation in terms of the "decomposition" function

$$
\begin{aligned}
\mathbf G^{-1}:\ &\mathbb Z_q^n\to\mathbb Z^{n\ell}\\
&\mathbf u\mapsto\text{a short solution }\mathbf x\text{ to }\mathbf G\mathbf x=\mathbf u\pmod q,
\end{aligned}\tag{5.4.1}
$$

Footnote 8: This $\mathbf g$ can be generalized in a variety of ways, e.g., by using a base other
than two, mixed bases, the Chinese Remainder Theorem, etc.

<a id="pdf-1a9802b66031-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.95 -->

**Section 5.4.3, the relation $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$ (printed p. 51).**
where the choice of notation is explained by the relation

$$
\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u\pmod q.
$$

We stress that $\mathbf G^{-1}$ is not a matrix, but rather a function that maps a mod-$q$ input to
a short integer vector. Depending on the context, the $\mathbf G^{-1}$ operation may even be
randomized, e.g., it could sample a Gaussian-distribution solution.

Finally, observe that given any invertible matrix $\mathbf H\in\mathbb Z_q^{n\times n}$, SIS and LWE
remain easy with respect to the matrix $\mathbf H\mathbf G\in\mathbb Z_q^{n\times n\ell}$.
Specifically, to solve $(\mathbf H\mathbf G)\mathbf x=\mathbf u$, simply output
$\mathbf x=\mathbf G^{-1}(\mathbf H^{-1}\cdot\mathbf u)$, and given
$\mathbf b^t\approx\mathbf s^t\mathbf H\mathbf G$, first recover $\mathbf s^t\mathbf H$ by solving
with respect to $\mathbf G$, then multiply the solution by $\mathbf H^{-1}$.

*Transcription note.* The sentence continues the display (5.4.1) from the previous page.

<a id="pdf-1a9802b66031-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.95 -->

**Section 6.1.2, bootstrapping (printed p. 66).** Even with all of the above techniques,
homomorphic operations still always increase the error rate of a ciphertext, by as much as a
polynomial factor per operation. Therefore, the schemes described so far can only homomorphically
evaluate circuits of an a-priori bounded depth; such systems are frequently called "somewhat
homomorphic" or "leveled" (we ignore the precise technical distinction between these terms).

A beautiful idea from Gentry's original work [Gen09b, Gen09a], called *bootstrapping* or sometimes
*refreshing*, makes it possible to reduce the error rate of a ciphertext, thus enabling unbounded
homomorphic computation. Suppose we have a ciphertext $c$ that encrypts some (unknown) message
$\mu$ under a secret key $s$, where the error rate of $c$ is too large to perform further
homomorphic operations on it. The idea behind bootstrapping is to homomorphically evaluate the
*decryption function* on a low-error encryption $c_s=\mathrm{Enc}(s)$ of the secret key $s$, which
is included as part of the public key. More specifically, we homomorphically evaluate the function
$f_c(\cdot)=\mathrm{Dec}(\cdot,c)$ on the ciphertext $c_s$. (Note that the ciphertext $c$ to be
refreshed is "hard-coded" into the function $f_c(\cdot)$, whereas the secret key is treated as the
function argument.) Because $f_c(s)=\mathrm{Dec}(s,c)=\mu$, it follows that homomorphic evaluation
of $f_c$ on an encryption of $s$ (namely, $c_s$) produces an encryption of $\mu$. Moreover, as long
as the circuit depth of $f_c$ and the error rate of $c_s$ are small enough, the error rate of the
output ciphertext will be substantially smaller than that of the input ciphertext $c$, as desired.
In particular, decryption can be performed in $O(\log\lambda)$ depth, so it suffices for $c_s$ to
have some $\lambda^{-O(\log\lambda)}$ error rate.

Because bootstrapping involves the homomorphic evaluation of a somewhat complex function, it is not
very efficient (see, e.g., [GH11b]). However, bootstrapping has been intensively studied and
improved in various ways [GH11a, BGV12], culminating in ring-LWE-based methods that run in only
polylogarithmic $\tilde O(1)$ time per encrypted bit [GHS12a, AP13], where the hidden
$\log^{O(1)}(\lambda)$ factors are not exceedingly large.

We conclude this discussion by noting that, in order to yield unbounded homomorphic operations,
bootstrapping requires a "circular" encryption of the secret key under itself. It is unknown
whether it is provably secure (under a standard assumption) to reveal such an encryption, but nor
are any attacks known. So to date, all unbounded FHE schemes require an additional assumption of
circular security for the secret key.

<a id="pdf-1a9802b66031-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.95 -->

**Section 6.1.3, third-generation FHE; homomorphic trapdoors, Equations (6.1.4)–(6.1.6) (printed
p. 67).** In 2013, Gentry, Sahai, and Waters (hereafter GSW) [GSW13] proposed an interesting
LWE-based FHE scheme that has some unique and advantageous properties. For example, homomorphic
multiplication does not require any key-switching step, and the scheme can be made identity-based.
Moreover, as shown in [BV14, AP14], the GSW scheme can be used to bootstrap with only a small
polynomial-factor growth in the error rate, as opposed to quasi-polynomial $\lambda^{\Theta(\log\lambda)}$
growth for the system described above. This yields unbounded FHE based on LWE with just an
inverse-polynomial $n^{-O(1)}$ error rate (plus a circular-security assumption). We describe these
results in some detail next.

*Homomorphic trapdoors.* The GSW scheme is presented most simply in terms of the gadget-based
trapdoors described in Section 5.4.3. (The presentation here has evolved through [BGG+14, AP14,
GVW15b].) At the heart of GSW are the following additive and multiplicative homomorphisms for tags
and trapdoors. Let $\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ be arbitrary, and for $i=1,2$ let

$$
\mathbf A_i=x_i\mathbf G-\bar{\mathbf A}\mathbf R_i\tag{6.1.4}
$$

for some integer $x_i$ and short integer matrix $\mathbf R_i$. In other words,
$\begin{bmatrix}\mathbf R_i\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_i$ (or more
accurately, tag $x_i\mathbf I$) for the matrix $[\bar{\mathbf A}\mid\mathbf A_i]$.

Applying Equation (6.1.4), it is easy to verify that

$$
\mathbf A_1+\mathbf A_2=(x_1+x_2)\mathbf G-\bar{\mathbf A}(\mathbf R_1+\mathbf R_2),\tag{6.1.5}
$$

and

$$
\begin{aligned}
\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)&=(x_1\mathbf G-\bar{\mathbf A}\mathbf R_1)\cdot\mathbf G^{-1}(\mathbf A_2)\\
&=x_1\mathbf A_2-\bar{\mathbf A}\cdot\mathbf R_1\mathbf G^{-1}(\mathbf A_2)\\
&=x_1x_2\mathbf G-\bar{\mathbf A}\underbrace{\bigl(\mathbf R_1\mathbf G^{-1}(\mathbf A_2)+x_1\mathbf R_2\bigr)}_{\mathbf R}.
\end{aligned}\tag{6.1.6}
$$

In other words, $\begin{bmatrix}\mathbf R_1+\mathbf R_2\\ \mathbf I\end{bmatrix}$ is a trapdoor with
tag $x_1+x_2$ for the matrix $[\bar{\mathbf A}\mid\mathbf A_1+\mathbf A_2]$, and
$\begin{bmatrix}\mathbf R\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_1x_2$ for the matrix
$[\bar{\mathbf A}\mid\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)]$. Note that in the latter case,
we need $x_1$ to be a small integer in order to get a good-quality trapdoor.

One very important property of homomorphic multiplication is that the growth of the resulting
trapdoor matrix $\mathbf R$ is *asymmetric* and *quasi-additive*: while $\mathbf R_1$ is expanded by
some polynomial factor due to the multiplication by $\mathbf G^{-1}(\mathbf A_2)$, the $\mathbf R_2$
term is only multiplied by $x_1$. We discuss the implications of this below.

<a id="pdf-1a9802b66031-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.95 -->

**Section 6.1.3, fully homomorphic encryption: the GSW scheme, Equation (6.1.7) (printed
pp. 67–68).** The GSW FHE scheme works as follows. As in prior systems, the public key is a matrix
$\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ whose columns are LWE samples with some secret
$\bar{\mathbf s}\in\mathbb Z^{n-1}$, i.e.,

$$
\mathbf s^t\bar{\mathbf A}\approx\mathbf 0\tag{6.1.7}
$$

where $\mathbf s=(-\bar{\mathbf s},1)$ is the secret key. An encryption of an integer $x$ is a matrix

$$
\mathbf A=x\mathbf G-\bar{\mathbf A}\mathbf R
$$

for some sufficiently short random $\mathbf R$. As usual, semantic security follows by a lossiness
argument: encrypting under a uniformly random ("malformed") public key $\bar{\mathbf A}$
statistically hides the message, because $[\bar{\mathbf A}\mid\bar{\mathbf A}\mathbf R]$ is very
close to uniformly distributed.

To decrypt a ciphertext $\mathbf A$ using the secret key $\mathbf s$, one just computes

$$
\mathbf s^t\mathbf A\approx x\cdot\mathbf s^t\mathbf G,
$$

where the approximation holds by Equation (6.1.7), and because $\mathbf R$ is short. Since it is
easy to solve LWE with respect to $\mathbf G$, we can recover $x\cdot\mathbf s^t$ and hence $x$
(modulo $q$). In fact, if $x$ is known to be just a bit, then because one of the rightmost entries
of $\mathbf s^t\mathbf G$ is far from zero modulo $q$, we can recover $x$ simply by testing whether
$\mathbf s^t\cdot\mathbf a\approx0$ for an appropriate column $\mathbf a$ of $\mathbf A$.

To homomorphically add or multiply ciphertexts $\mathbf A_1,\mathbf A_2$ that encrypt small
messages, one just computes $\mathbf A_1+\mathbf A_2$ or $\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)$,
respectively. As shown above in Equations (6.1.5) and (6.1.6), the resulting ciphertext is a valid
encryption for the sum or product of the messages, respectively. Because it is important for noise
growth that messages remain small integers, we typically only use operations that maintain the
messages as $\{0,1\}$-values. For example, the binary NAND operation, which is sufficient for
expressing arbitrary computations, can be written as $(x_1\text{ NAND }x_2)=1-x_1x_2$.

*Transcription note.* The block runs onto PDF page 70 (printed 68) from "for some sufficiently
short random $\mathbf R$". "$\bar{\mathbf s}\in\mathbb Z^{n-1}$" is as printed.

<a id="pdf-1a9802b66031-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.95 -->

**Section 6.1.3, bootstrapping (printed p. 68).** As first shown by Brakerski and Vaikuntanathan
[BV14], the asymmetric and quasi-additive growth of the trapdoor matrices under homomorphic
multiplication allows certain computations—in particular, decryption for the purpose of
bootstrapping—to be performed with rather small error growth. The first main observation is that
by Equation (6.1.6), any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth. The same
also holds when multiplying a sequence of permutation matrices (or more generally, orthonormal
integer matrices), where each matrix is encrypted entry-wise.

The second main idea is that by using Barrington's Theorem [Bar86], any depth-$d$ circuit can be
converted into a length-$4^d$ branching program of permutation matrices. In particular, the
$O(\log\lambda)$-depth decryption circuit can be computed homomorphically in polynomial time and
with polynomial error growth, albeit for rather large polynomials. The subsequent work of
Alperin-Sheriff and Peikert [AP14] significantly improved the runtime and growth to small
polynomials, by avoiding Barrington's Theorem and instead expressing decryption as an arithmetic
function that can be embedded directly into permutation matrices. Ducas and Micciancio [DM15]
devised and implemented a version of this method incorporating additional ideas, yielding a system
that evaluates a complete "bootstrapped NAND gate" in less than a second on standard desktop
hardware.
