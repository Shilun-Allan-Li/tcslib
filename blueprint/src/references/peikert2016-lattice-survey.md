<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PRs #236 and #237 -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20, 21 and 24 of the original PDF. The added SIS passages cover
the exclusion of trivial modulus multiples and the binary collision argument. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

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
