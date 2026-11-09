<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PR #236 -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20 and 24 of the original PDF. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

<a id="pdf-1a9802b66031-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->

**Definition 4.1.1 (Short Integer Solution ($\mathrm{SIS}_{n,q,\beta,m}$)).** Given $m$ uniformly random vectors $\mathbf a_i\in\mathbb Z_q^n$, forming
the columns of a matrix $\mathbf A\in\mathbb Z_q^{n\times m}$, find a nonzero integer vector $\mathbf z\in\mathbb Z^m$ of norm $\|\mathbf z\|\le\beta$ such
that

$$
f_{\mathbf A}(\mathbf z):=\mathbf A\mathbf z=\sum_i\mathbf a_i\cdot z_i=\mathbf0\in\mathbb Z_q^n.\tag{4.1.1}
$$

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
