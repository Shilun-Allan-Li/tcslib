<!-- source-pdf-sha256: 74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c -->
<!-- validation-status: approved scoped reference for draft PR #250 -->

# Lossy Trapdoor Functions and Their Applications

Chris Peikert and Brent Waters, author version dated June 4, 2010.
This reference summarizes the consumed passages on physical and printed pages
33–39 of the 44-page PDF. [Author PDF](https://web.eecs.umich.edu/~cpeikert/pubs/lossy_tdf.pdf)

<a id="pdf-74f48b0eff6f-p033-b001"></a>
<!-- pdf-source: page=33; block=1; confidence=1.00 -->

**Section 6.2, GenConceal and Lemma 6.2.** Given a public matrix $A$ with
$h$ rows and $d$ columns and a secret matrix $S$ with $w$ rows and $d$
columns, form $B=AS^\mathsf{T}+E$ using independent error entries and
publish $(A,B)$. The trapdoor is $S$. Lemma 6.2 gives pseudorandomness of
the public pair under LWE. The displayed sampling bullet on p. 33 gives
$h\times d$ for $S$. The dimensions of $B$ and the proof on p. 34
give $w\times d$.

<a id="pdf-74f48b0eff6f-p034-b001"></a>
<!-- pdf-source: page=34; block=1; confidence=1.00 -->

**Proof of Lemma 6.2.** Hybrid $H_j$ uses the same public matrix $A$,
concealed values in the first $j$ columns, and uniform independent columns
afterward. For an adjacent hybrid, the $h$ challenge samples supply $A$
and one column. In the real experiment that column uses one secret across all
rows.

<a id="pdf-74f48b0eff6f-p034-b002"></a>
<!-- pdf-source: page=34; block=2; confidence=1.00 -->

**Lemma 6.3.** With its Gaussian noise law and numerical conditions, the
lemma bounds the probability that any binary input has an error sum with a
normalized coordinate of magnitude at least $1/(4p)$.

<a id="pdf-74f48b0eff6f-p035-b001"></a>
<!-- pdf-source: page=35; block=1; confidence=1.00 -->

**Section 6.3.2, positional gadget.** For $p$ a power of two and
$n=w\log_2 p$, the $n\times w$ gadget $G$ replaces each identity-matrix
entry with that entry times the column of successive powers of two.
The product $xG$ reads one binary digit block per column. The printed row
formula gives $[w]$ for both indices. The length of the powers column and
the row formula give $[\log_2 p]$ for the within-block index.

<a id="pdf-74f48b0eff6f-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->

**Section 6.3.2, encoding and decoding.** Encode by rounding $qm/p$ to
an integer modulo $q$. Decode by rounding $pv/q$ to an integer modulo
$p$. Both operations extend coordinatewise.

<a id="pdf-74f48b0eff6f-p036-b002"></a>
<!-- pdf-source: page=36; block=2; confidence=1.00 -->

**Section 6.3.2, key generation and evaluation.** The injective generator
adds the encoded gadget to the concealed block $B$. The lossy generator
uses $B$ directly. Evaluation is the row product with the public key.
In the lossy mode the second output is $(xA)S^\mathsf{T}+xE$.

<a id="pdf-74f48b0eff6f-p036-b003"></a>
<!-- pdf-source: page=36; block=3; confidence=1.00 -->

**Section 6.3.2, inversion.** Subtract $z_1 S^\mathsf{T}$ from $z_2$,
decode the resulting coordinates, and recover the binary input by unpacking
the canonical representatives of the gadget product.

<a id="pdf-74f48b0eff6f-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=1.00 -->

**Theorem 6.4, mode indistinguishability and inversion.** Both key modes
are compared with uniform using Lemma 6.2. The inversion proof uses the
residual $xE+x\,c(G)$. Equations (3)–(4) bound noise and the encoding's
rounding error to recover $xG\bmod p$ simultaneously for all binary inputs
with overwhelming probability.

<a id="pdf-74f48b0eff6f-p037-b002"></a>
<!-- pdf-source: page=37; block=2; confidence=1.00 -->

**Theorem 6.4, lossy image and residual leakage.** Count the first output in
$\mathbb Z_q^d$ and the possible bounded error vectors $xE$. The
logarithm of the image bound controls residual leakage.

<a id="pdf-74f48b0eff6f-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->

**Section 6.4, anti-cyclic shifts and rank.** Shift by moving the last
coefficient to the front and negating it. The rows of $S(v)$ are the
successive shifts. At power-of-two width, multiplication by a nonzero
coefficient polynomial in $\mathbb Q[X]/(X^w+1)$ sends the power basis
to linearly independent rows. The expanded branch product can have
integer coordinates as large in magnitude as $w(p-1)$.

<a id="pdf-74f48b0eff6f-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->

**Section 6.4, branch gadget and key generation.** Expand the branch matrix
by the powers-of-two column and encode it with the enlarged message modulus
$p'=2pw$. Subtract that encoded matrix for the designated lossy branch
from the concealed block. The trapdoor retains the secret matrix and
the designated branch.

<a id="pdf-74f48b0eff6f-p039-b001"></a>
<!-- pdf-source: page=39; block=1; confidence=1.00 -->

**Section 6.4, evaluation and inversion.** Evaluation restores the queried
branch's encoded matrix. At the designated branch this cancels the
subtracted shift. For a different branch, the signed message lift modulo
$p'=2pw$ uses the interval from $-w(p-1)$ to $w(p-1)$. The inversion
algorithm then solves the full-rank branch system and unpacks the binary
blocks.

<a id="pdf-74f48b0eff6f-p039-b002"></a>
<!-- pdf-source: page=39; block=2; confidence=1.00 -->

**Theorem 6.5, hidden branch.** The proof compares each fixed designated
branch's public key with uniform via Lemma 6.2.

<a id="pdf-74f48b0eff6f-p039-b003"></a>
<!-- pdf-source: page=39; block=3; confidence=1.00 -->

**Theorem 6.5, other-branch inversion.** After cancelling the trapdoor
product the residual contains $xE$ and the difference between the two
encoded branch products. The rounding proof allows extra error from
subtracting rounded encodings. The signed lift uses coefficients in
$\{-1,0,1\}$ for the branch difference. The final coordinate bound
concerns the decoded, unencoded integer product.

<a id="pdf-74f48b0eff6f-p039-b004"></a>
<!-- pdf-source: page=39; block=4; confidence=1.00 -->

**Theorem 6.5, lossy branch.** The final paragraph applies the lossy image
and leakage argument of Theorem 6.4 with the enlarged message modulus.
