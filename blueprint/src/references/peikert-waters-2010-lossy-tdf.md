<!-- source-pdf-sha256: 74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c -->
<!-- validation-status: approved scoped reference for draft PR #250 (pages 33-39); EF-D4 extension (Sections 3.1-3.2, pages 14-15) awaiting Codex source review -->

# Lossy Trapdoor Functions and Their Applications

Chris Peikert and Brent Waters, author version dated June 4, 2010.
This reference summarizes the consumed passages on physical and printed pages
33–39 of the 44-page PDF. [Author PDF](https://web.eecs.umich.edu/~cpeikert/pubs/lossy_tdf.pdf)

**EF-D4 extension (2026-11-18).** The blocks on PDF pages 14–15 were added by the maintainer for
efficiency wave 1 (ruling Q-D4-1 A: ingest before EF-D4 is dispatched). They transcribe §3.1
(lossy TDFs: the parameters $n$, $k$, $r$, the definition of a collection of $(n,k)$-lossy
trapdoor functions, and the almost-always relaxation) and §3.2 (all-but-one TDFs: the branch
collection, the definition of a collection of $(n,k)$-all-but-one trapdoor functions, and its
almost-always relaxation) in full, from the scoped raw extraction checked against the page images.
§3 has no text between its heading and §3.1; §3.3 onward is not transcribed. Unlike the
summaries of pages 33–39, these blocks are transcriptions in the paper's wording, with
mathematics in LaTeX and the paper's italics as emphasis; the passages have no displayed
formulas. Printed page numbers equal the PDF page. The bold block labels are the maintainer's,
and notes marked *Transcription note* are not part of the source.

<a id="pdf-74f48b0eff6f-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 3.1, lossy TDFs: parameters (printed p. 14).** Here we define lossy trapdoor functions.
Define the following quantities as functions of the security parameter:
$n(\lambda)=\mathrm{poly}(\lambda)$ represents the input length of the function and
$k(\lambda)\le n(\lambda)$ represents the *lossiness* of the collection. For convenience, we also
define the *residual leakage* $r(\lambda)=n(\lambda)-k(\lambda)$. For all these quantities, we
often omit the dependence on $\lambda$.

*Transcription note.* The block begins under the headings "3 Lossy and All-But-One Trapdoor
Functions" and "3.1 Lossy TDFs".

<a id="pdf-74f48b0eff6f-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.1, definition of $(n,k)$-lossy trapdoor functions (printed p. 14).** A collection of
$(n,k)$-*lossy trapdoor functions* is given by a tuple of PPT algorithms
$(S_{\mathrm{inj}},S_{\mathrm{loss}},F_{\mathrm{ltdf}},F_{\mathrm{ltdf}}^{-1})$ having the
properties below.

1. *Easy to sample an injective function with trapdoor:* $S_{\mathrm{inj}}$ outputs $(s,t)$ where
   $s$ is a function index and $t$ is its trapdoor, $F_{\mathrm{ltdf}}(s,\cdot)$ computes an
   *injective* (deterministic) function $f_s(\cdot)$ over the domain $\{0,1\}^n$, and
   $F_{\mathrm{ltdf}}^{-1}(t,\cdot)$ computes $f_s^{-1}(\cdot)$. If a value $y$ is not in the image
   of $f_s$, i.e., if $f_s^{-1}(y)$ does not exist, then the behavior of
   $F_{\mathrm{ltdf}}^{-1}(t,y)$ is unspecified (because of this, the output of
   $F_{\mathrm{ltdf}}^{-1}$ may need to be checked for correctness in certain applications).

2. *Easy to sample a lossy function:* $S_{\mathrm{loss}}$ outputs $(s,\perp)$ where $s$ is a
   function index, and $F_{\mathrm{ltdf}}(s,\cdot)$ computes a (deterministic) function
   $f_s(\cdot)$ over the domain $\{0,1\}^n$ whose image has size at most $2^r=2^{n-k}$.

3. *Hard to distinguish injective from lossy:* the first outputs of $S_{\mathrm{inj}}$ and
   $S_{\mathrm{loss}}$ are computationally indistinguishable. More formally, let $X_\lambda$
   denote the distribution of $s$ from $S_{\mathrm{inj}}$, and let $Y_\lambda$ denote the
   distribution of $s$ from $S_{\mathrm{loss}}$. Then
   $\{X_\lambda\}\overset{c}{\approx}\{Y_\lambda\}$.

<a id="pdf-74f48b0eff6f-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->

**Section 3.1, hardness of inversion not required (printed p. 14).** Note that we make no
explicit requirement that an injective function be hard to invert. As shown in Lemma 3.3, this
property is implied by combination of the lossiness and indistinguishability properties.

<a id="pdf-74f48b0eff6f-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.95 -->

**Section 3.1, almost-always lossy TDFs (printed p. 14).** For our lattice-based constructions we
need to consider a slightly relaxed definition of lossy TDFs, which we call *almost-always* lossy
TDFs. Namely, we require that *with overwhelming probability* over the randomness of
$S_{\mathrm{inj}}$, the index $s$ of $S_{\mathrm{inj}}$ describes an injective function $f_s$ that
$F_{\mathrm{ltdf}}^{-1}$ inverts correctly on all values in the image of $f_s$. In other words,
there is only a negligible probability (over the choice of $s$) that

*Transcription note.* The sentence continues on p. 15 (`pdf-74f48b0eff6f-p015-b001`).

<a id="pdf-74f48b0eff6f-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Section 3.1, almost-always lossy TDFs, continued (printed p. 15).** $f_s(\cdot)$ is not
injective or that $F_{\mathrm{ltdf}}^{-1}(t,\cdot)$ incorrectly computes $f_s^{-1}(\cdot)$ for
some input. Furthermore, we require that with overwhelming probability, the lossy function $f_s$
generated by $S_{\mathrm{loss}}$ has image size at most $2^r$. In general, the function sampler
cannot check these conditions because they refer to "global" properties of the generated
function. The use of almost-always lossy TDFs does not affect security in our applications
(e.g., CCA-secure encryption) because the adversary has no control over the generation of
trapdoor/lossy functions. Therefore the potential advantage of the adversary due to sampling an
improper function is bounded by a negligible quantity.

<a id="pdf-74f48b0eff6f-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Section 3.2, all-but-one TDFs: overview (printed p. 15).** For our CCA applications, it is
convenient to work with a richer abstraction that we call *all-but-one* (ABO) trapdoor
functions. In an ABO collection, each function has an extra input called its *branch*. All of
the branches are injective trapdoor functions (having the same trapdoor value), except for one
branch which is lossy. The lossy branch is specified as a parameter to the function sampler, and
its value is hidden (computationally) by the resulting function description.

<a id="pdf-74f48b0eff6f-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.95 -->

**Section 3.2, definition of $(n,k)$-all-but-one trapdoor functions (printed p. 15).** We retain
the same notation for $n,k,r$ as above, and also let
$\mathcal B=\{B_\lambda\}_{\lambda\in\mathbb N}$ be a collection of sets whose elements represent
the branches. Then a collection of $(n,k)$-*all-but-one* trapdoor functions with branch
collection $\mathcal B$ is given by a tuple of PPT algorithms
$(S_{\mathrm{abo}},G_{\mathrm{abo}},G_{\mathrm{abo}}^{-1})$ having the following properties:

1. *Sampling a trapdoor function with given lossy branch:* for any $b^*\in B_\lambda$,
   $S_{\mathrm{abo}}(b^*)$ outputs $(s,t)$, where $s$ is a function index and $t$ is its
   trapdoor.

   For any $b\in B_\lambda$ distinct from $b^*$, $G_{\mathrm{abo}}(s,b,\cdot)$ computes an
   injective (deterministic) function $g_{s,b}(\cdot)$ over the domain $\{0,1\}^n$, and
   $G_{\mathrm{abo}}^{-1}(t,b,\cdot)$ computes $g_{s,b}^{-1}(\cdot)$. As above, the behavior of
   $G_{\mathrm{abo}}^{-1}(t,b,y)$ is unspecified if $g_{s,b}^{-1}(y)$ does not exist.

   Additionally, $G_{\mathrm{abo}}(s,b^*,\cdot)$ computes a function $g_{s,b^*}(\cdot)$ over the
   domain $\{0,1\}^n$ whose image has size at most $2^r=2^{n-k}$.

2. *Hidden lossy branch:* the views of any PPT adversary $\mathcal A$ in the following two
   experiments, indexed by a bit $i\in\{0,1\}$, are computationally indistinguishable:
   $\mathcal A$ outputs $(b_0^*,b_1^*)\in B_\lambda\times B_\lambda$ and is given a function
   index $s$, where $(s,t)\leftarrow S_{\mathrm{abo}}(b_i^*)$.

<a id="pdf-74f48b0eff6f-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.95 -->

**Section 3.2, almost-always ABOs (printed p. 15).** Just as with lossy TDFs, we also need to
consider an "almost-always" relaxation of the ABO definition. Specifically, the injective,
invertible, and lossy properties need only hold with overwhelming probability over the choice of
the function index $s$. As with lossy TDFs, the use of almost-always ABOs does not affect
security in our applications.

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
