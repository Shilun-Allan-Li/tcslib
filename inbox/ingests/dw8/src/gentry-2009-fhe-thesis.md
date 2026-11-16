<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: 9e7f32f1b8543416fc6c2fcbfedd5d2d69150226b9bbd2cccac57840a5db7b66 -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# A Fully Homomorphic Encryption Scheme

Craig Gentry. PhD thesis, Stanford University, September 2009 (tag `Gen09`). Uploaded copy:
`craig-thesis.pdf`, 209 PDF pages.

**Scope.** Only the passages that the leveled scheme uses are transcribed (DW-8; GSW
phase-6 rulings P6-Q14 and P6-Q19 with its refinement): Chapter 4, §4.1 (the overview of
$\mathcal E^{(d)}$ and its chain of encrypted secret keys, Recrypt and $\mathrm{Recrypt}'$,
Definition 4.1.2 of the augmented decryption circuit, Definition 4.1.3 of a bootstrappable
scheme, and the construction $\mathsf{KeyGen}_{\mathcal E^{(d)}}$ /
$\mathsf{Encrypt}$ / $\mathsf{Decrypt}$ / $\mathsf{Evaluate}$ / $\mathsf{Augment}$ /
$\mathsf{Reduce}$ with the high-level review), §4.2 (Theorem 4.2.1, correctness; and
**Theorem 4.2.3 with its proof — the security hybrid**) and the opening of §4.3 with
Remark 4.3.1, which says why the chain is acyclic. Chapters 1–3 and 5–, and §§4.2's
complexity theorem and 4.4, are not transcribed. The PDF is not committed. Anchors use the
**physical** PDF page; the printed page is $p-10$ (`p053` is printed page 43). The scoped
raw extraction is `gentry-2009-fhe-thesis.raw.md`. Mathematics is set in LaTeX; the wording
is the thesis's. Notes marked *Transcription note* are not part of the source.

**Index convention (important when reading the library's leveled scheme).** Gentry numbers
keys $0,\dots,d$ and encrypts $\mathrm{sk}_i$ under $\mathrm{pk}_{i-1}$; a fresh ciphertext
is made under $\mathrm{pk}_d$ and the final decryption is under $\mathrm{sk}_0$, so
evaluation runs *down* the index. He says so explicitly: "in the description below we
encrypt the secret keys in reverse order; the only reason is that this ordering simplifies
our description of the recursion in Evaluate" (p. 46).

<a id="pdf-9e7f32f1b854-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.95 -->

**Section 4.1, Leveled Fully Homomorphic Encryption from Bootstrappable Encryption,
Generically (p. 43).** Assume we have an encryption scheme $\mathcal E$ that compactly
evaluates some set of circuits $C_{\mathcal E}$. We want to use $\mathcal E$ to construct a
homomorphic encryption scheme that can handle arbitrary circuits. In this Chapter we prove
a fundamental result: that if $C_{\mathcal E}$ contains (slight augmentations of)
$\mathcal E$'s own decryption circuit $D_{\mathcal E}$ – i.e., if $\mathcal E$ "compactly
evaluates" its (augmented) decryption circuit – then we can use $\mathcal E$ to construct
an efficient scheme that handles circuits of arbitrary depth.

A bit more specifically, for any integer $d$, we use $\mathcal E$ to construct a scheme
$\mathcal E^{(d)}$ that can compactly evaluate circuits of depth up to $d$. The decryption
circuit for $\mathcal E^{(d)}$ is still $D_{\mathcal E}$; the secret key and ciphertexts
are the same size as in $\mathcal E$. **The public key in $\mathcal E^{(d)}$ consists of
$d+1$ public keys from $\mathcal E$, together with a chain of encrypted $\mathcal E$ secret
keys – the first $\mathcal E$ secret key encrypted under the second $\mathcal E$ public key,
and so on.** In short, the family of schemes $\{\mathcal E^{(d)}\}$ is leveled fully
homomorphic. **We base the semantic security of $\mathcal E^{(d)}$ on that of $\mathcal E$
using a hybrid argument; as usual with hybrid arguments, the reduction loses a factor
linear in $d$.**

In Chapter 4.3, we describe how one can obtain a fully homomorphic encryption scheme (where
the public key size does not depend on the maximum number of levels we want to evaluate) by
assuming key-dependent-message (KDM) security, specifically circular-security – i.e., that
one can safely encrypt a $\mathcal E$ secret key under its associated public key.

<a id="pdf-9e7f32f1b854-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.95 -->

**Section 4.1, why bootstrappability refreshes along the chain (p. 44).** Since this
critical property of $\mathcal E$ – that it can compactly evaluate (slight augmentations
of) its own decryption circuit – is self-referential and universal, we give it the obvious
name: *bootstrappability*. Why should bootstrappability be such a powerful feature? At a
high level, the reason is that bootstrappability allows us periodically to "refresh"
ciphertexts associated to interior nodes in a circuit; we can refresh for an arbitrary
number of levels in the circuit, and thus can evaluate circuits of arbitrary depth. **To
"refresh" a ciphertext that encrypts a plaintext $\pi$ under $\mathcal E$ public key
$\mathrm{pk}_i$, we re-encrypt it under $\mathrm{pk}_{i+1}$ and then homomorphically apply
the decryption circuit to the result, using the secret key $\mathrm{sk}_i$ that is
encrypted under $\mathrm{pk}_{i+1}$, thereby obtaining an encryption of $\pi$ under
$\mathrm{pk}_{i+1}$.** Homomorphically evaluating the decryption circuit decrypts the inner
ciphertext under $\mathrm{pk}_i$, but within homomorphic encryption under
$\mathrm{pk}_{i+1}$. The implicit decryption "refreshes" the ciphertext, but the plaintext
is never revealed; the plaintext is always covered by at least one layer of encryption. Now
that the ciphertext is refreshed, we can "continue" correctly evaluating the circuit.

<a id="pdf-9e7f32f1b854-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=0.95 -->

**Section 4.1, the Recrypt algorithm (p. 44).** To see how this works mathematically, begin
by considering the following algorithm, called Recrypt. For simplicity, suppose the
plaintext space $\mathcal P$ is $\{0,1\}$ and $D_{\mathcal E}$ is a boolean circuit in
$C_{\mathcal E}$. Let $(\mathrm{sk}_1,\mathrm{pk}_1)$ and
$(\mathrm{sk}_2,\mathrm{pk}_2)$ be two $\mathcal E$ key-pairs. Let $\psi_1$ be an encryption
of $\pi\in\mathcal P$ under $\mathrm{pk}_1$. Let $\overline{\mathrm{sk}_{1j}}$ be an
encryption of the $j$-th bit of the first secret key $\mathrm{sk}_1$ under the second public
key $\mathrm{pk}_2$. Recrypt takes as these things as input, and outputs an encryption of
$\pi$ under $\mathrm{pk}_2$.

$$
\begin{aligned}
&\mathsf{Recrypt}(\mathrm{pk}_2,D_{\mathcal E},
  \langle\overline{\mathrm{sk}_{1j}}\rangle,\psi_1).\\
&\qquad \text{Set }\overline{\psi_{1j}}\xleftarrow{\ R\ }
  \mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_2,\psi_{1j})\text{ where }\psi_{1j}
  \text{ is the }j\text{-th bit of }\psi_1\\
&\qquad \text{Set }\psi_2\leftarrow\mathsf{Evaluate}_{\mathcal E}(\mathrm{pk}_2,
  D_{\mathcal E},\langle\langle\overline{\mathrm{sk}_{1j}}\rangle,
  \langle\overline{\psi_{1j}}\rangle\rangle)\\
&\qquad \text{Output }\psi_2
\end{aligned}
$$

Above, the Evaluate algorithm takes in all of the bits of $\mathrm{sk}_1$ and all of the
bits of $\psi_1$, each encrypted under $\mathrm{pk}_2$. Then, $\mathcal E$ is used to
evaluate the decryption circuit homomorphically. The output $\psi_2$ is thus an encryption
under $\mathrm{pk}_2$ of $\mathsf{Decrypt}_{\mathcal E}(\mathrm{sk}_1,\psi_1)\to\pi$.

*Transcription note.* "Recrypt takes as these things as input" is transcribed as printed.
The `-layout` extraction loses the overbars that mark a value as encrypted (it prints
`sk1j` for $\overline{\mathrm{sk}_{1j}}$ and `ψ1j` for both $\psi_{1j}$ and
$\overline{\psi_{1j}}$); the overbars were read from the page images and are restored here.
The superscript $R$ on the assignment arrow marks a random draw.

<a id="pdf-9e7f32f1b854-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.95 -->

**Definition 4.1.2 (Augmented Decryption Circuit) (pp. 45–46).** Let $D_{\mathcal E}$ be
$\mathcal E$'s decryption circuit, which takes a secret key and ciphertext as input, each
formatted as an element of $\mathcal P^{\ell(\lambda)}$, where $\mathcal P$ is the
plaintext space. Let $\Gamma$ be a set of gates with inputs and output in $\mathcal P$,
which includes the trivial gate (input and output are the same). We call a circuit composed
of multiple copies of $D_{\mathcal E}$ connected by a single $g$ gate (the number of copies
equals the number of inputs to $g$) a "$g$-augmented decryption circuit." We denote the set
of $g$-augmented decryption circuits, $g\in\Gamma$, by $D_{\mathcal E}(\Gamma)$.

<a id="pdf-9e7f32f1b854-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.95 -->

**Definition 4.1.3 (Bootstrappable Encryption Scheme) (p. 46).** As before, let
$C_{\mathcal E}$ denote the set of circuits that $\mathcal E$ can compactly evaluate. We
say that $\mathcal E$ is *bootstrappable with respect to $\Gamma$* if

$$
D_{\mathcal E}(\Gamma)\subseteq C_{\mathcal E}.
$$

For example, if $\Gamma$ includes the trivial gate and NAND, $\mathcal E$ is bootstrappable
with respect to $\Gamma$ if $C_{\mathcal E}$ contains $D_{\mathcal E}$ and the circuit
formed by joining two copies of $D_{\mathcal E}$ with a NAND gate. Remarkably, as we will
show, if there is a scheme $\mathcal E$ that can compactly evaluate only these two
circuits, then there is a scheme that is leveled fully homomorphic.

<a id="pdf-9e7f32f1b854-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.95 -->

**Section 4.1, the construction of $\mathcal E^{(d)}$, and the reverse-order convention
(p. 46).** From the informal description above, it should already be somewhat clear how to
use a bootstrappable encryption scheme to construct a leveled fully homomorphic one; below,
we give a more formal description. Let $\mathcal E$ be bootstrappable with respect to a set
of gates $\Gamma$. For any integer $d\ge 1$, we use $\mathcal E$ to construct a scheme
$\mathcal E^{(d)}=(\mathsf{KeyGen}_{\mathcal E^{(d)}},\mathsf{Encrypt}_{\mathcal E^{(d)}},
\mathsf{Evaluate}_{\mathcal E^{(d)}},\mathsf{Decrypt}_{\mathcal E^{(d)}})$ that can handle
all circuits of depth $d$ with gates in $\Gamma$. **Note that in the description below we
encrypt the secret keys in reverse order; the only reason is that this ordering simplifies
our description of the recursion in Evaluate.** When we refer to the *level* of a wire in
$C$, we mean the level of the gate for which the wire is an input. We use the notation
$D_{\mathcal E}(\Gamma,\delta)$ to refer to the set of circuits that equal a $\delta$-depth
circuit with gates in $\Gamma$ augmented by $D_{\mathcal E}$ (copies of $D_{\mathcal E}$
become inputs to the $\delta$-depth circuit).

<a id="pdf-9e7f32f1b854-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.95 -->

**The key chain: $\mathsf{KeyGen}_{\mathcal E^{(d)}}$ (pp. 46–47).**
$\mathsf{KeyGen}_{\mathcal E^{(d)}}(\lambda,d)$. Takes as input a security parameter
$\lambda$ and a positive integer $d$. For $\ell=\ell(\lambda)$ as in Definition 4.1.2, it
sets

$$
\begin{aligned}
(\mathrm{sk}_i,\mathrm{pk}_i)&\xleftarrow{\ R\ }\mathsf{KeyGen}_{\mathcal E}(\lambda)
  &&\text{for } i\in[0,d]\\
\overline{\mathrm{sk}_{ij}}&\xleftarrow{\ R\ }
  \mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_{i-1},\mathrm{sk}_{ij})
  &&\text{for } i\in[1,d],\ j\in[1,\ell]
\end{aligned}
$$

where $\mathrm{sk}_{i1},\dots,\mathrm{sk}_{i\ell}$ is the representation of
$\mathrm{sk}_i$ as elements of $\mathcal P$. It outputs the secret key
$\mathrm{sk}^{(d)}\leftarrow\mathrm{sk}_0$ and the public key
$\mathrm{pk}^{(d)}\leftarrow(\langle\mathrm{pk}_i\rangle,
\langle\overline{\mathrm{sk}_{ij}}\rangle)$. Let $\mathcal E^{(\delta)}$ refer to the
sub-system that uses $\mathrm{sk}^{(\delta)}\leftarrow\mathrm{sk}_0$ and
$\mathrm{pk}^{(\delta)}\leftarrow(\langle\mathrm{pk}_i\rangle_{i\in[0,\delta]},
\langle\overline{\mathrm{sk}_{ij}}\rangle_{i\in[1,\delta]})$ for $\delta\le d$.

*Transcription note.* The second display is the key chain: $\ell$ ciphertexts for each
$i\in[1,d]$, so $\ell\cdot d$ encrypted secret-key elements in all, and only this part of
the public key grows with $d$. The `-layout` extraction prints both sides of that line as
`skij`, losing the overbar on the left; the page image (150 dpi) shows
$\overline{\mathrm{sk}_{ij}}$ on the left and $\mathrm{sk}_{ij}$ inside
$\mathsf{Encrypt}_{\mathcal E}$, as transcribed.

<a id="pdf-9e7f32f1b854-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.95 -->

**$\mathsf{Encrypt}$, $\mathsf{Decrypt}$ and $\mathsf{Evaluate}$ for
$\mathcal E^{(d)}$ (p. 47).**

$\mathsf{Encrypt}_{\mathcal E^{(d)}}(\mathrm{pk}^{(d)},\pi)$. Takes as input a public key
$\mathrm{pk}^{(d)}$ and a plaintext $\pi\in\mathcal P$. It outputs a ciphertext
$\psi\xleftarrow{\ R\ }\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_d,\pi)$.

$\mathsf{Decrypt}_{\mathcal E^{(d)}}(\mathrm{sk}^{(d)},\psi)$. Takes as input a secret key
$\mathrm{sk}^{(d)}$ and a ciphertext $\psi$ (which should be an encryption under
$\mathrm{pk}_0$). It outputs $\mathsf{Decrypt}_{\mathcal E}(\mathrm{sk}_0,\psi)$.

$\mathsf{Evaluate}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
Takes as input a public key $\mathrm{pk}^{(\delta)}$, a circuit $C_\delta$ of depth at most
$\delta$ with gates in $\Gamma$, and a tuple of input ciphertexts $\Psi_\delta$ (where each
input ciphertext should be under $\mathrm{pk}_\delta$). **We assume that each wire in
$C_\delta$ connects gates at consecutive levels; if not, add trivial gates to make it so.**
If $\delta=0$, it outputs $\Psi_0$ and terminates. Otherwise, it does the following:

- Sets $(C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})\leftarrow
  \mathsf{Augment}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
- Sets $(C_{\delta-1},\Psi_{\delta-1})\leftarrow
  \mathsf{Reduce}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},
  C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})$.
- Runs $\mathsf{Evaluate}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},
  C_{\delta-1},\Psi_{\delta-1})$.

*Transcription note.* The highlighted assumption is the thesis's own layering requirement
on the circuit: every wire joins consecutive levels, padded with trivial gates if not.

<a id="pdf-9e7f32f1b854-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.95 -->

**$\mathsf{Augment}$ and $\mathsf{Reduce}$ (p. 47).**

$\mathsf{Augment}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
Takes as input a public key $\mathrm{pk}^{(\delta)}$, a circuit $C_\delta$ of depth at most
$\delta$ with gates in $\Gamma$, and a tuple of input ciphertexts $\Psi_\delta$ (where each
input ciphertext should be under $\mathrm{pk}_\delta$). It augments $C_\delta$ with
$D_{\mathcal E}$; call the resulting circuit $C^\dagger_{\delta-1}$. Let
$\Psi^\dagger_{\delta-1}$ be the tuple of ciphertexts formed by replacing each input
ciphertext $\psi\in\Psi_\delta$ by the tuple
$\langle\langle\overline{\mathrm{sk}_{\delta j}}\rangle,
\langle\overline{\psi_j}\rangle\rangle$, where $\overline{\psi_j}\leftarrow
\mathsf{WeakEncrypt}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},\psi_j)$ and the
$\psi_j$'s form the properly-formatted representation of $\psi$ as elements of
$\mathcal P$. It outputs $(C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})$.

$\mathsf{Reduce}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C^\dagger_\delta,
\Psi^\dagger_\delta)$. Takes as input a public key $\mathrm{pk}^{(\delta)}$, a tuple of
input ciphertexts $\Psi^\dagger_\delta$ (where each input ciphertext should be in the image
of $\mathsf{Encrypt}_{\mathcal E^{(\delta)}}$), and a circuit $C^\dagger_\delta\in
D_{\mathcal E}(\Gamma,\delta+1)$. It sets $C_\delta$ to be the sub-circuit of
$C^\dagger_\delta$ consisting of the first $\delta$ levels. It sets $\Psi_\delta$ to be the
induced input ciphertexts of $C_\delta$, where the ciphertext $\psi^{(w)}_\delta$
associated to wire $w$ at level $\delta$ is set to
$\mathsf{Evaluate}_{\mathcal E}(\mathrm{pk}_\delta,C^{(w)}_\delta,\Psi^{(w)}_\delta)$,
where $C^{(w)}_\delta$ is the sub-circuit of $C^\dagger_\delta$ with output wire $w$, and
$\Psi^{(w)}_\delta$ are the input ciphertexts for $C^{(w)}_\delta$. It outputs
$(C_\delta,\Psi_\delta)$.

<a id="pdf-9e7f32f1b854-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=0.95 -->

**Section 4.1, high-level review of the Evaluate algorithm (p. 48).** In the full scheme
above, the ciphertexts that we associate to the decryption circuit that was attached to
wire $w$ are analogous to the ones we used in $\mathrm{Recrypt}'_{\mathcal E}$: **the
encrypted secret key ($\mathrm{sk}_d$ under $\mathrm{pk}_{d-1}$), and the re-encryption
ciphertexts of $\psi_w$ under $\mathrm{pk}_{d-1}$.** By the correctness of Recrypt, the
ciphertext now associated to $w$ (after performing $\mathsf{Evaluate}_{\mathcal E}$) should
encrypt the same plaintext as $\psi_w$, but now under $\mathrm{pk}_{d-1}$.

The Reduce step simply performs this Evaluate up to the wire $w$, and one level beyond. We
know that Evaluate can correctly continue one level beyond the wire $w$, because (by
assumption) $\mathcal E$ can evaluate not just the decryption circuit attached to $w$, but
can evaluate a circuit containing one $\Gamma$-gate above $w$. Reduce outputs $C_{d-1}$ and
ciphertexts associated to $C_{d-1}$'s input wires. We have made progress, since $C_{d-1}$
is one level shallower than $C_d$. We perform this entire process $d-1$ more times to
obtain the final output ciphertexts.

<a id="pdf-9e7f32f1b854-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.1 (correctness) (p. 49).** Let $\mathcal E$ be bootstrappable
with respect to a set of gates $\Gamma$. Then $\mathcal E^{(d)}$ compactly evaluates all
circuits of depth $d$ with gates in $\Gamma$ – i.e., if $\Gamma$ is a universal set of
gates, the family $\mathcal E^{(d)}$ is leveled fully homomorphic.

*Transcription note.* The proof of Theorem 4.2.1 (pp. 49–50) is not transcribed; only its
statement is, since the citation is for the construction and the security hybrid.

<a id="pdf-9e7f32f1b854-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.3 (the security hybrid) (p. 50).** Finally, assuming the
semantic security of $\mathcal E$, we prove the semantic security of $\mathcal E^{(d)}$.

**Theorem 4.2.3.** Let $\mathcal A$ be an algorithm that $(t,\epsilon)$-breaks the semantic
security of $\mathcal E^{(d)}$. Then, there is an algorithm $\mathcal B$ that
$(t',\epsilon')$-breaks the semantic security of $\mathcal E$ for $t'\approx t\cdot\ell$
and $\epsilon'\ge\epsilon/\ell(d+1)$, for $\ell$ as in Definition 4.1.2.

*Proof.* (Theorem 4.2.3) Let $(\mathcal E)^\ell$ be equivalent to $\mathcal E$, but with
plaintext space $\mathcal P^{\le\ell}$, where $\mathsf{Encrypt}_{(\mathcal E)^\ell}$
involves up to $\ell$ invocations of $\mathcal E$ and a concatenation of the results. We
use a hybrid argument to show that $\mathcal B$ $(t'',\epsilon'')$-breaks the semantic
security of $(\mathcal E)^\ell$ for $t''\approx t$ and $\epsilon''\ge\epsilon/(d+1)$, from
which the result follows.

**For $k\in[0,d]$, let Game $k$ denote a game against $\mathcal E^{(d)}$ in which
everything is exactly as in the real-world game, except that for all $i\in[1,k]$ the
challenger sets**

$$
(\mathrm{sk}'_i,\mathrm{pk}'_i)\xleftarrow{\ R\ }\mathsf{KeyGen}_{\mathcal E}(\lambda)
\quad\text{and}\quad
\overline{\mathrm{sk}_{ij}}\xleftarrow{\ R\ }
\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_{i-1},\mathrm{sk}'_{ij})
$$

In other words, for $i\in[1,k]$, $\overline{\mathrm{sk}_{ij}}$ is the encryption (under
$\mathrm{pk}_{i-1}$) of the $j$-th bit of a random secret key $\mathrm{sk}'_i$ unrelated to
$\mathrm{sk}_i$. Game $d+1$ is identical to Game $d$, except that the challenger ignores
$b$ and $(\pi_0,\pi_1)$, generates a random plaintext $\pi$ of the appropriate length, and
encrypts $\pi$ to construct the challenge ciphertext. Let $\epsilon_k$ denote the
adversary's advantage in Game $k$.

Since Game $0$ is identical to the real world attack, the adversary's advantage is
$\epsilon$ by assumption. Also, $\epsilon_{d+1}=0$, since the challenge is independent of
$b$. Consequently, for some $k\in[0,d]$, it must hold that
$|\epsilon_k-\epsilon_{k+1}|\ge\epsilon/(d+1)$; fix this value of $k$.

*Transcription note.* The thesis's $\epsilon$ is set in a font that the `-layout`
extraction renders as the character `²`; it is the advantage $\epsilon$ throughout, as the
page image (150 dpi) confirms.

<a id="pdf-9e7f32f1b854-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.3, the reduction (p. 51).** $\mathcal B$ uses $\mathcal A$ to
break $(\mathcal E)^\ell$ as follows. $\mathcal B$ receives from the challenger a public
key $\mathrm{pk}$. $\mathcal B$ generates the secret and public values exactly as in Game
$k$, except that it replaces its original value of $\mathrm{pk}_k$ with $\mathrm{pk}$.
Also, if $k<d$, it generates a dummy key pair
$(\mathrm{sk}'_{k+1},\mathrm{pk}'_{k+1})\xleftarrow{\ R\ }
\mathsf{KeyGen}_{\mathcal E}(\lambda)$, sets $\pi_0\leftarrow\mathrm{sk}_{k+1}$ and
$\pi_1\leftarrow\mathrm{sk}'_{k+1}$, and requests a challenge ciphertext (under
$\mathrm{pk}$) encrypting either $\pi_0,\pi_1\in\mathcal P^\ell$. The challenger generates
$\beta\xleftarrow{\ R\ }\{0,1\}$ and sends a tuple of ciphertexts $\langle\psi_j\rangle$
encrypting the bits $\langle\pi_{\beta j}\rangle$. $\mathcal B$ replaces its original tuple
$\langle\overline{\mathrm{sk}_{(k+1)j}}\rangle$ with the tuple $\langle\psi_j\rangle$. One
can verify that the public values are generated exactly as in Game $k+\beta$. $\mathcal B$
sends the public values to $\mathcal A$.

Eventually, $\mathcal A$ requests a challenge ciphertext on $\pi_0$ or $\pi_1$.
$\mathcal B$ sets $b\xleftarrow{\ R\ }\{0,1\}$. If $k<d$, $\mathcal B$ sends the values
$\psi_j\xleftarrow{\ R\ }\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_d,\pi_{bj})$. If $k=d$,
$\mathcal B$ generates random $\pi\xleftarrow{\ R\ }\mathcal P$ and asks the challenger for
a challenge ciphertext on $\pi_b$ or $\pi$. The challenger generates
$\beta\xleftarrow{\ R\ }\{0,1\}$ and encrypts $\pi_b$ or $\pi$ accordingly, and
$\mathcal B$ forwards the challenge to $\mathcal A$. $\mathcal A$ sends a bit $b'$.
$\mathcal B$ sends bit $\beta'\leftarrow b\oplus b'$ to the challenger. One can verify that
the challenge is generated as in Game $k+\beta$.

Since $\mathcal B$'s simulation has the same distribution as Game $k+\beta$, and the
probability that $\mathcal B$ outputs $0$ is $\epsilon_{k+\beta}$. The result follows.
$\square$

*Transcription note.* The last sentence is transcribed as printed; it reads as an
incomplete clause ("Since …, and the probability … is $\epsilon_{k+\beta}$.").

<a id="pdf-9e7f32f1b854-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.95 -->

**Section 4.3, why the chain is acyclic (pp. 51–52).** The length of the public key in
$\mathcal E^{(d)}$ is proportional to $d$ (the depth of the circuits that can be evaluated).
It would be preferable to have a construction $\mathcal E^*$ where the public key size is
completely independent of the circuit depth, a construction that is fully homomorphic
rather than merely leveled fully homomorphic. Here is the obvious way to make the public
key $\mathrm{pk}^*$ of $\mathcal E^*$ short: for $\mathcal E$ key pair
$(\mathrm{sk},\mathrm{pk})$, $\mathrm{pk}^*$ includes only $\mathrm{pk}$ and (the "bits"
of) $\mathrm{sk}$ encrypted under $\mathrm{pk}$. In other words, we have a cycle (in fact,
a self-loop in this example) of encrypted secret keys rather than an acyclic chain. It is
clear that $\mathcal E^*$ is correct: the recursive algorithm
$\mathsf{Evaluate}_{\mathcal E^*}$ works as before, except that the implicit recryptions
generate "refreshed" ciphertexts under the same public key.

**Why didn't we present this construction in the first place? Using an acyclic chain of
encrypted secret keys allowed us to base the security of $\mathcal E^{(d)}$ on
$\mathcal E$ using a hybrid argument; this hybrid argument breaks down when there is a
cycle.** In general, a semantically secure encryption scheme is not guaranteed to be
KDM-secure – i.e., secure when the adversary can request the encryptions of key-dependent
messages, such as the secret key itself.

<a id="pdf-9e7f32f1b854-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.95 -->

**Remark 4.3.1 (p. 52).** Canetti [27] proposed the acyclic, leveled approach as a way to
remove the need for KDM-security. Our initial approach had actually been to use
$\mathcal E^*$ (with the self-loop), and assume, or try to prove, KDM-security.
