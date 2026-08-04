<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: e658890bd7efd74e8042d47d6141825821ce4e0e28440509a52fca914282bbb7 -->

<a id="pdf-e658890bd7ef-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
## The Quantum Channel

<a id="pdf-e658890bd7ef-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
A noisy quantum channel (transmission, idle decoherence, or noisy gates) can map a pure input to a mixed output via a superoperator on the density matrix. Diagonalizing the superoperator writes it as a direct sum of (possibly non-unitary) matrices acting on input pure states with various probabilities; correcting each such matrix corrects the whole channel. Henceforth only a single (possibly non-unitary) matrix acting on a pure state is considered.

<a id="pdf-e658890bd7ef-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.98 -->
## A Simple Code

<a id="pdf-e658890bd7ef-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.96 -->
**Shor's nine-qubit code.** A single logical qubit is encoded into nine qubits (protecting against a single-qubit error) by
$$\ket{0}\to\ket{\overline{0}}=(\ket{000}+\ket{111})(\ket{000}+\ket{111})(\ket{000}+\ket{111})$$
$$\ket{1}\to\ket{\overline{1}}=(\ket{000}-\ket{111})(\ket{000}-\ket{111})(\ket{000}-\ket{111}).$$
Distinguishing the two codewords requires measuring at least three qubits.

<a id="pdf-e658890bd7ef-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.94 -->
**Bit-flip correction.** A single bit flip is located by comparing qubits within a block of three — measuring only their *difference* (not the qubits, to preserve the superposition). Comparing qubits 1–2 detects a disagreement (invalid codeword); comparing qubits 1–3 then pins down which qubit flipped, which is corrected by flipping it back. The same comparisons are applied within each block of three.

<a id="pdf-e658890bd7ef-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.94 -->
**Phase-flip correction.** A relative phase ($-1$) error on the first block sends
$$\ket{\overline{0}}\to(\ket{000}-\ket{111})(\ket{000}+\ket{111})(\ket{000}+\ket{111})$$
$$\ket{\overline{1}}\to(\ket{000}+\ket{111})(\ket{000}-\ket{111})(\ket{000}-\ket{111}).$$
Comparing the sign of block 1 vs block 2, then block 1 vs block 3, locates the sign error to one block, whose sign is flipped back. Only sign *agreement* is measured (measuring the signs would reveal $\ket{\overline{0}}$ vs $\ket{\overline{1}}$ and destroy superposition).

<a id="pdf-e658890bd7ef-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.96 -->
**Pauli errors.** A combined bit-and-sign flip is corrected by running both procedures in sequence (even when on different qubits). The single-qubit errors are
$$X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad Y=iXZ=\begin{pmatrix}0&-i\\i&0\end{pmatrix}.$$
Notation $X_i,Y_i,Z_i$ denotes $X,Y,Z$ acting on the $i$th qubit.

<a id="pdf-e658890bd7ef-p001-b008"></a>
<!-- pdf-source: page=1; block=8; confidence=0.95 -->
**General one-qubit error.** Any $2\times2$ error is a complex linear combination of $X,Y,Z,I$. On $\ket{\psi}=\alpha\ket{\overline{0}}+\beta\ket{\overline{1}}$ it acts as
$$\ket{\psi}\to a\,X_i\ket{\psi}+b\,Y_i\ket{\psi}+c\,Z_i\ket{\psi}+d\,\ket{\psi}.$$
The bit/sign comparison acts as a measurement collapsing the state to $X_i\ket{\psi}$, $Y_i\ket{\psi}$, $Z_i\ket{\psi}$, or $\ket{\psi}$ with probabilities $|a|^2,|b|^2,|c|^2,|d|^2$; in each case the error is identified and corrected.

<a id="pdf-e658890bd7ef-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
## Properties of Any Quantum Code

<a id="pdf-e658890bd7ef-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
**Coding space and error group.** A code encoding $k$ qubits in $n$ has $2^k$ basis codewords; their linear combinations are valid codewords, spanning the coding space $T$, a subspace of the $2^n$-dimensional Hilbert space. Since correcting $E$ and $F$ implies correcting $aE+bF$, only a basis of errors need be considered; a convenient basis is tensor products of $X,Y,Z,I$. The **weight** of such an operator is the number of qubits on which it differs from $I$. These tensor products with an overall factor $-1$ or $\pm i$ form a group $\mathcal{G}$ (written $\mathcal{G}_n$ per qubit count) under multiplication, central to the stabilizer formalism: $\mathcal{G}_1$ is the quaternionic group, and $\mathcal{G}_n$ the direct product of $n$ quaternion copies modulo a global phase.

<a id="pdf-e658890bd7ef-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->
**Error-correction condition.** To correct errors $\{E_a\}$, an error $E_a$ on codeword $\ket{\psi_i}$ must be distinguishable from $E_b$ on a different codeword $\ket{\psi_j}$, requiring orthogonality
$$\bra{\psi_i}E_a^\dagger E_b\ket{\psi_j}=0\quad(i\neq j).$$
Also, measuring the error must reveal nothing about the state within the coding space:
$$\bra{\psi_i}E_a^\dagger E_b\ket{\psi_i}=\bra{\psi_j}E_a^\dagger E_b\ket{\psi_j}.$$
These combine into the single condition (Knill–Laflamme; Bennett et al.)
$$\bra{\psi_i}E_a^\dagger E_b\ket{\psi_j}=C_{ab}\,\delta_{ij},$$
with $C_{ab}$ independent of $i,j$. (The identity is normally included among the errors.)

<a id="pdf-e658890bd7ef-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.94 -->
**Proof (sufficiency).** Necessity was argued above. For sufficiency: $C_{ab}$ is Hermitian, hence diagonalizable; diagonalizing and rescaling gives a new error basis $\{F_a\}$ satisfying, for each $a$, either
$$\bra{\psi_i}F_a^\dagger F_b\ket{\psi_j}=\delta_{ab}\delta_{ij}\quad\text{or}\quad \bra{\psi_i}F_a^\dagger F_b\ket{\psi_j}=0.$$
Errors of the second type annihilate every codeword (zero probability). The remaining errors always produce orthogonal states, so a measurement identifies exactly which occurred and it is corrected. Hence a code satisfies the condition for a set $\mathcal{E}$ iff it corrects all errors in $\mathcal{E}$.

<a id="pdf-e658890bd7ef-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.95 -->
**Degeneracy.** A further basis change makes any two errors on a codeword produce either orthogonal or identical states; annihilating $F_a$ correspond to errors acting identically on codewords (e.g. $Z_1$ and $Z_2$ in Shor's code, so $Z_1-Z_2$ annihilates codewords). This happens iff $C_{ab}$ lacks maximal rank. A code with singular $C_{ab}$ is **degenerate**, otherwise **nondegenerate**; Shor's nine-qubit code is degenerate. Degeneracy depends on the error set the code is meant to correct.

<a id="pdf-e658890bd7ef-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.96 -->
**Distance.** With $E=E_a^\dagger E_b\in\mathcal{G}$, the code's **distance** is the weight of the smallest $E\in\mathcal{G}$ for which the condition fails. A code correcting up to $t$ errors must have distance $\geq 2t+1$; every code has distance $\geq 1$. A distance-$d$ code encoding $k$ qubits in $n$ is an $[n,k,d]$ code (often written $[[n,k,d]]$ elsewhere to distinguish it from a classical $[n,k,d]$ code).

<a id="pdf-e658890bd7ef-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->
**Variations.** For error *detection* only, each $E_a$ need be distinguished merely from $I$ (set $E_b=I$), so detecting $s$ errors requires distance $\geq s+1$. For *located* errors (quantum erasure channel), $E_a$ need only be distinguished from $E_b$ acting on the same qubits, so $E_a^\dagger E_b$ has the same weight as $E_a$; correcting $r$ located errors requires distance $\geq r+1$. Combining tasks: correcting $t$ arbitrary errors, $r$ located errors, and detecting a further $s$ errors requires distance $\geq r+s+2t+1$.

<a id="pdf-e658890bd7ef-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
## Error Models

<a id="pdf-e658890bd7ef-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.94 -->
**Baseline model.** Errors are assumed independent across qubits and, when they occur, equally likely $X$, $Y$, or $Z$. For small per-qubit error probability $\epsilon$, ignoring more than $t$ errors costs only $O(\epsilon^{t+1})$; hence the focus is on codes correcting up to $t$ arbitrary errors, which handle any error on $\leq t$ qubits that keeps the data in the computational space.

<a id="pdf-e658890bd7ef-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.00 -->
**Leakage errors.** Some errors move a qubit outside the computational space (e.g. ion to a different excited state, photon escape), so standard correction networks (which assume $\ket{0}/\ket{1}$) fail. A measurement distinguishing the computational space from other states detects such a *leakage error* and identifies its qubit; resetting the qubit (cooling to ground, or a new random-polarization photon) turns it into a located error. The detection network (figure) flips an ancilla to $\ket{1}$ when the data qubit is $\ket{0}$ or $\ket{1}$, and leaves it $\ket{0}$ otherwise, signalling leakage; it assumes non-computational states do not interact with other qubits.

<a id="pdf-e658890bd7ef-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.94 -->
**Correlated and biased errors.** Correlated multi-qubit errors need no change of formalism provided a $t$-qubit correlated error has probability $O(\epsilon^t)$, matching the uncorrelated rate. The equal-$X,Y,Z$ assumption is unrealistic; e.g. spontaneous emission gives an *amplitude damping* channel: the excited state either decays, producing error $X+iY$ with probability $\epsilon$, or does not, giving error $I-Z$ with probability $O(\epsilon^2)$. Since the only $O(1)$ effect is the identity, a single-arbitrary-error-correcting code suffices to lowest order, though codes tailored to the restricted error set can be more efficient.

<a id="pdf-e658890bd7ef-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.98 -->
# Stabilizer Coding

## The Nine-Qubit Code Revisited

<a id="pdf-e658890bd7ef-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
Correcting the nine-qubit code amounts to measuring operator eigenvalues. Bit-flip detection on the first block: compare qubits via $Z_1Z_2$ and $Z_1Z_3$ (eigenvalue $+1$ if agreeing, $-1$ if differing). Sign-error detection: measure $X_1X_2X_3X_4X_5X_6$ and $X_1X_2X_3X_7X_8X_9$ ($+1$ if signs agree, $-1$ otherwise). Full correction requires measuring eight operators.

<a id="pdf-e658890bd7ef-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
**Stabilizer of Shor's nine-qubit code** — generators $M_1,\dots,M_8$:

| | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
|$M_1$|Z|Z|I|I|I|I|I|I|I|
|$M_2$|Z|I|Z|I|I|I|I|I|I|
|$M_3$|I|I|I|Z|Z|I|I|I|I|
|$M_4$|I|I|I|Z|I|Z|I|I|I|
|$M_5$|I|I|I|I|I|I|Z|Z|I|
|$M_6$|I|I|I|I|I|I|Z|I|Z|
|$M_7$|X|X|X|X|X|X|I|I|I|
|$M_8$|X|X|X|I|I|I|X|X|X|

<a id="pdf-e658890bd7ef-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.96 -->
**Definition (stabilizer).** The codewords $\ket{\overline 0},\ket{\overline 1}$ are $+1$ eigenvectors of all eight operators. The operators in $\mathcal G$ fixing both codewords form a group $S$, the *stabilizer* of the code, with generators $M_1,\dots,M_8$; every stabilizer element is a product of these generators.

<a id="pdf-e658890bd7ef-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.96 -->
Measuring $M_1$ detects $X_1$ or $X_2$: both anticommute with $M_1$, while $X_3,\dots,X_9$ commute with it. Likewise $M_2$ detects $X_1,X_3$ and $M_7$ detects $Z_1,\dots,Z_6$. General principle: if $M\in S$, $\{M,E\}=0$, $\ket\psi\in T$, then
$$ME\ket\psi=-EM\ket\psi=-E\ket\psi,$$
so $E\ket\psi$ is a $-1$ eigenvector of $M$; measuring $M$ detects $E$.

<a id="pdf-e658890bd7ef-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.00 -->
The code has distance three. Any weight-one operator $X_i,Y_i,Z_i$ anticommutes with some $M_j$, so the error-correction condition holds for $E_a$ of weight one, $E_b=I$. Every weight-two operator anticommutes with some element of $S$ except $Z_aZ_b$ with $a,b$ in the same block of three; such operators lie in $S$, giving $Z_aZ_b\ket\psi=\ket\psi$ and $\bra\psi Z_aZ_b\ket\psi=1$, so the condition still holds (the errors act identically). At weight three the condition can fail: $X_1X_2X_3$ commutes with all of $S$ yet
$$\bra{\overline0}X_1X_2X_3\ket{\overline0}=+1,\qquad \bra{\overline1}X_1X_2X_3\ket{\overline1}=-1.$$

<a id="pdf-e658890bd7ef-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.98 -->
## The General Stabilizer Code

<a id="pdf-e658890bd7ef-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.94 -->
**General stabilizer code.** $S$ is an Abelian subgroup of $\mathcal G$ and the coding space $T$ is the joint $+1$ eigenspace fixed by $S$. Parity of $Y$'s in stabilizer elements controls whether basis-codeword coefficients are real (even) or possibly imaginary (odd); by Rains, a real code with the same parameters exists whenever any code does, so attention is restricted to real codes.

To encode $k$ qubits in $n$: $\dim T=2^k$ and $|S|=2^{n-k}$, where $T=\{\ket\psi : M\ket\psi=\ket\psi\ \forall M\in S\}$. $S$ must be Abelian and contain neither $i$ nor $-1$. Properties of $\mathcal G$: since $X^2=Y^2=Z^2=I$, every element squares to $\pm1$; $X,Y,Z$ anticommute on the same qubit and commute on different qubits, so any two elements either commute or anticommute; elements are Hermitian or anti-Hermitian (with $A\in\mathcal G\Rightarrow A^\dagger\in\mathcal G$); every element is unitary.

<a id="pdf-e658890bd7ef-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.00 -->
If $M\in S$, $\ket{\psi_i}\in T$, $\{M,E\}=0$, then $ME\ket{\psi_i}=-E\ket{\psi_i}$, so
$$\bra{\psi_i}E\ket{\psi_j}=\bra{\psi_i}ME\ket{\psi_j}=-\bra{\psi_i}E\ket{\psi_j}=0.$$
With $E=E_a^\dagger E_b=\pm E_aE_b$, this gives the orthogonality condition and, since diagonal terms vanish too, the structure condition. Hence if $E_a^\dagger E_b$ anticommutes with some element of $S$ for all errors in a set, the code corrects that set.

<a id="pdf-e658890bd7ef-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
For the trivial case $E=I$ (which commutes with everything), note $I\in S$. More generally for $E\in S$,
$$\bra{\psi_i}E\ket{\psi_j}=\langle\psi_i|\psi_j\rangle=\delta_{ij},$$
satisfying the error-correction condition.

<a id="pdf-e658890bd7ef-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
**Centralizer/normalizer.** $C(S)$ is the set of elements of $\mathcal G$ commuting with all of $S$; $N(S)$ is the set fixing $S$ under conjugation. For $A\in\mathcal G$, $M\in S$: $A^\dagger MA=\pm A^\dagger AM=\pm M$, and since $-1\notin S$, $A\in N(S)\iff A\in C(S)$, so $N(S)=C(S)$. Also $S\subseteq N(S)$ and $S$ is a normal subgroup of $N(S)$. $N(S)$ has $4\cdot2^{n+k}$ elements (factor 4 from overall phase), often disregarded.

<a id="pdf-e658890bd7ef-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.95 -->
If $E\in N(S)-S$ then for $M\in S$, $\ket\psi\in T$: $ME\ket\psi=EM\ket\psi=E\ket\psi$, so $E\ket\psi\in T$; $E$ moves states within $T$. Since $E\notin S$ some state is not fixed, so (unless $E$ differs from an $S$-element by phase) $E$ is undetectable.

<a id="pdf-e658890bd7ef-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.95 -->
**Detection/correction criteria.** A stabilizer code detects all errors $E\in S\cup(\mathcal G-N(S))$. It corrects a set $\{E_i\}$ iff $E_aE_b\in S\cup(\mathcal G-N(S))$ for all $E_a,E_b$. The code has distance $d$ iff $N(S)-S$ contains no element of weight $<d$. If $S$ contains a non-identity element of weight $<d$ the code is *degenerate*, else *nondegenerate*; the nine-qubit code is degenerate ($Z_1Z_2\in S$, distance three). A nondegenerate code satisfies
$$\bra{\psi_i}E_a^\dagger E_b\ket{\psi_j}=\delta_{ab}\delta_{ij}.$$
By convention an $[n,0,d]$ code is nondegenerate. Errors with $E_aE_b\in S$ are *degenerate* (indistinguishable but with identical action).

<a id="pdf-e658890bd7ef-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.95 -->
**Error syndrome.** Define $f_M:\mathcal G\to\mathbf Z_2$ by $f_M(E)=0$ if $[M,E]=0$ and $1$ if $\{M,E\}=0$, and $f(E)=(f_{M_1}(E),\dots,f_{M_{n-k}}(E))$ over the generators. Then $f(E)$ is an $(n-k)$-bit number, $=0$ iff $E\in N(S)$, with $f(E_a)=f(E_b)\iff f(E_aE_b)=0$; for a nondegenerate code $f(E)$ is distinct for each correctable error.

<a id="pdf-e658890bd7ef-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.94 -->
Correction proceeds by measuring each generator's eigenvalue, which equals $(-1)^{f_{M_i}(E)}$, yielding the syndrome; this identifies the error (nondegenerate) or degenerate set (degenerate). The error lies in the unitary, invertible group $\mathcal G$, so applying the error operator (or an $S$-equivalent) restores the state. Syndrome measurement projects any linear-combination error onto a basis error. Fault-tolerant syndrome measurement is deferred to the fault-tolerant chapter.

<a id="pdf-e658890bd7ef-p005-b008"></a>
<!-- pdf-source: page=5; block=8; confidence=0.95 -->
**Encoded operators.** Elements of $N(S)$ permute codewords within $T$; since $S$ fixes $T$, only $N(S)/S$ acts nontrivially. Choosing a $T$-basis of eigenvectors of $n$ commuting $N(S)$ elements gives an automorphism $N(S)/S\to\mathcal G_k$. Thus $N(S)/S$ is generated by $i$ and $2k$ classes $\overline X_i,\overline Z_i$ ($i=1\dots k$) mapping to $X_i,Z_i$ in $\mathcal G_k$ (for $k=1$: $\overline X,\overline Z$). They satisfy
$$[\overline X_i,\overline X_j]=0,\quad [\overline Z_i,\overline Z_j]=0,\quad [\overline X_i,\overline Z_j]=0\ (i\ne j),\quad \{\overline X_i,\overline Z_i\}=0.$$

<a id="pdf-e658890bd7ef-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.98 -->
## Some Examples

<a id="pdf-e658890bd7ef-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.96 -->
**Five-qubit code** (one qubit in five), stabilizer generators plus encoded operators:

| | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
|$M_1$|X|Z|Z|X|I|
|$M_2$|I|X|Z|Z|X|
|$M_3$|X|I|X|Z|Z|
|$M_4$|Z|X|I|X|Z|
|$\overline X$|X|X|X|X|X|
|$\overline Z$|Z|Z|Z|Z|Z|

$M_1,\dots,M_4$ with $\overline X,\overline Z$ generate $N(S)$. The code is *cyclic* (stabilizer and codewords invariant under cyclic qubit permutation), has distance three (e.g. $Y_1Z_2Y_3\in N(S)-S$), and is nondegenerate.

<a id="pdf-e658890bd7ef-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.94 -->
Basis codewords:
$$\ket{\overline0}=\sum_{M\in S}M\ket{00000},\qquad \ket{\overline1}=\overline X\ket{\overline0}.$$
Explicitly,
$$\ket{\overline0}=\ket{00000}+\ket{10010}+\ket{01001}+\ket{10100}+\ket{01010}-\ket{11011}-\ket{00110}-\ket{11000}-\ket{11101}-\ket{00011}-\ket{11110}-\ket{01111}-\ket{10001}-\ket{01100}-\ket{10111}+\ket{00101},$$
$$\ket{\overline1}=\ket{11111}+\ket{01101}+\ket{10110}+\ket{01011}+\ket{10101}-\ket{00100}-\ket{11001}-\ket{00111}-\ket{00010}-\ket{11100}-\ket{00001}-\ket{10000}-\ket{01110}-\ket{10011}-\ket{01000}+\ket{11010}.$$
Multiplying by $S$ merely reorders the sum, so both lie in $T$; $\overline X,\overline Z$ are the encoded $X,Z$. Every single-qubit error uses a distinct syndrome, so the code is *perfect*.

<a id="pdf-e658890bd7ef-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
**Eight-qubit code** (three qubits in eight), generators and encoded operators:

| | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
|$M_1$|X|X|X|X|X|X|X|X|
|$M_2$|Z|Z|Z|Z|Z|Z|Z|Z|
|$M_3$|I|X|I|X|Y|Z|Y|Z|
|$M_4$|I|X|Z|Y|I|X|Z|Y|
|$M_5$|I|Y|X|Z|X|Z|I|Y|
|$\overline X_1$|X|X|I|I|I|Z|I|Z|
|$\overline X_2$|X|I|X|Z|I|I|Z|I|
|$\overline X_3$|X|I|I|Z|X|Z|I|I|
|$\overline Z_1$|I|Z|I|Z|I|Z|I|Z|
|$\overline Z_2$|I|I|Z|Z|I|I|Z|Z|
|$\overline Z_3$|I|I|I|I|Z|Z|Z|Z|

$M_1,\dots,M_5$ generate $S$ and, with $\overline X_i,\overline Z_i$, generate $N(S)$; nondegenerate, distance three. Codewords:
$$\ket{\overline{c_1c_2c_3}}=\overline X_1^{c_1}\overline X_2^{c_2}\overline X_3^{c_3}\sum_{M\in S}M\ket{00000000}.$$
The $\overline X_i,\overline Z_i$ are the encoded $X,Z$ on the $i$th encoded qubit; part of an infinite code family.

<a id="pdf-e658890bd7ef-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.94 -->
**CSS (Calderbank–Shor–Steane) codes.** From a classical code with parity-check matrix $P$, build stabilizer generators with $Z$ where $P$ has a $1$ and $I$ elsewhere; then $f(E)$ for an $X$-error product equals the classical syndrome for the corresponding bit-flip errors. Adding generators from a second parity-check matrix $Q$ using $X$'s identifies $Z$ errors; together they identify $Y$ errors (nontrivial in both parts). Such a code corrects as many $X$ errors as $P$'s code and as many $Z$ errors as $Q$'s code (a $Y$ counts as one of each). The two parts combine in CSS form iff the generators commute, i.e. iff rows of $P$ and $Q$ are orthogonal under the binary dot product (each code's dual is a subcode of the other). The quantum minimum distance is $\min$ of the two classical distances.

<a id="pdf-e658890bd7ef-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.95 -->
**Seven-qubit CSS code**, based on the self-dual classical $[7,4,3]$ Hamming code:

| | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
|$M_1$|X|X|X|X|I|I|I|
|$M_2$|X|X|I|I|X|X|I|
|$M_3$|X|I|X|I|X|I|X|
|$M_4$|Z|Z|Z|Z|I|I|I|
|$M_5$|Z|Z|I|I|Z|Z|I|
|$M_6$|Z|I|Z|I|Z|I|Z|
|$\overline X$|I|I|I|I|X|X|X|
|$\overline Z$|I|I|I|I|Z|Z|Z|

Codewords:
$$\ket{\overline0}=\ket{0000000}+\ket{1111000}+\ket{1100110}+\ket{1010101}+\ket{0011110}+\ket{0101101}+\ket{0110011}+\ket{1001011},$$
$$\ket{\overline1}=\ket{0000111}+\ket{1111111}+\ket{1100001}+\ket{1010010}+\ket{0011001}+\ket{0101010}+\ket{0110100}+\ket{1001100}.$$
$\ket{\overline0}$ superposes even Hamming codewords, $\ket{\overline1}$ the odd ones — characteristic of CSS codes (codewords are superpositions of subcode words of a classical code).

<a id="pdf-e658890bd7ef-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.90 -->
CSS codes are less efficient than general quantum codes but are easily derived from classical codes; the seven-qubit code is well suited to fault-tolerant computation.

<a id="pdf-e658890bd7ef-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.97 -->
**Section — Alternate Languages for Stabilizers.** Several equivalent descriptions of a stabilizer exist (finite-group, binary vector space, GF(4)), each useful in different settings.

<a id="pdf-e658890bd7ef-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->
**Binary formalism.** Write the stabilizer as a pair of $(n-k)\times n$ binary matrices (or one $(n-k)\times 2n$ matrix $(A\,|\,B)$); rows index generators, columns index qubits. Left matrix has a $1$ where the generator has $X$ or $Y$; right matrix has a $1$ where it has $Y$ or $Z$. Overall phases are dropped. Example — five-qubit code:
$$\left(\begin{array}{ccccc|ccccc}1&0&0&1&0&0&1&1&0&0\\0&1&0&0&1&0&0&1&1&0\\1&0&1&0&0&0&0&0&1&1\\0&1&0&1&0&1&0&0&0&1\end{array}\right).$$
Convert back: $X$ where left is $1$, $Z$ where right is $1$, $Y$ where both are $1$; generators formed this way carry no overall phase. Group multiplication corresponds to binary vector addition.

<a id="pdf-e658890bd7ef-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.96 -->
**Commutation conditions (binary).** Two operators $(a|b)$, $(c|d)$ commute iff
$$Q(a|b,c|d)=\sum_{i=1}^n (a_i d_i + b_i c_i)=0 \tag{eq-commute-bin}$$
(binary arithmetic). The stabilizer $(A|B)$ is Abelian iff
$$\sum_{l=1}^n (A_{il}B_{jl}+B_{il}A_{jl})=0.$$
$N(S)$ is found by testing (eq-commute-bin) against the rows of $(A|B)$. A real code (even number of $Y$'s) additionally satisfies
$$\sum_{l=1}^n A_{il}B_{il}=0.$$

<a id="pdf-e658890bd7ef-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.95 -->
**GF(4) formalism.** Represent generators as $n$-dimensional vectors over $\mathrm{GF}(4)=\{0,1,\omega,\omega^2\}$ (characteristic two): $1+1=\omega+\omega=\omega^2+\omega^2=0$, $\omega^3=1$, $1+\omega=\omega^2$. Substitute $1\to X$, $\omega\to Z$, $\omega^2\to Y$; the multiplicative structure of $\mathcal G$ becomes GF(4) addition. If the stabilizer is closed under multiplication by $\omega$ the code is **linear** (a classical GF(4) code); otherwise it is **additive**. The five-qubit code (linear) is
$$\left(\begin{array}{ccccc}1&\omega&\omega&1&0\\0&1&\omega&\omega&1\\1&0&1&\omega&\omega\\\omega&1&0&1&\omega\end{array}\right).$$
Define the trace $\mathrm{Tr}\,\omega=\mathrm{Tr}\,\omega^2=1$, $\mathrm{Tr}\,1=\mathrm{Tr}\,0=0$. Two operators with GF(4) images $u,v$ commute iff
$$\mathrm{Tr}(u\cdot\overline v)=\mathrm{Tr}\Big(\sum_{j=1}^n u_j\overline v_j\Big)=0,$$
where $\overline{v}_j$ conjugates the $j$th component (swap $\omega\leftrightarrow\omega^2$, fix $0,1$).

<a id="pdf-e658890bd7ef-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.96 -->
**Section — Making New Codes From Old Codes.** Simple modifications of existing codes yield new codes with different parameters.

<a id="pdf-e658890bd7ef-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.93 -->
**Construction (permute / add qubit).** Permuting $X,Y,Z$ on each qubit preserves distance and size. Adding a new qubit with a new generator equal to $X$ on it (tensoring existing generators with $I$) turns an $[n,k,d]$ code into an $[n+1,k,d]$ degenerate code: any operator acting as $Y$ or $Z$ on the new qubit anticommutes with the new generator, and $M\otimes X^{(n+1)}\equiv M\otimes I$, so a member of $N(S)-S$ must have weight $\ge d$ on the first $n$ qubits.

<a id="pdf-e658890bd7ef-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.94 -->
**Construction (remove last qubit).** Convert an $[n,k,d]$ code into an $[n-1,k+1,d-1]$ code. Choose the $n-k$ generators so $M_1$ ends in $X$, $M_2$ ends in $Z$, and $M_3,\dots,M_{n-k}$ end in $I$ (possible when $d>1$). The new stabilizer is generated by $M_3,\dots,M_{n-k}$ (drop $M_1,M_2$) on the first $n-1$ qubits. For an operator $A$ of weight $w$ on the first $n-1$ qubits commuting with $M_3,\dots,M_{n-k}$, four cases each give a weight-$\le w+1$ operator commuting with the original stabilizer: (1) $A$ commutes with $M_1,M_2$; (2) commutes with $M_1$ not $M_2$ → $A\otimes X_n$; (3) commutes with $M_2$ not $M_1$ → $A\otimes Z_n$; (4) anticommutes with both → $A\otimes Y_n$. Hence $w\ge d-1$, giving distance $d-1$; the $n-k-2$ generators encode $k+1$ qubits, and new $\overline X,\overline Z$ are $M_1,M_2$ restricted to the first $n-1$ qubits.

<a id="pdf-e658890bd7ef-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.90 -->
**Example.** Removing the last qubit of the $[5,1,3]$ code gives a $[4,2,2]$ code with generators $M_1$ and $M_3M_4$ (last qubit dropped); $\overline Z_1=M_3\overline Z$ is used so $\overline Z_1$ anticommutes with $\overline X_1$. Stabilizer (Table, fig-droplast): $M_1'=XZZX$, $M_2'=YXXY$; $\overline X_1=XXXX$, $\overline X_2=XIXZ$, $\overline Z_1=YZYI$, $\overline Z_2=IXZZ$.

<a id="pdf-e658890bd7ef-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.93 -->
**Construction (pasting).** Given stabilizers $R_1\subset S_1$, $R_2\subset S_2$ with $R_1$ an $[n_1,l_1,c_1]$, $R_2$ an $[n_2,l_2,c_2]$, $S_1$ an $[n_1,k_1,d_1]$, $S_2$ an $[n_2,k_2,d_2]$ code (so $k_i<l_i$, $c_i\le d_i$). Require $l_1-k_1=l_2-k_2$ and $S_1,S_2$ nondegenerate. With generators $R_1=\{M_1,\dots,M_{n_1-l_1}\}$, $S_1=\{M_1,\dots,M_{n_1-k_1}\}$, $R_2=\{N_1,\dots,N_{n_2-l_2}\}$, $S_2=\{N_1,\dots,N_{n_2-k_2}\}$, the new stabilizer $S$ on $n_1+n_2$ qubits is generated by
$$\{M_1\otimes I,\dots,M_{n_1-l_1}\otimes I,\;I\otimes N_1,\dots,I\otimes N_{n_2-l_2},\;M_{n_1-l_1+1}\otimes N_{n_2-l_2+1},\dots,M_{n_1-k_1}\otimes N_{n_2-k_2}\}.$$
It has $(n_1-l_1)+(n_2-l_2)+(l_i-k_i)$ generators and encodes $l_1+k_2=l_2+k_1$ qubits.

<a id="pdf-e658890bd7ef-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.88 -->
**Example.** Pasting the eight-qubit code ($S_1$, with $R_1=\{X^{\otimes 8},Z^{\otimes 8}\}$) and the five-qubit code ($S_2$, $R_2=XZZXI$) yields the $[13,7,3]$ code (Table, table-13qubit).

<a id="pdf-e658890bd7ef-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
**Distance (pasting).** The pasted code has distance $\min\{d_1,d_2,c_1+c_2\}$: an operator on only the first $n_1$ qubits must commute with $S_1$, one on only the last $n_2$ with $S_2$, and one on both parts must commute with $R_1\otimes I$ and $I\otimes R_2$.

<a id="pdf-e658890bd7ef-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.92 -->
**Construction (concatenation).** Encode each of the $n_1$ qubits of an $[n_1,k,d_1]$ code (stabilizer $S_1$) again with an $[n_2,1,d_2]$ code (stabilizer $S_2$), giving an $[n_1 n_2,k,d_1 d_2]$ code. Its stabilizer $S$ is $n_1$ copies of $S_2$ (on blocks of $n_2$ physical qubits) plus $n_1-k$ generators from $S_1$, with each $X$ of $S_1$ replaced by the encoded $\overline X$ of $S_2$.

<a id="pdf-e658890bd7ef-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.88 -->
**Example.** Concatenating the five-qubit code with itself gives the 25-qubit stabilizer of Table (table-25qubit).

<a id="pdf-e658890bd7ef-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.90 -->
**Distance (concatenation).** The concatenated code has distance $d_1 d_2$ because operators in $N(S)-S$ must have weight $\ge d_2$ on at least $d_1$ blocks of $n_2$ qubits, hence weight $\ge d_1 d_2$. The same code need not be used for every qubit of $S_1$.

<a id="pdf-e658890bd7ef-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.91 -->
**Concatenation, multi-qubit $S_2$ (way 1).** For $S_1=[n_1,k_1,d_1]$, $S_2=[n_2,k_2,d_2]$ with $n_1$ a multiple of $k_2$, encode blocks of $S_1$ of size $k_2$ using $S_2$, giving a code on $n_1 n_2/k_2$ qubits encoding $k_1$ qubits. A distance-$d_2$ error on an $n_2$-block can cause up to $k_2$ errors in $S_1$, so distance is at least $\lceil d_1/k_2\rceil d_2$. If $S_1$ has block-distance $d_1'$ (with $d_1'\ge\lceil d_1/k_2\rceil$) for blocks of $k_2$ errors, the concatenated code has distance $d_1' d_2$.

<a id="pdf-e658890bd7ef-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.91 -->
**Concatenation, multi-qubit $S_2$ (way 2).** Encode $k_2$ copies of $S_1$, placing the $i$th qubit of each copy in the same $S_2$ block. Since any $S_2$-block failure gives one error per $S_1$ block, this yields an $[n_1 n_2,k_1 k_2,d_1 d_2]$ code.

<a id="pdf-e658890bd7ef-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->
**Section — Higher Dimensional States.** Generalizing stabilizer codes to tensor products of $d$-dimensional systems (qudits, $d>2$).

<a id="pdf-e658890bd7ef-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.90 -->
**Motivation.** Physical implementations may use $d$-level systems; the fundamental unit is a **qudit**, and the stabilizer formalism must be modified for the extra dimensions.

<a id="pdf-e658890bd7ef-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.00 -->
**Definition (nice error basis).** A set of $d^2$ single-qudit unitaries $E_1,\dots,E_{d^2}$ (including identity) forming a basis of all $d\times d$ complex matrices is a **nice error basis** if $E_i E_j = w_{ij} E_{i*j}$ for all $i,j$, where $*$ is a binary group operation; then $|w_{ij}|=1$. The group $\mathcal G_n$ is the tensor product of $n$ copies with phases generated by the $w_{ij}$. An Abelian subgroup $S\le\mathcal G_n$ containing no nontrivial phase times identity has a nontrivial code $T$ = the common $+1$ eigenspace of $S$. $T$ detects any error $E$ with $EM=cME$ for some $M\in\mathcal G_n$, $c\ne 1$.

<a id="pdf-e658890bd7ef-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.90 -->
**Remark (encoded dimension).** With $n-k$ generators, $T$ need not encode $k$ qudits; this occurs only when $d$ is composite and a generator's order is a nontrivial factor of $d$. If $S$ has $r$ elements, $\dim T = d^n/r$. If all generators have order $d$, then $T$ encodes $k$ qudits.

<a id="pdf-e658890bd7ef-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.00 -->
**Example (error basis).** For any $d$, generate a nice error basis from $D_\omega$ and $C_n$ with $(D_\omega)_{ij}=\delta_{ij}\omega^i$ and $(C_n)_{ij}=\delta_{j,(i+1\bmod n)}$, $\omega$ a primitive root of unity. For $d=2$: $C_2=X$, $D_{-1}=Z$. Generally $D_\omega:\ket i\to\omega^i\ket i$ and $C_n$ adds one mod $n$, with
$$C_n D_\omega=\omega D_\omega C_n.$$
Basis elements are $C_n^a D_\omega^b$, satisfying
$$(C_n^a D_\omega^b)(C_n^c D_\omega^d)=\omega^{ad-bc}(C_n^c D_\omega^d)(C_n^a D_\omega^b).$$

<a id="pdf-e658890bd7ef-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.85 -->
**Remark.** Higher-dimensional codes are less studied; some constructions are cited (Knill; Chau; Aharonov; Rains).

<a id="pdf-e658890bd7ef-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.98 -->
**Chapter — Bounds on Quantum Error-Correcting Codes.** **Section: General Bounds.**

<a id="pdf-e658890bd7ef-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->
Efficiency of error-correcting codes (in encoded qubits vs. distance) is important classically and quantumly; only upper/lower bounds are known for minimum-distance codes, true bounds unknown. Asymptotic efficiency is better understood: classically Shannon's theorem gives channel capacity. No real quantum analogue of Shannon's theorem is known despite extensive work.

<a id="pdf-e658890bd7ef-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->
**Quantum Hamming bound.** For a nondegenerate code on $n$ qubits with basis codewords $|\psi_i\rangle$ and errors $E_a$, all states $E_a|\psi_i\rangle$ are linearly independent, so (#errors)$\times$(#codewords) $\le 2^n$. For a code correcting all errors of weight $\le t$ and encoding $k$ qubits:
$$\sum_{j=0}^{t} 3^j \binom{n}{j} 2^k \le 2^n. \quad (\text{eq-QHB-finite})$$
Here $\binom{n}{j}$ counts choices of $j$ affected qubits and $3^j$ counts tensor products of $X,Y,Z$. Analogous to the classical Hamming bound but with the extra $3^j$ factor and valid only for nondegenerate codes. Whether degenerate codes can exceed (eq-QHB-finite) is unknown.

<a id="pdf-e658890bd7ef-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.94 -->
For a depolarizing channel with probability $p$ of an $X,Y,$ or $Z$ error per qubit, expected errors $t=np$. The bound becomes $3^{np}\binom{n}{np}2^k \le 2^n$, giving
$$\frac{k}{n} \le 1 - p\log_2 3 - H(p), \quad (\text{eq-QHB})$$
with $H(x)=-x\log_2 x-(1-x)\log_2(1-x)$. Achievable via random codes, but not always the most efficient use of the channel, so (eq-QHB) is not the true quantum channel capacity.

<a id="pdf-e658890bd7ef-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.93 -->
**Quantum Gilbert-Varshamov bound.** From $\langle\psi_i|E_a^\dagger E_b|\psi_j\rangle = C_{ab}\delta_{ij}$, treat $C_{ab}$ as a function of operators $O=E_a^\dagger E_b$ of weight $<d$ (for distance $d$). Then $\langle\psi|E_a^\dagger E_b|\psi\rangle=C_{ab}$ (eq-Cab) imposes $N=\sum_{j=0}^{d-1}3^j\binom{n}{j}$ constraints on $|\psi\rangle$. Iteratively choose $|\psi_i\rangle$ orthogonal to all $O|\psi_j\rangle$ ($j\le i-1$) satisfying (eq-Cab); this continues while $\sum_{j=0}^{d-1}3^j\binom{n}{j}\,i < 2^n$. Hence a distance-$d$ code encoding $k$ in $n$ qubits exists with
$$\sum_{j=0}^{d-1}3^j\binom{n}{j}2^k \ge 2^n. \quad (\text{eq-QGV})$$
In the limit $t=pn=d/2$, $n$ large: $\frac{k}{n} \ge 1 - 2p\log_2 3 - H(2p).$

<a id="pdf-e658890bd7ef-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->
**Knill-Laflamme bound.** For an $[n,k,d]$ code, remove any $d-1$ qubits; the remaining $n-d+1$ qubits must reconstruct the $2^k$ codewords and the state of the missing (maximum-entropy) qubits, giving
$$n-d+1 \ge d-1+k, \qquad n \ge 2(d-1)+k.$$
This is a quantum analog of the classical Singleton bound, holding for degenerate and nondegenerate codes. A $t$-error-correcting code has $d=2t+1$, so $n\ge 4t+k$; hence the smallest one-error-correcting quantum code uses five qubits.

<a id="pdf-e658890bd7ef-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
**Section: Weight Enumerators and Linear Programming Bounds.** Classically, codeword weight distributions encoded as *weight enumerator* polynomials, with algebraic relations between them, bound codes; these ideas adapt to quantum codes.

<a id="pdf-e658890bd7ef-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.96 -->
**Definition (weight enumerators).** Let $A_d$ = number of weight-$d$ elements of the stabilizer $S$ and $B_d$ = number of weight-$d$ elements of $N(S)$ (ignoring phases); $B_d\ge A_d\ge 0$. Define $A(z)=\sum_{d=0}^n A_d z^d$, $B(z)=\sum_{d=0}^n B_d z^d$. Always $A_0=B_0=1$. For a distance-$d$ code, $B_{d'}=A_{d'}$ for $d'<d$; nondegenerate: $B_{d'}=A_{d'}=0$ for $d'<d$; degenerate: $B_{d'}=A_{d'}>0$ for some $d'<d$.

<a id="pdf-e658890bd7ef-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.95 -->
**Quantum MacWilliams identity.**
$$B(z) = \frac{1}{2^{n-k}}(1+3z)^n A\!\left(\frac{1-z}{1+3z}\right). \quad (\text{eq-QMW})$$
Equivalently $\sum_d B_d z^d = \frac{1}{2^{n-k}}\sum_d A_d (1-z)^d(1+3z)^{n-d}$, and matching coefficients of $z^d$:
$$B_d = \frac{1}{2^{n-k}}\sum_{d'=0}^n\left[\sum_{s=0}^d (-1)^s 3^{d-s}\binom{d'}{s}\binom{n-d'}{d-s}\right]A_{d'}.$$

<a id="pdf-e658890bd7ef-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.94 -->
**Proof.** An operator $E\in G$ of weight $d$ commutes with every $M\in S$ or with exactly half, so $\sum_{M\in S}(-1)^{f_M(E)}=0$ if $E\notin N(S)$ and $=2^{n-k}$ if $E\in N(S)$ ($f_M(E)=0/1$ for commute/anticommute). Thus $B_d=\frac{1}{2^{n-k}}\sum_E\sum_{M\in S}(-1)^{f_M(E)}$ over weight-$d$ $E$. Split the $M$-sum by weight $d'$: $B_d=\frac{1}{2^{n-k}}\sum_{d'}\sum_M\sum_E(-1)^{f_M(E)}$. A given $M,E$ act nontrivially on $s$ common qubits, as different Paulis on $t$ of them and the same on $s-t$, with $(-1)^{f_M(E)}=(-1)^t$. The count of $E$ agreeing on $s-t$ and disagreeing on $t$ qubits is $2^t 3^{d-s}\binom{s}{t}\binom{d'}{s}\binom{n-d'}{d-s}$, independent of $M$. Summing $\sum_t (-2)^t\binom{s}{t}=(1-2)^s=(-1)^s$ yields
$$B_d=\frac{1}{2^{n-k}}\sum_{d'=0}^n\left[\sum_{s=0}^d(-1)^s 3^{d-s}\binom{d'}{s}\binom{n-d'}{d-s}\right]A_{d'}. \qquad\square$$

<a id="pdf-e658890bd7ef-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.95 -->
The identity (eq-QMW) also holds for non-stabilizer codes, so bounds from it apply to all quantum codes. For a distance-$d$ code the coefficients satisfy: $B_0=A_0=1$; $B_{d'}=A_{d'}$ for $d'<d$; $B_{d'}\ge A_{d'}\ge 0$ for all $d'$; nondegenerate $\Rightarrow A_{d'}=B_{d'}=0$ for $d'<d$. These linear constraints plus (eq-QMW) are solvable by linear programming; no integer solution $\Rightarrow$ no $[n,k,d]$ code. Example: for $[5,1,3]$ the unique solution is $A_i=(1,0,0,0,15,0)$, $B_i=(1,0,0,30,15,18)$, so the usual five-qubit code is essentially the only $[5,1,3]$ code and there are no degenerate five-qubit codes.

<a id="pdf-e658890bd7ef-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->
**Definition (shadow enumerator).** The *shadow* $Sh(S)$ of code $S$ is $\{E\in G : f_M(E)\equiv \mathrm{wt}(M)\pmod 2\ \forall M\in S\}$. Let $S_d$ = number of weight-$d$ elements of $Sh(S)$ (ignoring phases) and $S(z)=\sum_{d=0}^n S_d z^d$. Then
$$S(z)=\frac{1}{2^{n-k}}(1+3z)^n A\!\left(\frac{z-1}{1+3z}\right). \quad (\text{eq-shadow})$$

<a id="pdf-e658890bd7ef-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.93 -->
**Proof.** If $S$ has only even-weight operators, $E\in Sh(S)$ iff $f_M(E)=0\ \forall M$, so $Sh(S)=N(S)$ and $S_d=B_d$; since $A(z)$ is then even, (eq-shadow) follows from (eq-QMW). If $S$ has an odd-weight element, the even-weight subset $S'\subset S$ has $2^{n-k-1}$ elements (commuting $M,M'$ overlap and disagree on an even number of qubits, so $\mathrm{wt}(MM')\equiv\mathrm{wt}(M)+\mathrm{wt}(M')\pmod 2$), and $Sh(S)=N(S')-N(S)$. With enumerators $B'(z),A'(z)$ of $S',N(S')$:
$$S(z)=B'(z)-B(z)=\frac{1}{2^{n-k}}(1+3z)^n\left[2A'\!\left(\tfrac{1-z}{1+3z}\right)-A\!\left(\tfrac{1-z}{1+3z}\right)\right].$$
Since $A'_d=A_d$ (even $d$), $0$ (odd $d$), $A(z)+A(-z)=2A'(z)$, giving $S(z)=\frac{1}{2^{n-k}}(1+3z)^n A\!\left(\frac{z-1}{1+3z}\right)$. $\square$

<a id="pdf-e658890bd7ef-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.94 -->
The shadow enumerator is also defined for non-stabilizer codes and satisfies (eq-shadow); with $S_d\ge 0$ this adds constraints to the linear programming bound for any code. Applied to all codes with $n\le 30$: the smallest distance-5 code is an $[11,1,5]$ code, and degenerate codes in this region all fall below the quantum Hamming bound. The shadow enumerator also shows any nondegenerate code on $n$ qubits corrects at most $\lfloor(n+1)/6\rfloor$ errors.

<a id="pdf-e658890bd7ef-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.94 -->
**Section: Bounds on Degenerate Stabilizer Codes.** Whether any degenerate code exceeds the quantum Hamming bound is unknown in general; for restricted cases it is shown not to. For $n<30$ the LP bounds show it; this section proves it for all stabilizer codes correcting one or two errors.

<a id="pdf-e658890bd7ef-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.92 -->
**Claim/Proof (distance three).** For a one-error-correcting degenerate code, $S$ contains weight-1 or weight-2 operators. A weight-1 operator eliminates its qubit ($[n,k,d]\to[n-1,k,d]$). Suppose $l$ independent weight-2 operators $M_1,\dots,M_l$ generate $D$; then $S-D$ has no operator of weight $<3$. The subspace fixed by $D$ has dimension $2^{n-l}$. If no operator in $D$ acts on qubit $j$, then $X_j,Y_j,Z_j\in N(D)$ are nondegenerate and produce orthogonal states per codeword. At least $n-2l$ qubits are unaffected by $D$ (each generator adds $\le 2$ qubits), so
$$[1+3(n-2l)]2^k \le 2^{n-l}, \qquad k \le n-l-\log_2[1+3(n-2l)]. \quad (\text{eq-QHB-deg1})$$
Since the quantum Hamming bound is $k\le n-\log_2(1+3n)$, (eq-QHB-deg1) is more restrictive when
$$l+\log_2[1+3(n-2l)] \ge \log_2(1+3n),\ \text{i.e.}\ l \ge \log_2\!\left[1+\tfrac{6l}{1+3(n-2l)}\right]. \quad (\text{eq-QHB-deg1'})$$
Assuming $n\ge 2l$, this holds if $l\ge\log_2(1+6l)$, true for $l\ge 5$; $l=4$ needs $n\ge 9$, $l=3$ needs $n\ge 7$, $l=2$ needs $n\ge 5$, $l=1$ needs $n\ge 4$. Remaining $n\ge 2l$ cases are ruled out by the LP bounds. If $l>n/2$ then $k\le n-l\le n/2$, and for $n\ge 13$ the quantum Hamming bound is less restrictive. Hence, with the LP bounds, no distance-three degenerate stabilizer code exceeds the quantum Hamming bound. $\square$

<a id="pdf-e658890bd7ef-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.93 -->
**Proof (two-error case, continued).** Let $D$ be generated by the weight-$\le 4$ operators of $S$; at least $n-4l$ qubits are unaffected by $D$, and all weight-1,2 errors on them give orthogonal states, so
$$[1 + 3(n-4l) + \tfrac{9}{2}(n-4l)(n-4l-1)]\,2^k \le 2^{n-l},$$
$$[1 - \tfrac{3}{2}n + \tfrac{9}{2}n^2 + 6l(1+12l-6n)]\,2^l \le 2^{n-k}.$$
The quantum Hamming bound (QHB) still holds if
$$[1 - \tfrac{3}{2}n + \tfrac{9}{2}n^2 + 6l(1+12l-6n)]\,2^l \ge 1 - \tfrac{3}{2}n + \tfrac{9}{2}n^2,$$
i.e. $\left[1 - \dfrac{6l(6n-12l-1)}{1-3n/2+9n^2/2}\right]2^l \ge 1$ (eq-QHB-deg2). Since $l(6n-12l-1)$ is maximized at $l=(6n-1)/24$, (eq-QHB-deg2) holds when $\left[1-\dfrac{(6n-1)^2}{8-12n+36n^2}\right]2^l\ge1$, i.e. $\dfrac{7}{8-12n+36n^2}\,2^l\ge1$, i.e. $7\cdot2^{l-2}\ge 9n^2-3n+2$. If this fails then $l \le 2-\log_2 7 + \log_2(9n^2-3n+2) \le 3+2\log_2 n$, whence $l(6n-12l-1)\le 6nl\le 6n(3+2\log_2 n)$ and (eq-QHB-deg2) holds when $\left[1-\dfrac{6n(3+2\log_2 n)}{1-3n/2+9n^2/2}\right]2^l\ge1$. For $n\ge30$ that fraction $\le0.58$, so (eq-QHB-deg2) holds for all $1<l\le n/4$. For $l=1$ it becomes $1-\dfrac{6(6n-13)}{1-3n/2+9n^2/2}\ge1/2$; for $n\ge30$ the fraction $\le0.26$, so it holds for $l=1$ as well.

<a id="pdf-e658890bd7ef-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.94 -->
**Proof (continued, $l>n/4$).** Only $l>n/4$ remains, giving $k\le n-l<3n/4$, at least as restrictive as the QHB for $n\ge52$; for $n=31$ the QHB gives $k\le n-13$. So for $31\le n\le51$ the code needs $l\le n/4+5$ to violate the QHB, and the only case with $l>n/4+4$ is $l=12,\,n=31$. Assuming $l\le n/4+4$: at least $n-16$ qubits are affected by at most one generator of $D$; being $>l+3$, either two generators each affect two qubits fixed by all others, or one generator fixes four such qubits (the latter more restrictive, so assume the former). Taking WLOG the two generators to be $M_{l-1},M_l$, errors on the four qubits they alone affect keep codewords in the subspace fixed by $D'=\langle M_1,\dots,M_{l-2}\rangle$. With 67 weight-0,1,2 errors on four qubits, $67\cdot2^k\le2^{\,n-(l-2)}$, so $k\le n-l-5$, at least as restrictive as the QHB for $31\le n\le51$.

<a id="pdf-e658890bd7ef-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->
**Proof (case $l=12,\,n=31$; conclusion).** Here at least fourteen qubits are affected by at most one generator of $D$, again allowing two generators that jointly act on four qubits unaffected by the others, giving $k\le n-l-5$, more restrictive than the QHB. Therefore no two-error-correcting degenerate stabilizer code exceeds the quantum Hamming bound. $\square$

<a id="pdf-e658890bd7ef-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.90 -->
Remark: the method might extend to $t\ge3$ errors but grows harder — the cases $l>n/(2t)$ need special treatment and the range of $n$ that could violate the QHB grows rapidly with $t$; a sufficiently degenerate code may eventually violate it.

<a id="pdf-e658890bd7ef-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.00 -->
A less restrictive bound on degenerate stabilizer codes follows from constructing a classical code from the quantum code [cleve-classical]. Put the code in standard form (eq-standard-form), noting the $r\times k$ matrix $A_2$; $r\le n-k$, and single-qubit rotations from $N(\mathcal{G})$ can convert one generator to a product of $Z$'s, ensuring $r\le n-k-1$. The classical code $C$ with $k\times(r+k)$ generator matrix $(A_2^T\mid I)$ encodes $k$ bits in at most $n-1$ bits. If the quantum code corrects $t$ quantum errors, $C$ corrects $t$ classical bit-flip errors (whether the quantum code is degenerate or not). Hence an $[n,k,d]$ quantum code implies an $[n-1,k,d]$ classical code exists.

<a id="pdf-e658890bd7ef-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.98 -->
## Error-Correcting Codes and Entanglement Purification Protocols

<a id="pdf-e658890bd7ef-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.93 -->
**Definition (EPP).** Alice prepares EPR pairs and sends one half to Bob; errors leave them sharing imperfect pairs. An *entanglement purification protocol* (EPP) is a set of local operations by Alice and Bob that converts many imperfect pairs into a smaller number of perfect (or better) pairs [bennett-tome, bennett-EPP].

<a id="pdf-e658890bd7ef-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.94 -->
**Definition (1-EPP, 2-EPP).** If both Alice and Bob can communicate classically, their protocols are *two-way* EPPs (2-EPPs); if Bob can only receive (not transmit), they are *one-way* EPPs (1-EPPs). Protocols with no classical communication are equivalent to 1-EPPs. In some circumstances 2-EPPs purify more good pairs than 1-EPPs do [bennett-tome].

<a id="pdf-e658890bd7ef-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.93 -->
**Claim.** 1-EPPs are equivalent to quantum error-correcting codes. From a code: Alice encodes and sends, Bob corrects and decodes; preserved encoded qubits retain entanglement with Alice's, forming good EPR pairs, one per encoded qubit. Conversely, a 1-EPP distilling $k$ good pairs from $n$ noisy pairs yields a code (Alice encoder, Bob decoder): Alice creates $n$ pairs, performs her half of the 1-EPP without waiting (she cannot receive from Bob — why this gives a 1-EPP, not a 2-EPP), sends the needed classical information, then teleports her $k$ protected qubits through her halves of the $k$ good pairs; Bob completes purification and teleportation, giving the correct state — a code encoding $k$ qubits in $n$.

<a id="pdf-e658890bd7ef-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.98 -->
## Capacity of the Erasure Channel

<a id="pdf-e658890bd7ef-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.95 -->
**Definition (erasure channel).** Each transmitted qubit is totally randomized with probability $p$, but the qubit on which this occurs is always known. The capacity for both quantum codes and 2-EPPs is computable [bennett-erasure].

<a id="pdf-e658890bd7ef-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.95 -->
**2-EPP capacity.** Of $n$ pairs sent, $pn$ are destroyed and $(1-p)n$ remain intact; Bob knows which, tells Alice, and they discard the rest, achieving rate $1-p$, which is optimal. Hence the 2-EPP capacity is $1-p$.

<a id="pdf-e658890bd7ef-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.93 -->
**1-EPP / quantum-code upper bound.** Since Bob cannot tell Alice which pairs to keep, the capacity is bounded by $1-2p$. Model the erasure by Charlie stealing each qubit with probability $p$, replacing it randomly, and telling Bob which he stole. At $p=1/2$ Bob and Charlie hold equally many valid pairs, so any purification Alice enables for Bob also works for Charlie; teleporting to Bob then also teleports to Charlie, cloning the state — so the rate is zero for $p>1/2$. For $p<1/2$, if Alice knew $n(1-2p)$ safe pairs, then of the remaining $2pn$ uncertain pairs $pn$ go to Charlie (equal good pairs to Bob); purifying more than $n(1-2p)$ pairs also purifies with Charlie, again cloning. Hence capacity $\le 1-2p$.

<a id="pdf-e658890bd7ef-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.00 -->
**Achievability.** Take a random Abelian subgroup of $\mathcal{G}_n$ with $n-k$ generators as the stabilizer $S$. Sending $k$ encoded qubits through the channel randomizes $pn$ known qubits, giving $4^{pn}$ possible errors (and $4^{pn}$ products); errors are correctable when at least one such product anticommutes with an element of $S$. Each random generator (anti)commutes with half the weight-$pn$ operators, independently, so the number commuting with all $n-k$ generators is
$$4^{pn}/2^{n-k}=2^{k-(1-2p)n}=2^{(r-1+2p)n},\qquad k=rn.$$
For $r<1-2p$ the failure probability $\to0$ as $n\to\infty$, so a random stabilizer code attains rate $1-2p$; matching the upper bound, the erasure-channel capacity is $1-2p$.

<a id="pdf-e658890bd7ef-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.98 -->
## Capacity of the Depolarizing Channel

<a id="pdf-e658890bd7ef-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->
**Definition (depolarizing channel).** With probability $1-p$ a qubit is left alone; with equal probabilities $p/3$ each of $X$, $Y$, $Z$ acts on it. Upper and lower capacity bounds can be found as for the erasure channel, but they do not meet, so the depolarizing-channel capacity is unknown.

<a id="pdf-e658890bd7ef-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.94 -->
**Upper bound (cloning).** Simulate the channel by Charlie stealing each qubit with probability $q$ and replacing it randomly without telling Bob; a $1/4$ chance of matching the state gives a $q/4$ chance for each of $X,Y,Z$, i.e. the depolarizing channel with $p=3q/4$. The cloning argument bounds the capacity by $1-2q=1-8p/3$; for $p>3/8$ the rate is necessarily zero.

<a id="pdf-e658890bd7ef-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.92 -->
**Tighter bound.** Random stealing is not the best eavesdropping: the optimal method lets Charlie reproduce Bob's state whenever $p>1/4$ [fuchs-KL], limiting the rate to $1-4p$ — the asymptotic form of the Knill-Laflamme bound derived for fixed-minimum-distance codes in section (sec-gen-bounds).

<a id="pdf-e658890bd7ef-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.00 -->
**Lower bound (random stabilizer).** Encoding $k$ in $n$ with random $S$, the expected error weight is $pn$; errors $E,F$ are distinguishable iff $E^\dagger F$ anticommutes with some element of $S$. The typical product $E^\dagger F$ has weight below $2pn$: probability $p^2$ that both act nontrivially on a qubit, probability $p^2/3$ as the same Pauli (then cancelling), so its expected weight is $(2p-4p^2/3)n$; set $x=2p-4p^2/3$. With $N(w)$ errors of weight $w$, there are $N(xn)$ products of weight $xn$, of which $N(xn)/2^{n-k}$ commute with $S$; among the $N(pn)$ likely errors there are $\binom{N(pn)}{2}$ pairs, so each weight-$xn$ operator arises $\binom{N(pn)}{2}/N(xn)$ ways, forcing removal of $\binom{N(pn)}{2}/2^{n-k}$ errors. Requiring this $\ll N(pn)$ gives $N(pn)/2^{n-k+1}\ll1$, i.e. $N(pn)\ll2^{n-k+1}$, i.e.
$$k/n < 1-\tfrac{1}{n}\log_2 N(pn)=1-p\log_2 3 - H(p),$$
which is the quantum Hamming bound (eq-QHB): a random code saturates it.

<a id="pdf-e658890bd7ef-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.91 -->
**Degenerate upper bound.** The QHB limits only nondegenerate codes; a random stabilizer's typical element has weight $3n/4\gg pn$, so degeneracies are negligible and the QHB applies. Restricted-form stabilizers can have many degeneracies and exceed the QHB [shor-smolin], though only slightly — Shor and Smolin concatenate a random code with a repetition code ($|0\rangle\to|0\rangle^{\otimes m}$, $|1\rangle\to|1\rangle^{\otimes m}$, optimal block size five). Assuming every element of $S$ has weight $xn$: at least $N(xn)/2^{n-k}$ weight-$n$ operators commute with $S$, of which $2^{n-k}$ lie in $S$, leaving $N(xn)/2^{n-k}-2^{n-k}$ troublesome operators. For large $n$, $k=rn$, either $N(xn)/2^{n-k}$ dominates (recovering the QHB), or $N(xn)/2^{n-k}\ll2^{n-k}$, giving $N(xn)\ll2^{2(n-k)}$ and
$$r=k/n<1-\tfrac{1}{2n}\log_2 N(xn)=1-\tfrac{x}{2}\log_2 3-\tfrac12 H(x)$$
(eq-deg-bound). Since $x=2p-4p^2/3$ this exceeds the QHB and upper-bounds the depolarizing-channel capacity achievable with stabilizer codes. Cleve's degenerate-code bound [cleve-classical] is slightly worse throughout the region of interest.

<a id="pdf-e658890bd7ef-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.95 -->
Figure (CCBounds): the quantum Hamming bound (dashed), the Knill-Laflamme bound (dotted), and the bound (eq-deg-bound) (solid).
