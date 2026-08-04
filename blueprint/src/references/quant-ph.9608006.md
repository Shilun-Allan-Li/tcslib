<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 4fa1f624d1c5302fdb219cbf7200800ddad55ae0401f87f8215aadb18dbd44e8 -->

<a id="pdf-4fa1f624d1c5-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Quantum Error Correction Via Codes Over $GF(4)$

Authors: A. R. Calderbank, E. M. Rains, P. W. Shor, N. J. A. Sloane (AT&T Labs / IDA), Aug 27, 1997.

**Abstract.** Finding quantum-error-correcting codes is transformed into finding additive codes over $GF(4)$ that are self-orthogonal with respect to a certain trace inner product. Presents many new codes and bounds, plus a table of upper/lower bounds for codes of length up to 30 qubits.

<a id="pdf-4fa1f624d1c5-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Motivational background: quantum vs. classical information differ (e.g. no-cloning theorem forbids duplicating a qubit), so classical error-correction techniques were thought inapplicable. Shor showed quantum-error-correcting codes exist; Calderbank–Shor gave a construction from a binary linear code $C$ containing its dual $C^\perp$ (CSS), discovered independently by Steane. Bennett et al. showed EPR-pair purification over a one-way classical channel is equivalent to a quantum code. The known codes connect to a finite group $L$ (the Clifford group) of unitaries on $\mathbb{C}^{2^n}$ that performs encoding/decoding; this leads to a general construction (initially reported in CRSS96, some ideas found independently by Gottesman). This paper develops the theory so standard classical coding techniques can be applied.

<a id="pdf-4fa1f624d1c5-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->
Organization: §2 reduces the problem to constructing a binary space (Theorem `th1`); §3 shows these are equivalent to additive codes over $GF(4)$ (Theorem `th2`) and gives basic properties; §4 general constructions; §§5–7 cyclic/related, self-dual codes, and bounds; the linear programming bound (Theorems `LPA`, `LPW`) in §7 gives sharp bounds; §8 gives the main Table III; §9 gives updates since first circulation.

<a id="pdf-4fa1f624d1c5-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->
## From quantum codes to binary spaces

(Note: proofs that are standard or straightforward are omitted throughout.)

<a id="pdf-4fa1f624d1c5-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.92 -->
An encoding of $k$ qubits into $n$ qubits is a linear map of $\mathbb{C}^{2^k}$ onto a $2^k$-dimensional subspace of $\mathbb{C}^{2^n}$; since error-correction depends only on the subspace, the subspace itself is called the quantum error correcting code. Using the tensor decomposition $\mathbb{C}^{2^n}=(\mathbb{C}^2)^{\otimes n}$, codes are oriented so that any error on a small number of qubits moves a coded state perpendicular to the code subspace and is thus correctable.

<a id="pdf-4fa1f624d1c5-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.93 -->
Bit error = Pauli $\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, phase error = $\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, and $\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}=i\sigma_x\sigma_z$ (combined). The error group $E$ consists of tensor products $\pm w_1\otimes\cdots\otimes w_n$ and $\pm i\,w_1\otimes\cdots\otimes w_n$ with each $w_j\in\{I,\sigma_x,\sigma_y,\sigma_z\}$; $E\subset U(2^n)$. Correcting these three error types on $t$ qubits suffices to correct arbitrary errors on $t$ qubits, because $\{I,\sigma_x,\sigma_y,\sigma_z\}$ is a basis of $2\times2$ matrices, so their $t$-fold tensor products span all $2^t\times2^t$ matrices.

<a id="pdf-4fa1f624d1c5-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
Codes are designed for the model where each qubit undergoes independent errors with $\sigma_x,\sigma_y,\sigma_z$ equally likely; such codes also handle arbitrary uncorrelated, low-rate error models.

<a id="pdf-4fa1f624d1c5-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.95 -->
Let $\bar E$ be the $2n$-dimensional binary vector space with elements written $(a\mid b)$ and inner product
$$((a\mid b),(a'\mid b'))=a\cdot b'+a'\cdot b.\qquad(2)$$
This is symplectic since $((a\mid b),(a\mid b))=0$. The **weight** of $(a\mid b)=(a_1\cdots a_n\mid b_1\cdots b_n)$ is the number of coordinates $i$ with $a_i=1$ or $b_i=1$. The **distance** between two elements is the weight of their difference.

<a id="pdf-4fa1f624d1c5-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.95 -->
**Theorem 1 (`th1`).** Suppose $\bar S$ is an $(n-k)$-dimensional linear subspace of $\bar E$ contained in its dual $\bar S^\perp$ (w.r.t. inner product $(2)$), such that there are no vectors of weight $\le d-1$ in $\bar S^\perp\setminus\bar S$. Then there is a quantum-error-correcting code mapping $k$ qubits to $n$ qubits that can correct $\lfloor(d-1)/2\rfloor$ errors. (Immediate consequence of Theorem 1 of CRSS96.)

<a id="pdf-4fa1f624d1c5-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.94 -->
Such a code has parameters $[[n,k,d]]$ with **minimal distance** $d$; a code from Theorem `th1` is called **additive**. More general codes use notation $((n,K,d))$: minimal distance $d$, encoding $K$ states into $n$ qubits. An $[[n,k,d]]$ code is also an $((n,2^k,d))$ code.

<a id="pdf-4fa1f624d1c5-p002-b008"></a>
<!-- pdf-source: page=2; block=8; confidence=0.90 -->
Reformulation of classical binary linear codes: a linear code $C\subseteq\mathbb{Z}_2^n$ is also a subgroup of the error group $\mathbb{Z}_2^n$. An error $e\in C$ iff translation by $e$ maps codewords to codewords (undetectable). $C$ corrects a set of errors iff the sum of any two errors is detectable (outside $C$), except for the trivial error $\mathbf 0$, which is undetectable but harmless.

<a id="pdf-4fa1f624d1c5-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.91 -->
In the quantum setting a nontrivial error can be undetectable yet have no effect on the encoded state. So build a quantum code from two subgroups of $E$: $S'$ (undetectable errors) and $S\subseteq S'$ (errors with no effect, analogue of the classical zero subgroup). Require every element of $S'$ to commute with $S$; in particular $S$ is abelian.

<a id="pdf-4fa1f624d1c5-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.94 -->
$E$ has order $2^{2n+2}$ and center $\Xi(E)=\{\pm I,\pm iI\}$; the quotient $\bar E=E/\Xi(E)$ is elementary abelian of order $2^{2n}$, a binary vector space. With $V=\mathbb{Z}_2^n$ and basis $|v\rangle$ of $\mathbb{C}^{2^n}$, every $e\in E$ is uniquely
$$e=i^\lambda X(a)Z(b),\qquad(1)$$
where $\lambda\in\mathbb{Z}_4$, $X(a):|v\rangle\to|v+a\rangle$, $Z(b):|v\rangle\to(-1)^{b\cdot v}|v\rangle$, $a,b\in V$. $X(a)Z(b)$ has bit errors where $a_j=1$ and phase errors where $b_j=1$. ($E$ is essentially an extraspecial 2-group.)

<a id="pdf-4fa1f624d1c5-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.94 -->
For $e,e'\in E$ given by $(1)$, $ee'=\pm e'e$ with sign $(-1)^{a\cdot b'+a'\cdot b}$, inducing the symplectic inner product $((a\mid b),(a'\mid b'))=a\cdot b'+a'\cdot b$ on the images $(a\mid b)$ in $\bar E$. Two elements of $E$ commute iff their images are orthogonal under this form.

<a id="pdf-4fa1f624d1c5-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.94 -->
A subspace $\bar S\subseteq\bar E$ is **totally isotropic** if $(\bar s_1,\bar s_2)=0$ for all $\bar s_1,\bar s_2\in\bar S$. A subgroup $S\le E$ is commutative iff its image $\bar S$ is totally isotropic; such a subspace has dimension $\le n$. The groups $X=\{X(a):a\in V\}$ and $Z=\{Z(b):b\in V\}$ have images of dimension $n$. Define $S^\perp$ as the lift of $(\bar S)^\perp$ to $E$, i.e. the centralizer of $S$ in $E$; take $S'=S^\perp$ as the group of undetectable errors.

<a id="pdf-4fa1f624d1c5-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.91 -->
Since $S$ is abelian its elements are simultaneously diagonalizable, decomposing $\mathbb{C}^{2^n}$ into orthogonal eigenspaces. The code $Q$ is taken to be one eigenspace (preserved by $S^\perp$); these are the **additive** codes. Each eigenspace corresponds to a character $\chi:S\to\mathbb{C}$ with $\chi(iI)=i$.

<a id="pdf-4fa1f624d1c5-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.91 -->
Every $e\in E$ normalizes $S$, inducing an action on characters; $S^\perp$ acts trivially while elements outside $S^\perp$ negate the character on elements they anticommute with, so $E/S^\perp$ acts faithfully. Each character orbit has size $|E/S^\perp|$. If $\bar S$ has dimension $n-k$ then $|E/S^\perp|=2^{n-k}$, matching the $2^{n-k}$ characters with $\chi(iI)=i$, so $E/S^\perp$ acts transitively and each eigenspace has dimension $2^k$.

<a id="pdf-4fa1f624d1c5-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.95 -->
**Lemma 1 (`Lem1`).** An additive quantum-error-correcting code $Q$ with associated space $\bar S$ can correct a set of errors $\Sigma\subseteq E$ precisely when $\bar e_1^{-1}\bar e_2\notin\bar S^\perp\setminus\bar S$ for all $e_1,e_2\in\Sigma$.

<a id="pdf-4fa1f624d1c5-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.93 -->
**Proof.** ($\Leftarrow$) To correct an occurred error $e$ we find $e_1\in E$ with $e_1^{-1}e\in S$, i.e. determine the coset $eS$. The hypothesis ensures each coset of $S^\perp$ contains at most one coset of $S$ meeting $\Sigma$, so it suffices to determine $eS^\perp$. Since $E/S^\perp$ permutes the eigenspaces of $S$ regularly, measuring which eigenspace the state lies in (possible as they are orthogonal) reveals $eS^\perp$ without disturbing the state. ($\Rightarrow$) If $\bar e_1^{-1}\bar e_2\in\bar S^\perp\setminus\bar S$: any correction must send $e_1(v)\in e_1(Q)$ to $v$. Because $e_1^{-1}e_2\in S^\perp$, $e_2(v)\in e_1(Q)$, so $e_2(v)$ gets corrected to $e_1^{-1}e_2(v)$; but $e_1^{-1}e_2\notin S$ means some $v\in Q$ has $e_1^{-1}e_2(v)$ not proportional to $v$, so $e_2$ is not corrected. $\Box$

<a id="pdf-4fa1f624d1c5-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.96 -->
**Proof (continued).** Let $d$ be the minimal weight of $\bar S^\perp \setminus \bar S$; then the code corrects every error of weight $\le [(d-1)/2]$. This completes the proof of Theorem 1: $Q$ maps $k$ qubits into $n$ qubits and corrects $[(d-1)/2]$ errors.

<a id="pdf-4fa1f624d1c5-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.94 -->
Eigenspaces of $S$ correspond bijectively to characters $\chi$ of $S$ with $\chi(iI)=i$; the eigenspace containing a state is identified by computing this character. Since $\chi$ is a homomorphism it suffices to evaluate it on a basis of $\bar S$; each basis element yields one bit, and the collected bits form the *syndrome* of the error. Recovering the most likely error from the syndrome may be hard, though exhaustive search always works in principle.

<a id="pdf-4fa1f624d1c5-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.94 -->
**Definition (Clifford groups).** The *complex Clifford group* $L$ is the subgroup of the normalizer of $E$ in $U(2^n)$ with entries in $\mathbb{Q}[\eta]$, $\eta=(1+i)/\sqrt2$. (The full normalizer has infinite center $e^{2\pi i\theta}I$; $\mathbb{Q}[\eta]$ is the smallest usable coefficient ring, since $\{\tfrac1{\sqrt2}\begin{psmallmatrix}1&1\\1&-1\end{psmallmatrix}\begin{psmallmatrix}1&0\\0&i\end{psmallmatrix}\}^3=\begin{psmallmatrix}\eta&0\\0&\eta\end{psmallmatrix}$.) The *real Clifford group* $L_R$ is the real subgroup of $L$, equivalently the subgroup with entries in $\mathbb{Q}[\sqrt2]$; with $E_R$ the real subgroup of $E$, $L_R$ is the normalizer of $E_R$ in $O(2^n)$. $E_R$ consists of $\pm w_1\otimes\cdots\otimes w_n$ with each $w_j\in\{I,\sigma_x,\sigma_z,\sigma_x\sigma_z\}$; it is extraspecial of order $2^{2n+1}$ with center $\{\pm I\}$, and $E_R/\{\pm I\}=E/\Xi(E)=\bar E$.

<a id="pdf-4fa1f624d1c5-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->
**Generators.** $L$ is generated by $E$, all matrices $I_2\otimes\cdots\otimes H_2\otimes\cdots\otimes I_2$ (Eq. 300), where $H_2=\tfrac1{\sqrt2}\begin{psmallmatrix}1&1\\1&-1\end{psmallmatrix}$, and all $\operatorname{diag}(i^{\phi(v)})_{v\in V}$ with $\phi$ any $\mathbb{Z}_4$-valued quadratic form on $V$. $L_R$ is generated by $E_R$, Eq. (300), and all $\operatorname{diag}((-1)^{\phi(v)})_{v\in V}$ with $\phi$ any $\mathbb{Z}_2$-valued quadratic form on $V$.

<a id="pdf-4fa1f624d1c5-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.95 -->
Properties: $L/\langle E,\eta I\rangle\cong Sp_{2n}(2)$ (the $2n\times2n$ matrices over $\mathbb{Z}_2$ preserving inner product (1)); $|L|=8\,|Sp_{2n}(2)|\,2^{2n}=2^{n^2+2n+3}\prod_{j=1}^n(4^j-1)$. $L_R/E_R\cong O_{2n}^+(2)$; $|L_R|=2\,|O_{2n}^+(2)|\,2^{2n}=2^{n^2+n+2}(2^n-1)\prod_{j=1}^{n-1}(4^j-1)$. $L$ acts on $\bar E$ as $Sp_{2n}(2)$ and $L_R$ acts on $\bar E$ as $O_{2n}^+(2)$.

<a id="pdf-4fa1f624d1c5-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.90 -->
$L$ and $L_R$ link quantum codes with Barnes–Wall lattices, orthogonal spreads and Kerdock sets, spherical codes, and Grassmannian packings, and occur in purely group-theoretic settings; discussed further later.

<a id="pdf-4fa1f624d1c5-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.94 -->
Since $Sp_{2n}(2)$ acts transitively on isotropic subspaces and $E$ transitively on eigenspaces of a given subspace, $L$ acts transitively on additive codes. The trivial code corresponds to the subspace $\bar S$ with generators $(0\mid e_i)$, $i=k+1,\dots,n$; by transitivity some (non-unique) $\lambda\in L$ carries it to $Q$. Cleve and Gottesman give explicit gate descriptions of $\lambda$.

<a id="pdf-4fa1f624d1c5-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.94 -->
**Definition.** A code is *nondegenerate* if distinct elements of $E$ give linearly independent results on code elements, and *pure* if distinct elements of $E$ give orthogonal results. For additive codes 'pure' and 'nondegenerate' coincide; in general pure $\Rightarrow$ nondegenerate but not conversely. The paper adopts the pure/impure dichotomy throughout.

<a id="pdf-4fa1f624d1c5-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.93 -->
To obtain a basis for $Q$: choose a maximal isotropic subspace $\bar T\supseteq\bar S$ and take those $1$-dimensional eigenspaces of $T$ whose character agrees with the given character on $S$ (equivalently, all eigenspaces lying inside $Q$). $T$ is not unique, giving the same freedom as in the choice of $\lambda$.

<a id="pdf-4fa1f624d1c5-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.96 -->
**Theorem Nth1 (restated).** Suppose $\bar S$ is an $(n-k)$-dimensional linear subspace of $\bar E$ contained in its dual $\bar S^\perp$ (w.r.t. inner product (Eq. 2)), with no vectors of weight $\le d-1$ in $\bar S^\perp\setminus\bar S$. Then an eigenspace (for any chosen linear character) of $\bar S$ is a quantum-error-correcting code mapping $k$ qubits to $n$ qubits and correcting $[(d-1)/2]$ errors.

<a id="pdf-4fa1f624d1c5-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.97 -->
**Section 3. From binary spaces to codes over $GF(4)$.**

<a id="pdf-4fa1f624d1c5-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.96 -->
**Definition.** $GF(4)=\{0,1,\omega,\bar\omega\}$ with $\omega^2=\omega+1$, $\omega^3=1$, conjugation $\bar x=x^2$, and trace $\operatorname{Tr}:GF(4)\to\mathbb{Z}_2$, $x\mapsto x+\bar x$. The Hamming weight $\operatorname{wt}(u)$ of $u\in GF(4)^n$ is its number of nonzero components; the Hamming distance is $\operatorname{dist}(u,u')=\operatorname{wt}(u-u')$; $\operatorname{dist}(C)$ is the minimal distance over a subset $C$.

<a id="pdf-4fa1f624d1c5-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.95 -->
**Definition.** For $v=(a\mid b)\in\bar E$ set $\phi(v)=\omega a+\bar\omega b\in GF(4)^n$. Then $\operatorname{wt}(v)=\operatorname{wt}(\phi(v))$ and $\operatorname{dist}(v,v')=\operatorname{dist}(\phi(v),\phi(v'))$. The symplectic inner product of $v,v'$ (Eq. 2) equals $\operatorname{Tr}(\phi(v)\cdot\overline{\phi(v')})$; the computation gives $\operatorname{Tr}((\omega a+\bar\omega b)(\bar\omega a'+\omega b'))=a\cdot b'+a'\cdot b$.

<a id="pdf-4fa1f624d1c5-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.96 -->
**Definition.** If $\bar S\subseteq\bar E$ is a linear subspace, $C=\phi(\bar S)\subseteq GF(4)^n$ is closed under addition, an *additive* code; it is an $(n,2^k)$ code if it has $2^k$ vectors. If $C$ is also closed under multiplication by $\omega$ it is *linear*.

<a id="pdf-4fa1f624d1c5-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.96 -->
**Definition.** The *trace inner product* is $u\ast v=\operatorname{Tr}\,u\cdot\bar v=\sum_{j=1}^n(u_j\bar v_j+\bar u_j v_j)$ (Eq. 8). For an $(n,2^k)$ additive code, $C^\perp=\{u\in GF(4)^n: u\ast v=0\ \forall v\in C\}$ (Eq. 9) is an $(n,2^{2n-k})$ code. $C$ is *self-orthogonal* if $C\subseteq C^\perp$ and *self-dual* if $C=C^\perp$.

<a id="pdf-4fa1f624d1c5-p005-b008"></a>
<!-- pdf-source: page=5; block=8; confidence=0.95 -->
**Theorem 2.** If $C$ is an additive self-orthogonal subcode of $GF(4)^n$ with $2^k$ vectors and no vectors of weight $\le d-1$ in $C^\perp\setminus C$, then any eigenspace of $\phi^{-1}(C)$ is a quantum-error-correcting code with parameters $[[n,n-k,d]]$.

<a id="pdf-4fa1f624d1c5-p005-b009"></a>
<!-- pdf-source: page=5; block=9; confidence=0.95 -->
**Definition.** $C$ is *pure* if $C^\perp$ has no nonzero vector of weight $<d$, else *impure*. The associated QECC is pure (Section 2 sense) iff $C$ is pure. A QECC is *linear* if its associated additive code $C$ is linear.

<a id="pdf-4fa1f624d1c5-p005-b010"></a>
<!-- pdf-source: page=5; block=10; confidence=0.93 -->
For $[[n,k,d]]$ codes $k=0$ is allowed, corresponding to a self-dual $(n,2^n)$ code $C$ of minimal nonzero weight $d$; an $[[n,0,d]]$ code is pure by convention. Such a code is a quantum state for which decoherence of $[(d-1)/2]$ coordinates can be exactly located — useful e.g. for detecting abnormally fast-decohering storage locations (Section 6).

<a id="pdf-4fa1f624d1c5-p005-b011"></a>
<!-- pdf-source: page=5; block=11; confidence=0.94 -->
**Definition.** Most previously studied $GF(4)$ codes are linear with duality w.r.t. the hermitian inner product $u\cdot\bar v$; these are called *classical*.

<a id="pdf-4fa1f624d1c5-p005-b012"></a>
<!-- pdf-source: page=5; block=12; confidence=0.96 -->
**Theorem MM1.** A linear code $C$ is self-orthogonal w.r.t. the trace inner product (Eq. 8) if and only if it is classically self-orthogonal w.r.t. the hermitian inner product.

<a id="pdf-4fa1f624d1c5-p005-b013"></a>
<!-- pdf-source: page=5; block=13; confidence=0.95 -->
**Proof.** Sufficiency is clear. If $C$ is self-orthogonal, write $u\cdot\bar v=\alpha+\beta\omega$ ($\alpha,\beta\in\mathbb{Z}_2$) for $u,v\in C$. Then $\operatorname{Tr}(u\cdot\bar v)=0$ forces $\beta=0$, and $\operatorname{Tr}(u\cdot\bar\omega\bar v)=0$ forces $\alpha=0$, so $u\cdot\bar v=0$. $\Box$

<a id="pdf-4fa1f624d1c5-p005-b014"></a>
<!-- pdf-source: page=5; block=14; confidence=0.94 -->
An $(n,2^k)$ additive code is specified by a $k\times n$ generator matrix whose rows span it additively, or by listing generators in $\langle\ \rangle$. If linear, a $(k/2)\times n$ generator matrix whose rows are a $GF(4)$-basis suffices.

<a id="pdf-4fa1f624d1c5-p005-b015"></a>
<!-- pdf-source: page=5; block=15; confidence=0.95 -->
**Definition.** $\mathcal{G}_n$ is the group of order $6^n n!$ generated by coordinate permutations, multiplication of coordinates by $\omega$, and coordinate conjugation — the wreath product $S_3\wr S_n$; it preserves weights and trace inner products. Two additive codes of length $n$ are *equivalent* if related by an element of $\mathcal{G}_n$. $\mathrm{Aut}(C)$ is the subgroup fixing $C$, and the number of codes equivalent to $C$ is $6^n n!/|\mathrm{Aut}(C)|$ (Eq. 10).

<a id="pdf-4fa1f624d1c5-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.94 -->
To find $\mathrm{Aut}(C)$ for an $(n,2^k)$ additive code, map $C$ to a $[3n,k]$ binary linear code $\beta(C)$ using $0\to000$, $1\to011$, $\omega\to101$, $\bar\omega\to110$ on each generator. With $\Omega$ the $(n,2^{2n})$ code of all vectors, form $\beta(\Omega)$. Compute (e.g. in MAGMA) the automorphism groups of $\beta(C)$ and $\beta(\Omega)$; their intersection is $\mathrm{Aut}(C)$.

<a id="pdf-4fa1f624d1c5-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.94 -->
**Definition.** Any $(n,2^k)$ additive code is equivalent to one with generator matrix $\begin{bmatrix}I_{k_0}&\omega B_1&A_1\\\omega I_{k_0}&\omega B_2&A_2\\0&I_{k_1}&B_3\end{bmatrix}$, where $A_j$ is arbitrary, $B_j$ binary, and $k=2k_0+k_1$. A code is *even* if every codeword has even weight, otherwise *odd*.

<a id="pdf-4fa1f624d1c5-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.96 -->
**Theorem M0.** An even additive code is self-orthogonal. A self-orthogonal linear code is even.

<a id="pdf-4fa1f624d1c5-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.95 -->
**Proof.** The first assertion follows from $\operatorname{wt}(u+v)\equiv\operatorname{wt}(u)+\operatorname{wt}(v)+u\ast v\ (\bmod 2)$ (Eq. 11) for all $u,v\in GF(4)^n$; the second from $u\ast(\omega u)\equiv\operatorname{wt}(u)\ (\bmod 2)$ (Eq. 12). $\Box$

<a id="pdf-4fa1f624d1c5-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.95 -->
**Definition.** The weight distribution of an $(n,2^k)$ additive code $C$ is $A_0,\dots,A_n$ with $A_j$ the number of weight-$j$ vectors. Any translate $u+C$ ($u\in C$) has the same weight distribution, so the minimal distance equals the minimal nonzero weight. The weight enumerator is $W(x,y)=\sum_{j=0}^n A_j x^{n-j}y^j$.

<a id="pdf-4fa1f624d1c5-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.96 -->
**Theorem M1.** If $C$ is an $(n,2^k)$ additive code with weight enumerator $W(x,y)$, then $C^\perp$ has weight enumerator $2^{-k}W(x+3y,\,x-y)$.

<a id="pdf-4fa1f624d1c5-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.94 -->
**Proof.** This analog of the MacWilliams identity follows from Delsarte's general theory of additive codes, since the trace inner product is a special case of the symmetric inner products used there. $\Box$

<a id="pdf-4fa1f624d1c5-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.95 -->
**Section 4. General constructions.** Methods for modifying and combining additive codes over $GF(4)$.

<a id="pdf-4fa1f624d1c5-p006-b009"></a>
<!-- pdf-source: page=6; block=9; confidence=0.95 -->
**Definition.** The *direct sum* is $C\oplus C'=\{uv: u\in C, v\in C'\}$. Combining $[[n,k,d]]$ and $[[n',k',d']]$ codes gives an $[[n+n',k+k',d'']]$ code with $d''=\min\{d,d'\}$. A code that is not a direct sum is *indecomposable*.

<a id="pdf-4fa1f624d1c5-p006-b010"></a>
<!-- pdf-source: page=6; block=10; confidence=0.96 -->
**Theorem P0.** Suppose an $[[n,k,d]]$ code exists. (a) If $k>0$, an $[[n+1,k,d]]$ code exists. (b) If the code is pure and $n\ge2$, an $[[n-1,k+1,d-1]]$ code exists. (c) If $k>1$, or $k=1$ and the code is pure, an $[[n,k-1,d]]$ code exists. (d) If $n\ge2$, an $[[n-1,k,d-1]]$ code exists. (e) If $n\ge2$ and the associated code $C$ contains a weight-1 vector, an $[[n-1,k,d]]$ code exists.

<a id="pdf-4fa1f624d1c5-p006-b011"></a>
<!-- pdf-source: page=6; block=11; confidence=0.93 -->
**Proof.** Let $C\subset C^\perp$ be the associated $(n,2^{n-k})$ and $(n,2^{n+k})$ codes. (a) Take the direct sum of $C$ with $c_1=\{0,1\}$; the resulting $[[n+1,k,d]]$ code is impure (so this fails for $k=0$). (b) Puncture $C^\perp$ by deleting the first coordinate, giving $(n-1,2^{n+k})$ code $B^\perp$ of minimal distance $\ge d-1$; its dual is $\{u:0u\in C\}\subseteq B^\perp$. (c) There are codes $B,B^\perp$ of sizes $(n,2^{n-k+1}),(n,2^{n+k-1})$ with $C\subset B\subset B^\perp\subset C^\perp$. (d) Take $B=\{u:0u\text{ or }1u\in C\}$, so $B^\perp=\{v:0v\text{ or }1v\in C^\perp\}$; words of $C^\perp\setminus C$ of weight $<d$ starting with $\omega,\bar\omega$ are not in $B^\perp$, while those starting with $0,1$ give (after truncation) words of $B^\perp\setminus B$, and weight-$d$ words starting with $1$ become weight $d-1$, reducing minimal distance by 1. (e) Left to the reader. $\Box$

<a id="pdf-4fa1f624d1c5-p006-b012"></a>
<!-- pdf-source: page=6; block=12; confidence=0.92 -->
By P0(a), the $[[5,1,3]]$ Hamming code (Section 5) gives an impure $[[6,1,3]]$ code; exhaustive search (or integer programming, Section 7) shows no pure $[[6,1,3]]$ exists — the first case where an impure code exists but a pure one does not. A second, inequivalent impure $[[6,1,3]]$ code is generated by $000011,\ 011110,\ 0\omega\omega\omega\omega\omega,\ 101\omega\bar\omega\omega,\ \omega0\omega\bar\omega10$. Up to equivalence there are no other $[[6,1,3]]$ codes.

<a id="pdf-4fa1f624d1c5-p006-b013"></a>
<!-- pdf-source: page=6; block=13; confidence=0.95 -->
**Lemma P1.** Let $C$ be a linear self-orthogonal code over $GF(4)$, and $S$ a set of coordinates such that every codeword of $C$ meets $S$ in a vector of even weight. Then deleting the coordinates in $S$ yields a self-orthogonal code.

<a id="pdf-4fa1f624d1c5-p006-b014"></a>
<!-- pdf-source: page=6; block=14; confidence=0.95 -->
**Proof.** Follows from Theorem M0. $\Box$

<a id="pdf-4fa1f624d1c5-p006-b015"></a>
<!-- pdf-source: page=6; block=15; confidence=0.95 -->
**Theorem P2.** Given a linear $[[n,k,d]]$ code with associated $(n,2^{n-k})$ code $C$, there exists a linear $[[n-m,k',d']]$ code with $k'\ge k-m$ and $d'\ge d$, for any $m$ such that the dual of the binary code generated by the supports of the codewords of $C$ contains a codeword of weight $m$.

<a id="pdf-4fa1f624d1c5-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.10 -->
**Proof.** Let $S$ be the support of a word of weight $m$. Then $S$ satisfies the Lemma's conditions, and deleting those coordinates yields the desired code. $\Box$

<a id="pdf-4fa1f624d1c5-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.93 -->
**Example.** The $[[85,77,3]]$ Hamming code gives an $(85,2^4)$ code $C$ whose codeword supports generate a binary code with weight enumerator
$$x^{85}+3570\,x^{53}y^{32}+38080\,x^{45}y^{40}+23800\,x^{37}y^{48}+85\,x^{21}y^{64}.$$
Its MacWilliams transform (MS77, Thm 1, p.127) shows the dual binary code has words of weights $0$, $5$ through $80$, and $85$. Theorem P2 then yields $[[9,1,3]],[[10,2,3]],\dots,[[80,72,3]]$ codes. An analogue holds for additive codes via a more complicated binary construction.

<a id="pdf-4fa1f624d1c5-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->
**Theorem P3.** Given $[[n_1,k_1,d_1]]$ and $[[n_2,k_2,d_2]]$ codes with $k_2\le n_1$, one can construct an $[[n_1+n_2-k_2,\;k_1,\;d]]$ code where $d\ge\min\{d_1,\;d_1+d_2-k_2\}$.

<a id="pdf-4fa1f624d1c5-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.94 -->
**Proof.** Use associated codes $C_1,C_1^\perp$ of parameters $(n_1,2^{n_1-k_1}),(n_1,2^{n_1+k_1})$ and $C_2,C_2^\perp$ of parameters $(n_2,2^{n_2-k_2}),(n_2,2^{n_2+k_2})$. Let $\rho$ compose the natural map $C_2^\perp\to C_2^\perp/C_2$ with an inner-product-preserving map $C_2^\perp/C_2\to GF(4)^{k_2}$. Set $C=\{uv:v\in C_2^\perp,\;u\rho(v)\in C_1\}$ with $C^\perp=\{uv:v\in C_2^\perp,\;u\rho(v)\in C_1^\perp\}$. If $\rho(v)\ne0$, $v$ contributes $\ge d_2$ to $\mathrm{wt}(uv)$ while $u$ need only have weight $d_1-k_2$; if $\rho(v)=0$ and $uv\ne0$, then $\mathrm{wt}(u)\ge d_1$. $\Box$

<a id="pdf-4fa1f624d1c5-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.90 -->
Different $\rho$ (i.e. different encodings of $C_2$) may give inequivalent codes. Taking the second code $[[1,0,1]]$ (generator $[1]$) recovers $[[n_1+1,k_1,d_1]]$ (Thm P0(a)); taking $[[2,1,1]]$ (generator $[11]$) gives a different $[[n_1+1,k,d_1]]$. Concatenation: if $Q_1$ is $[[nm,k]]$ whose associated $(nm,2^{nm+k})$ code has minimal nonzero weight $d$ in each $m$-bit block and $Q_2$ is $[[n_2,m,d_2]]$, encoding each block via P3 gives an $[[nn_2,k,dd_2]]$ concatenated code. Concatenating the $[[5,1,3]]$ Hamming code with itself (associated $(5,2^4)$ generator $\left[\begin{smallmatrix}0&1&1&1&1\\1&0&1&\omega&\bar\omega\end{smallmatrix}\right]$) yields a $[[25,1,9]]$ code (Fig. 1); it is not pure though the Hamming code is.

<a id="pdf-4fa1f624d1c5-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.85 -->
**Figure 1.** Generator matrices for a $(25,2^{24})$ linear code (above the line) and its dual, a $(25,2^{26})$ linear code (all rows), corresponding to a $[[25,1,9]]$ quantum code. (Explicit $12\times25$ / $13\times25$ matrices over $\{0,1,\omega,\bar\omega\}$ shown; entries not transcribed.)

<a id="pdf-4fa1f624d1c5-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.95 -->
**Theorem P4** (restating/generalizing CaSh96). For binary linear codes $C_1\subseteq C_2$, taking $C=\omega C_1+\bar\omega C_2^\perp$ in Theorem th2 gives an $[[n,\;k_2-k_1,\;d]]$ code with $d=\min\{\mathrm{dist}(C_2\setminus C_1),\;\mathrm{dist}(C_1^\perp\setminus C_2^\perp)\}$.

<a id="pdf-4fa1f624d1c5-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.94 -->
**Proof.** $C$ is additive and $C\subseteq C^\perp=\bar\omega C_1^\perp+\omega C_2$. $\Box$

<a id="pdf-4fa1f624d1c5-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.94 -->
**Theorem P5** (generalizing Got96). Let $\mathcal S_m$ be the binary simplex code of length $n=2^m-1$, dimension $m$, minimal distance $2^{m-1}$. For a fixed-point-free automorphism $f$ of $\mathcal S_m$, let $\mathcal G_m$ be the $(2^m,2^{m+2})$ additive code generated by the vectors $u+\omega f(u)$ ($u\in\mathcal S_m$) with a $0$ appended, together with the length-$2^m$ vectors $11\ldots1$ and $\omega\omega\ldots\omega$. This yields a $[[2^m,\;2^m-m-2,\;3]]$ quantum code. (Proof omitted.)

<a id="pdf-4fa1f624d1c5-p007-b010"></a>
<!-- pdf-source: page=7; block=10; confidence=0.93 -->
Properties of $\mathcal G_m$ (proofs omitted):
(i) For any $f$, weight enumerator $x^{2^m}+4(2^m-1)x^{2^{m-2}}y^{3\cdot2^{m-2}}+3y^{2^m}$.
(ii) The weight-$2^m$ vectors generate a dimension-2 subcode.
(iii) $\mathcal G'_m$ (from $f'$) is equivalent to $\mathcal G_m$ iff $f'$ is conjugate under $\mathrm{Aut}(\mathcal S_m)$ to one of (Eq. 900) $\{f,\,1-f,\,1/f,\,1-1/f,\,1/(1-f),\,f/(1-f)\}$.
(iv) $\mathrm{Aut}(\mathcal G_m)$ has a normal subgroup $H$, a semidirect product of the centralizer of $f$ in $\mathrm{Aut}(\mathcal S_m)$ with $\mathcal S_m$; the index $[\mathrm{Aut}(\mathcal G_m):H]$ equals the number of elements of Eq. 900 conjugate to $f$.
(v) $\mathcal G_m$ is linear precisely when $f^2+f+1=0$.

<a id="pdf-4fa1f624d1c5-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
$\mathrm{Aut}(\mathcal S_m)\cong GL_m(2)$, whose conjugacy classes are determined by elementary divisors; so $f$ is conveniently specified by listing its elementary divisors.

<a id="pdf-4fa1f624d1c5-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.10 -->
$m=3$: unique $f$ (elementary divisor $x^3+x+1$), unique $\mathcal G_3=[[8,3,3]]$; $|\mathrm{Aut}(\mathcal G_3)|=168$ (semidirect product $C_3\rtimes GA_1(8)$).
$m=4$: three codes $[[16,10,3]]$: (a) $x^2+x+1$ twice — linear, $|\mathrm{Aut}|=17280$ (code is linear iff all elementary divisors equal $x^2+x+1$); (b) $(x^2+x+1)^2$, $|\mathrm{Aut}|=1152$; (c) $x^4+x+1$, $|\mathrm{Aut}|=480$.
$m=5$: two codes $[[32,25,3]]$: (a) $x^3+x+1$ and $x^2+x+1$, $|\mathrm{Aut}|=2016$; (b) $x^5+x^2+1$, $|\mathrm{Aut}|=992$.
Gottesman (Got96a) used a single $f$ given by the companion-type matrix (bottom row all ones; for odd $m$ the first row is complemented), corresponding to case (c) for $m=4$ and (b) for $m=5$.

<a id="pdf-4fa1f624d1c5-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->
**Theorem P6.** For $m\ge2$ there exists an $[[n,\;n-m-2,\;3]]$ code where $n=\sum_{i=0}^{m/2}2^{2i}$ ($m$ even) or $n=\sum_{i=1}^{(m-1)/2}2^{2i+1}$ ($m$ odd).

<a id="pdf-4fa1f624d1c5-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.92 -->
**Sketch of proof.** The associated $(n,2^{m+2})$ additive code $C$ has weight enumerator $x^n+(2^{m+2}-1)x^{n-2^m}y^{2^m}$ ($m$ even), or $x^n+(2^{m+2}-2^m)x^{n-2^m+2}y^{2^m-2}+(2^m-1)x^{n-2^m}y^{2^m}$ ($m$ odd). Take $C_2,C_3$ as the additive codes of $[[5,1,3]]$ and $[[8,3,3]]$. For $m>3$, with $\mathcal G_m$ from P5 and $\mathcal G'_m$ its weight-$2^m$ subcode, pick an isomorphism $\phi$ between $C_{m-2}$ and $\mathcal G_m/\mathcal G'_m$ (both dimension $m$). Define $C_m=\{v_1v_2:v_1\in C_{m-2},\ \phi(v_1)=v_2+\mathcal G'_m\}$. Counting gives the claimed weight distribution; by Theorem M1, $C_m^\perp$ has minimal distance 3. $\Box$

<a id="pdf-4fa1f624d1c5-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.93 -->
Theorem P6 was independently found by Got96a. The codes are pure and additive but generally nonlinear. For even $m$ one gets the Section-5 Hamming codes plus nonlinear codes with the same parameters; for odd $m$ one gets $[[8,3,3]],[[40,33,3]],[[168,159,3]],\dots$. A generator matrix for the $(40,2^7)$ additive code of a $[[40,33,3]]$ code is in Fig. 2.

<a id="pdf-4fa1f624d1c5-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.85 -->
**Figure 2.** Generator matrix for a $(40,2^7)$ additive code producing a $[[40,33,3]]$ quantum code. (Explicit $7\times40$ matrix over $\{0,1,\omega,\bar\omega\}$ shown; entries not transcribed.)

<a id="pdf-4fa1f624d1c5-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.95 -->
**Theorem P7.** Suppose there is a pure $[[n,k_1,d_1]]$ code with associated $(n,2^{n-k_1})$ additive code $C_1$ and a pure $[[n,k_2,d_2]]$ code with associated code $C_2$, with $C_1\subseteq C_2$. Then there exists a pure $[[2n,\;k_1-k_2,\;d]]$ code with $d=\min\{2d_1,\delta\}$, $\delta=\mathrm{dist}(C_2)$.

<a id="pdf-4fa1f624d1c5-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.94 -->
**Proof.** Take $C$ to be the $(2n,2^{2n-k_1+k_2})$ additive code of vectors $u\mid u+v$ with $u\in C_2^\perp,\ v\in C_1$. Then $C^\perp=\{u\mid u+v:u\in C_1^\perp,\ v\in C_2\}$ has minimal distance $\min\{2d_1,\delta\}$ by Theorem 33 of MS77, Ch. 1. $\Box$

<a id="pdf-4fa1f624d1c5-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.93 -->
Combining the $[[14,8,3]]$ and $[[14,0,6]]$ codes (Table II) gives a $[[28,8,6]]$ code. Adding one generator to a linear code is pointless: if $D$ is $(n,2^{n+k})$ linear and $D'=\langle D,v\rangle$ is $(n,2^{n+k+1})$ additive with minimal distance $d$, then the linear $D''=\langle D,v,\omega v\rangle$ also has minimal distance $d$. Trivial codes: $[[n,k,1]]$ exists for all $0\le k\le n$, $n\ge1$; $[[n,k,2]]$ exists for $0\le k\le n-2$ if $n\ge2$ even, or $0\le k\le n-3$ if $n\ge3$ odd.

<a id="pdf-4fa1f624d1c5-p008-b010"></a>
<!-- pdf-source: page=8; block=10; confidence=0.95 -->
**Section — Cyclic and related codes.**

<a id="pdf-4fa1f624d1c5-p008-b011"></a>
<!-- pdf-source: page=8; block=11; confidence=0.95 -->
**Definition.** An $(n,2^k)$ additive code $C$ is *constacyclic* if there is a constant $\kappa\in\{1,\omega,\bar\omega\}$ with $(u_0,\dots,u_{n-1})\in C\Rightarrow(\kappa u_{n-1},u_0,\dots,u_{n-2})\in C$. If $\kappa=1$ it is *cyclic*. If instead $(u_0,\dots,u_{n-1})\in C\Rightarrow(\bar u_{n-1},u_0,\dots,u_{n-2})\in C$, the code is *conjucyclic*.

<a id="pdf-4fa1f624d1c5-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.93 -->
A linear constacyclic code corresponds to an ideal in $GF(4)[x]/(x^n-\kappa)$, a principal ideal ring; the code is all multiples of a generator polynomial $g(x)$ dividing $x^n-\kappa$. Throughout, $n$ is odd.

<a id="pdf-4fa1f624d1c5-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->
**Theorem C1.** A linear cyclic or constacyclic code with generator $g(x)$ is self-orthogonal iff $g(x)g^{\dagger}(x)\equiv0\pmod{x^n-\kappa}$, where for $g(x)=\sum_{j=0}^{n-1}g_jx^j$,
$$g^{\dagger}(x)=\kappa\bar g_0+\sum_{j=1}^{n-1}\bar g_{n-j}x^j.\quad(\text{Eq. 13})$$

<a id="pdf-4fa1f624d1c5-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.93 -->
(Elementary proof omitted.) Note $g^{\dagger}(x)\equiv\overline{g(x^{-1})}\pmod{x^n-\kappa}$. The $\dagger$ operation is an involution on factors of $x^n-\kappa$, giving $x^n-\kappa=\prod_i p_i(x)\prod_j(q_j(x)q_j^{\dagger}(x))$ (Eq. 14) with all $p_i,q_j,q_j^{\dagger}$ distinct and $p_i^{\dagger}=p_i$. A divisor $g(x)$ generates a self-orthogonal linear constacyclic code iff $g$ is divisible by each $p_i$ and by at least one from each pair $q_j,q_j^{\dagger}$.

<a id="pdf-4fa1f624d1c5-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.94 -->
**Example.** The classical Hamming code $H$ over $GF(4)$ has length $n=(4^m-1)/3$, $4^{n-m}$ codewords, minimal distance 3 ($m\ge1$). Its dual $C=H^\perp$ is self-orthogonal, giving a $[[n,\,n-2m,\,3]]$ quantum code. $C,H$ are cyclic if $m$ even, constacyclic if $m$ odd. E.g. $m=2$: $g(x)=x^2+\omega x+1$ divides $x^5-1$; $m=3$: $g(x)=x^3+x^2+x+\omega$ divides $x^{21}-\omega$. These meet the sphere-packing bound (Eq. LP1) with equality. The smallest, $[[5,1,3]]$, was independently found in BDSW96 and LMPZ96.

<a id="pdf-4fa1f624d1c5-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.92 -->
Hamming codes correct single errors; their classical multi-error-correcting generalizations are BCH codes. An analogous generalization gives multiple-error-correcting quantum BCH codes, cyclic or constacyclic; only the construction and examples are given.

<a id="pdf-4fa1f624d1c5-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.93 -->
Cyclic case: let $\xi$ be a primitive $n$-th root of unity in an extension of $GF(4)$; write each $q_j=\prod_{s\in S_j}(x-\xi^s)$, the zero set $S_j$ a cyclotomic coset mod $n$ under multiplication by 4; the zero set of $q_j^{\dagger}$ is $-2S_j$. Choose a minimal subset of the $q_j$ such that (a) the union of their zero sets contains an arithmetic progression of length $d-1$ with step size coprime to $n$, and (b) if $q_j$ is chosen then $q_j^{\dagger}$ is not. Let $B$ be the cyclic code whose generator is the product of the chosen $q_j$. Then (a) gives minimal distance $\ge d$ and (b) gives $B\supset B^\perp$, yielding $[[n,k,d]]$ with $k=n-2\deg g$.

<a id="pdf-4fa1f624d1c5-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.92 -->
Constacyclic case: same construction but $\xi$ a primitive $(3n)$-th root of unity. For $n=(4^m-1)/3$ most $q_j$ have degree $m$, giving (for $m\ge4$) the sequence $[[n,n-2m,3]],[[n,n-4m,4]],[[n,n-6m,5]],[[n,n-8m,7]],\dots$. E.g. $m=4$: $[[85,77,3]],[[85,69,4]],[[85,61,5]],[[85,53,7]]$. Turning to additive (not necessarily linear) codes: an additive constacyclic code with $\kappa=\omega$ or $\bar\omega$ is necessarily linear.

<a id="pdf-4fa1f624d1c5-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.94 -->
**Theorem C2.** (a) Any $(n,2^k)$ additive cyclic code $C$ has two generators, $C=\langle\omega p(x)+q(x),\,r(x)\rangle$, with $p,q,r$ binary polynomials, $p$ and $r$ dividing $x^n-1\pmod2$, $r$ dividing $q(x)(x^n-1)/p(x)\pmod2$, and $k=2n-\deg p-\deg r$. (b) Any other such representation $\langle\omega p'(x)+q'(x),r'(x)\rangle$ satisfies $p'=p$, $r'=r$, $q'\equiv q\pmod{r(x)}$. (c) $C$ is self-orthogonal iff
$$p(x)r(x^{n-1})\equiv p(x^{n-1})r(x)\equiv0\pmod{x^n-1},$$
$$p(x)q(x^{n-1})\equiv p(x^{n-1})q(x)\pmod{x^n-1}.$$

<a id="pdf-4fa1f624d1c5-p009-b009"></a>
<!-- pdf-source: page=9; block=9; confidence=0.93 -->
**Proof.** (a) The componentwise trace map $\mathrm{Tr}:C\to\mathbb Z_2[x]/(x^n-1)$ has kernel a binary cyclic code $\langle r(x)\rangle$ ($r\mid x^n-1$) and image a binary cyclic code $\langle p(x)\rangle$; $C$ is generated by $r(x)$ and an inverse image $\omega p(x)+q(x)$ of $p(x)$. If $r$ did not divide $q(x)(x^n-1)/p(x)$, then $((x^n-1)/p(x))(\omega p(x)+q(x))$ would be a binary vector of $C$ outside $\langle r(x)\rangle$, a contradiction. (b) omitted. (c) The inner product of the vectors for $\omega f(x)+g(x)$ and $\omega h(x)+i(x)$ is the constant coefficient of $f(x)i(x^{n-1})+g(x)h(x^{n-1})\pmod{x^n-1}$; for $\omega f+g$ and $x^m(\omega h+i)$ it is the coefficient of $x^m$. The result follows. $\Box$

<a id="pdf-4fa1f624d1c5-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.90 -->
Stated without proof: if $C$ is self-orthogonal, $q(x)$ may be taken with $q(x^{n-1}) = \frac{\pi(x)}{p(x)} + \frac{\sigma(x)(x^n-1)}{p(x)}$ (Eq. 15), and $r(x) \mid q(x)(x^n-1)/p(x)$, where $\pi(x)\equiv\pi(x^{n-1})\pmod{x^n-1}$, $\pi(x)\equiv 0\pmod{p(x)}$, and $\deg\sigma < \deg r + \deg p - n$. This yields a search over all self-orthogonal additive cyclic codes of given dimension: $r(x)$ ranges over divisors of $x^n-1$, $p(x)$ over divisors of $(x^n-1)/\gcd\{r(x^{n-1}),x^n-1\}$ of appropriate degree, and all $\pi(x),\sigma(x)$ are considered.

<a id="pdf-4fa1f624d1c5-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.10 -->
Table I lists additive cyclic codes found by this search, with parameters $[[15,0,6]]$, $[[21,0,8]]$, $[[23,0,8]]$, $[[23,12,4]]$, $[[25,0,8]]$, each given by explicit generator vectors over $\{0,1,\omega,\bar\omega\}$.

<a id="pdf-4fa1f624d1c5-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.92 -->
**Theorem (C3).** Let $C$ be an $(n,2^k)$ additive conjucyclic code, and form the binary code $C' = \{\mathrm{Tr}(\omega u)\,|\,\mathrm{Tr}(\bar\omega u) : u\in C\}$, with trace applied componentwise and bar denoting concatenation. Then $C'$ is a binary cyclic code of length $2n$, self-orthogonal iff $C$ is self-orthogonal.

<a id="pdf-4fa1f624d1c5-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.85 -->
**Proof.** Omitted. Note $C'$ determines $C$ since $\omega\,\mathrm{Tr}(\omega u)+\bar\omega\,\mathrm{Tr}(\omega u)=u$; Theorem C3 enables searching such codes (no record codes found so far). Returning to linear codes: a *quasicyclic* code has length $n=ab$ with the group acting as $a$ cycles of length $b$. Gulliver's quasicyclic codes over small fields supply the last five examples of Table II; double parentheses indicate the permutation applied.

<a id="pdf-4fa1f624d1c5-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.10 -->
Table II lists linear quasicyclic codes with parameters $[[14,0,6]]$, $[[14,8,3]]$, $[[15,5,4]]$, $[[18,6,5]]$, $[[20,10,4]]$, $[[25,15,4]]$, $[[28,14,5]]$, $[[30,20,4]]$, $[[40,30,4]]$, each specified by parenthesized generator blocks over $\{0,1,\omega,\bar\omega\}$.

<a id="pdf-4fa1f624d1c5-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.97 -->
# Self-dual codes

<a id="pdf-4fa1f624d1c5-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.90 -->
Studies $[[n,0,d]]$ quantum codes and associated $(n,2^n)$ self-dual codes $C$; e.g. the unique $[[2,0,2]]$ code corresponds to the EPR pair $\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle)$. These are also used to build $[[n,k,d]]$ codes with $k>0$ (Section 8).

<a id="pdf-4fa1f624d1c5-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.93 -->
**Theorem (M2).** (a) The weight enumerator of a self-dual code is fixed under the transformation (Eq. 16): replace $\binom{x}{y}$ by $\tfrac12\left(\begin{smallmatrix}1&3\\1&-1\end{smallmatrix}\right)\binom{x}{y}$, and is therefore a polynomial in $x+y$ and $x^2+3y^2$. (b) The minimal distance of a self-dual code of length $n$ is $\le [n/2]+1$.

<a id="pdf-4fa1f624d1c5-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.90 -->
**Proof.** (a) Eq. 16 follows from Theorem M1; the second assertion parallels Theorem 13 of [MOSW78]. (b) Parallel to Corollary 3 of [MS73]. $\Box$ (The bound in (b) is later improved; see Section 9.)

<a id="pdf-4fa1f624d1c5-p010-b010"></a>
<!-- pdf-source: page=10; block=10; confidence=0.93 -->
**Theorem (M3).** (a) The weight enumerator of an even self-dual code is a polynomial in $x^2+3y^2$ and $y^2(x^2-y^2)^2$. (b) The minimal distance of an even self-dual code of length $n$ is $\le 2[n/6]+2$.

<a id="pdf-4fa1f624d1c5-p010-b011"></a>
<!-- pdf-source: page=10; block=11; confidence=0.92 -->
**Proof.** (a) Immediate from Theorem 13 of [MOSW78]. (b) From Corollary 15 of [MOSW78]. $\Box$

<a id="pdf-4fa1f624d1c5-p010-b012"></a>
<!-- pdf-source: page=10; block=12; confidence=0.85 -->
Motivated by the role of doubly-even self-dual codes in binary coding theory, the next result is noted.

<a id="pdf-4fa1f624d1c5-p010-b013"></a>
<!-- pdf-source: page=10; block=13; confidence=0.94 -->
**Theorem (M4).** If there is an integer constant $c>1$ such that the weight of every vector in a self-dual code is divisible by $c$, then $c=2$.

<a id="pdf-4fa1f624d1c5-p010-b014"></a>
<!-- pdf-source: page=10; block=14; confidence=0.92 -->
**Proof.** The proof of the Gleason–Prange theorem for classical self-dual codes in [Slo79] applies unchanged. $\Box$

<a id="pdf-4fa1f624d1c5-p010-b015"></a>
<!-- pdf-source: page=10; block=15; confidence=0.85 -->
A complete enumeration of self-dual codes of modest length is possible, following [MOSW78] and [CPS79].

<a id="pdf-4fa1f624d1c5-p010-b016"></a>
<!-- pdf-source: page=10; block=16; confidence=0.92 -->
**Theorem (M5).** (a) The total number of self-dual codes of length $n$ is $\prod_{j=1}^n(2^j+1)$. (b) $\sum \frac{1}{|\mathrm{Aut}(C)|} = \frac{\prod_{j=1}^n(2^j+1)}{6^n\,n!}$, where the sum is over all inequivalent self-dual codes $C$ of length $n$.

<a id="pdf-4fa1f624d1c5-p010-b017"></a>
<!-- pdf-source: page=10; block=17; confidence=0.92 -->
**Proof.** (a) Parallel to Theorem 19 of [MOSW78]. (b) From (a) and Eq. 10. $\Box$

<a id="pdf-4fa1f624d1c5-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.90 -->
**Definition.** Let $d_n$ be the $(n,2^{n-1})$ code spanned by all even-weight binary vectors of length $n$ ($n\ge2$), and $d_n^+ = \langle d_n,\ \omega\omega\ldots\omega\rangle$.

<a id="pdf-4fa1f624d1c5-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.92 -->
**Theorem (M6).** If $C$ is a self-orthogonal additive code with no identically-zero coordinate, generated by words of weight 2, then $C$ is equivalent to a direct sum $d_2^+\oplus\cdots\oplus d_2^+\oplus d_i\oplus d_j\oplus d_k\oplus\cdots$ with $i,j,k\ge2$.

<a id="pdf-4fa1f624d1c5-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.92 -->
**Proof.** Analogous to Theorem 4 of [CPS79]. $\Box$

<a id="pdf-4fa1f624d1c5-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.82 -->
Using Theorems M5 and M6, the numbers $t_n$ (inequivalent) and $i_n$ (inequivalent indecomposable) self-dual codes of length $n\le5$ are: $t_n = 1,2,3,6,11$ and $i_n = 1,1,1,2,4$ for $n=1,\dots,5$. The indecomposable codes are: the trivial code $c_1$; the codes $d_n^+$ ($n\ge2$); the length-4 code $\langle 1100,0011,\omega\omega\omega\omega,01\omega\bar\omega\rangle$; two length-5 codes $\langle 11000,00110,00101,01\omega\omega\omega,\omega\omega001\rangle$ and $\langle 11000,00110,10101,\omega\omega00\omega,00\omega\omega\omega\rangle$; and a $(5,2^5)$ $d=3$ code from the hexacode via Theorem P0.

<a id="pdf-4fa1f624d1c5-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.10 -->
The highest achievable minimal distance of self-dual (equiv. $[[n,0,d]]$) codes appears in the $k=0$ column of the main table (Section 8); by Theorem P0(c) this bounds minimal distances of pure $[[n,k,d]]$ codes. The Theorem M3 bound for even self-dual codes is met with equality at lengths $2,4,\ldots,22,28,30$, achievable by classical self-dual linear codes over $GF(4)$ except at length 12, where no classical self-dual $d=6$ code exists [CPS79] but an additive one does. This is the $(12,2^{12})$ $d=6$ *dodecacode*, given by an explicit $12\times12$ generator matrix over $\{0,1,\omega,\bar\omega\}$, equivalent to the cyclic code with generator $\omega10100100101$. Its weight distribution is $A_0=1$, $A_6=396$, $A_8=1485$, $A_{10}=1980$, $A_{12}=234$; its automorphism group has order 648 and is transitive on coordinates.

<a id="pdf-4fa1f624d1c5-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.85 -->
At length 24 there exist a $(24,2^{24})$ $d=8$ binary Golay code and at least two $(24,3^{12})$ $d=9$ ternary codes meeting the analogues of the Theorem M3(b) bound [MS77]. No $(24,4^{12})$ $d=10$ classical code over $GF(4)$ exists [LP90], but a $(24,2^{24})$ $d=10$ additive self-dual code remains open; linear programming forces such a code to be even, and construction attempts have failed, so it may not exist.

<a id="pdf-4fa1f624d1c5-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.97 -->
# Linear programming and other bounds

<a id="pdf-4fa1f624d1c5-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.90 -->
Gottesman [Got96]: any nondegenerate $[[n,k,2t+1]]$ code satisfies the sphere-packing bound $\sum_{j=0}^t 3^j\binom{n}{j}\le 2^{n-k}$ (Eq. LP1). Knill–Laflamme [KL96]: any code satisfies the Singleton bound $n\ge 4e+k$ (Eq. LP1b), where $e=\lfloor(d-1)/2\rfloor$. Setup: for a $[[n,k,d]]$ code let $C$ be the $(n,2^{n-k})$ code over $GF(4)$ and $C^\perp$ its $(n,2^{n+k})$ dual (Theorem th2), with weight distributions $A_i$ and $A'_i$; by Theorem P0(e) assume $A_1=0$. The Krawtchouk polynomials for length-$n$ codes over $GF(4)$ are $P_j(x,n)=\sum_{s=0}^j(-1)^s 3^{j-s}\binom{x}{s}\binom{n-x}{j-s}$, $j=0,\dots,n$ (Ch. 6 of [MS77]).

<a id="pdf-4fa1f624d1c5-p011-b009"></a>
<!-- pdf-source: page=11; block=9; confidence=0.90 -->
**Theorem (LPA).** If an $[[n,k,d]]$ code exists whose associated $(n,2^{n-k})$ code $C$ has no weight-1 vectors, then the following system has a solution: (LP6) $A_0=1$, $A_1=0$, $A_j\ge0$ ($2\le j\le n$); (LP7) $\sum_{j=0}^n A_j = 2^{n-k}$; (LP9) $A'_j = \frac{1}{2^{n-k}}\sum_{r=0}^n P_j(r,n)A_r$ ($0\le j\le n$); (LP10) $A_j=A'_j$ ($0\le j\le d-1$), $A_j\le A'_j$ ($d\le j\le n$); (LP11) $\sum_{j\ge0}A_{2j} = 2^{n-k-1}$ or $2^{n-k}$; (LP12) $\frac{1}{2^{n-k-1}}\sum_{r=0}^n P_j(2r,n)A_{2r}\ge A'_j$ ($0\le j\le n$). If the second option in LP11 holds, LP12 reduces to $2A'_j\ge A'_j$ and may be dropped.

<a id="pdf-4fa1f624d1c5-p011-b010"></a>
<!-- pdf-source: page=11; block=10; confidence=0.90 -->
**Proof.** LP9 follows from Theorem M1; LP10 from $C\subset C^\perp$ and the fact that any $C^\perp$ vector of weight between 1 and $d-1$ lies in $C$. By Eq. 11 the even-weight vectors of $C$ form an additive subcode $C'$ that is half or all of $C$, giving LP11. If $C'$ is half of $C$, then $C'\subset C\subset C^\perp\subset (C')^\perp$, yielding LP12. Remaining constraints are clear. $\Box$

<a id="pdf-4fa1f624d1c5-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.90 -->
**Theorem (LPW).** If an $[[n,k,d]]$ code exists then there are homogeneous degree-$n$ polynomials $W(x,y)$, $W^\perp(x,y)$, $S(x,y)$ with: (EqLPW1) $W(1,0)=W^\perp(1,0)=1$; (EqLPW2) $W^\perp(x,y)=2^k W\!\left(\frac{x+3y}{2},\frac{x-y}{2}\right)$; (EqLPW3) $S(x,y)=2^k W\!\left(\frac{x+3y}{2},\frac{y-x}{2}\right)$; (EqLPW4) $W^\perp(1,y)-W(1,y)=O(y^d)$; and (EqLPW5) $W(x,y),\ W^\perp(x,y)-W(x,y),\ S(x,y)\ge0$, where $P\ge0$ means $P$ has nonnegative coefficients.

<a id="pdf-4fa1f624d1c5-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.90 -->
**Proof.** Take $W$ and $W^\perp$ as the weight enumerators of $C$ and $C^\perp$. $S(x,y)$ is the *shadow enumerator* (cf. [shadow]), nonnegative by Eq. LP12. $\Box$

<a id="pdf-4fa1f624d1c5-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.85 -->
Two implementations: (i) minimize $A_1+\cdots+A_{d-1}$ subject to LP6–LP12 via an optimizer (CPLEX, CONOPT, formulated in AMPL); it either finds a solution or proves infeasibility (hence no such code), but near $n\approx30$ double-precision coefficients grow too large to trust. (ii) symbolic (MAPLE) exact-arithmetic feasibility check of LP6–LP12 or EqLPW1–EqLPW5 (the latter easier), reliable but slower. Most upper bounds in the main table were computed by both. For pure codes one sets $A_2,\dots,A_{d-1}=0$; within Table III this never changed the bound. LP11 is handled by running each right-hand-side choice. Example: by Theorem LPA no $[[n,1,5]]$ code with $A_1=0$ exists for $n\le10$, hence (Theorem P0) none of any type for $n\le10$, while an $[[11,1,5]]$ code does exist.

<a id="pdf-4fa1f624d1c5-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.82 -->
Variations of the argument: (i) No $[[13,0,6]]$ code: for a $(13,2^{13})$ additive code with $d\ge5$ and even subcode $C'$, the LP constraints express all unknowns via $A_5,A_6$; integrality of $(C')^\perp$'s weight distribution forces congruences eliminating $A_6$ and giving $A_5\equiv1\pmod2$, so $A_5\ne0$ and $d=5$. (ii) No $[[18,12,3]]$ code: for $(18,2^6)$ code $C$, LP forces a weight-12 vector, taken as $u_0=0^6 1^{12}$. Define the refined weight enumerator $R_C(x_0,x_1,y_0,y_1,y_2)=\sum_{u\in C}x_0^{6-a(u)}x_1^{a(u)}y_0^{12-b(u)-c(u)}y_1^{b(u)}y_2^{c(u)}$, where $a(u)$ is weight in the first 6 coordinates, $b(u)$/$c(u)$ count 1's / ($\omega$ or $\bar\omega$)'s in the last 12. Then $c(u)\equiv0\pmod2$, $(a,b,c)(u+u_0)=(a(u),12-b(u)-c(u),c(u))$, and $R_{C^\perp}=\frac{1}{|C|}R_C(x_0+3x_1,x_0-x_1,y_0+y_1+2y_2,y_0+y_1-2y_2,y_0-y_1)$. LP yields weight distribution either $\{A_0=1,A_{12}=9,A_{14}=54\}$ or $\{A_0=1,A_{12}=1,A_{13}=24,A_{14}=30,A_{15}=8\}$; both give infeasible refined LPs. (iii) Similar arguments rule out $[[7,0,4]]$, $[[15,4,5]]$, $[[15,7,4]]$, $[[16,8,4]]$, $[[19,3,3]]$, $[[22,14,4]]$, $[[25,0,10]]$.

<a id="pdf-4fa1f624d1c5-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.94 -->
**Theorem (SB1).** If a pure $[[n,k,d]]$ code exists then $k\le n-2d+2$.

<a id="pdf-4fa1f624d1c5-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.92 -->
**Proof.** The associated $C^\perp$ is an additive $(n,2^{n+k})$ code of minimal distance $d$. By Theorem 15 of [Del72], $2^{n+k}\le 4^{n-d+1}$, giving $k\le n-2d+2$. $\Box$

<a id="pdf-4fa1f624d1c5-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.85 -->
For odd $d$ this equals the Knill–Laflamme bound (LP1b); for even $d$ it is slightly stronger. All codes meeting it (analogues of classical MDS codes, cf. Ch. 11 of [MS77]) were determined; the answer is stated, the lengthy proof omitted.

<a id="pdf-4fa1f624d1c5-p012-b008"></a>
<!-- pdf-source: page=12; block=8; confidence=0.93 -->
**Theorem (SB2).** A pure $[[n,n-2d+2,d]]$ code has parameters $[[n,n,1]]$ ($n\ge1$), $[[n,n-2,2]]$ ($n$ even $\ge2$), $[[5,1,3]]$, or $[[6,0,4]]$. Up to equivalence there is a unique code in each case.

<a id="pdf-4fa1f624d1c5-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.90 -->
Allowing $k=n-2d+1$ yields no new codes: any pure $[[n,n-2d+1,d]]$ code has parameters $[[n,n-1,1]]$ ($n\ge1$), $[[n,n-3,2]]$ ($n\ge3$), $[[5,0,3]]$, or $[[8,3,3]]$.

<a id="pdf-4fa1f624d1c5-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.98 -->
# A table of quantum-error-correcting codes

<a id="pdf-4fa1f624d1c5-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->
Table III combines the best upper and lower bounds of previous sections to give the highest minimal distance $d$ achievable in any $[[n,k,d]]$ code of length $n\le30$.

<a id="pdf-4fa1f624d1c5-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.92 -->
**Notes.** Unknown exact $d$ shown as lower–upper bound separated by a dash. Unmarked upper bounds come from the linear programming bound (Theorem LPA); a few also from Eq. (LP1) or Theorem M2. Unmarked lower bounds come from Theorem P0. Except in the $k=0$ column, once a value of $d$ is achieved it holds for all lower entries in the same column, via Theorem P0(a).

<a id="pdf-4fa1f624d1c5-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.90 -->
**Markers.**
- $\alpha$: a code meeting this upper bound must be impure (integer-programming argument, as used for the nonexistence of a $[[13,0,6]]$ code).
- $\beta$: a special upper bound from Section 7; for nonadditive codes it must be increased by 1.
- $\gamma$: the unique other entry where the known nonadditive upper bound differs from the additive one — omitting Eq. (LP12) (the code is odd or even) raises the bound by 1. Elsewhere (LP12) is superfluous. A $((19,2^8,5))$ nonadditive code is thought unlikely.

<a id="pdf-4fa1f624d1c5-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.85 -->
Lower bounds specified via associated $(n,2^{n-k})$ additive codes:
- **a** hexacode: $(6,2^6)$ $d=4$ $GF(4)$ code, $Aut=3.S_6$ order 2160.
- **b** classical self-dual code over $GF(4)$.
- **c** cyclic code (Table I).
- **d** $[[25,1,9]]$ from concatenating $[[5,1,3]]$ Hamming with itself.
- **e** dodecacode (Section 6).
- **f** $[[8,3,3]]$ code; $(8,2^5)$ additive (generators given), unique, $Aut$ order 168 $=C_3\ltimes AGL(1,8)$.
- **g** quasicyclic code (Gulliver, Table II).
- **h** Hamming code.
- **i** $(12,2^8)$ and $(14,2^8)$ linear codes (generator matrices given), $Aut$ orders 720 and 8064, coordinate-transitive; the first via $u\mid u+v$ (Theorem P7) from the unique $[[6,4,2]]$ and $[[6,0,4]]$ codes.
- **j** $[[17,9,4]]$; dual $(17,2^8)$ $d=12$ two-weight code of class TF3, columns = 17 points of an ovoid in $PG(3,4)$; $C,C^\perp$ cyclic, $C^\perp$ generator $1\omega1\omega1\,0^{12}$; weights $A_0=1,A_{12}=204,A_{16}=51$; $Aut$ order 48960.
- **s** shorten (Theorem P2) the $[[21,15,3]]$/$[[85,77,3]]$ Hamming, $[[32,25,3]]$ Gottesman, $[[40,30,4]]$, or $[[40,33,3]]$ codes.
- **u** $u\mid u+v$ construction (Theorem P7).
- **v** a $(17,2^6)$ code with trivial automorphism group (matrix given).

<a id="pdf-4fa1f624d1c5-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.90 -->
Comparison with classical $GF(4)$ code tables suggests some lower bounds may be improvable via linear codes; e.g. classical linear $[30,18,8]$ codes over $GF(4)$ exist, and one containing its dual would yield a $[[30,6,8]]$ quantum code.

<a id="pdf-4fa1f624d1c5-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=0.10 -->
Data table (not reproduced in full): highest achievable $d$ in $[[n,k,d]]$ for $n=3..30$, columns $k=0..15$; ranges shown as low–high, entries annotated by the markers/notes above. Sample: $[[5,0,3]]$, $[[6,0,4]]^a$, $[[11,0,5]]$, $[[12,0,6]]^e$, $[[30,0,12]]^b$; $[[5,1,3]]^h$; $[[25,1,9]]^d$.

<a id="pdf-4fa1f624d1c5-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.10 -->
Continuation of Table III data (not reproduced in full): columns $k=16..23$, rows $n=16..30$; entries mostly $d\in\{1,2,3,4\}$ with ranges and $s$/$g$ annotations (e.g. $[[30,20,4]]^g$, $[[30,23,3]]^s$).

<a id="pdf-4fa1f624d1c5-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.98 -->
# Subsequent developments

<a id="pdf-4fa1f624d1c5-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.90 -->
Since the manuscripts of [CRSS96] and this paper first circulated (about 18 months earlier), a number of further developments occurred, listed below.

<a id="pdf-4fa1f624d1c5-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.90 -->
(i) Section 2 showed the Clifford group $L$ suffices to encode additive codes but gave no explicit recipes; these are now in Cleve–Gottesman [CG96].

<a id="pdf-4fa1f624d1c5-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.90 -->
(ii) The Cleve–Gottesman technique applies only to real codes, but any additive code is equivalent to a real additive code (and any linear to a real linear code) [RainsQSE], so this is not restrictive.

<a id="pdf-4fa1f624d1c5-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.90 -->
(iii) DiVincenzo–Shor [DiVS] correct errors in additive codes with imperfect gates; Shor's [ShoF] encoded-computation techniques extended to general additive codes by Gottesman [GottFT]. The most efficient known fault-tolerant methods use only CSS codes (cf. Theorem 9).

<a id="pdf-4fa1f624d1c5-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.90 -->
(iv) The lower bounds on quantum channel capacity of Bennett et al. [BBP96],[BDSW96] and DiVincenzo–Shor–Smolin [DiVSS] can be restated via additive codes, implying they are attainable by additive codes.

<a id="pdf-4fa1f624d1c5-p014-b008"></a>
<!-- pdf-source: page=14; block=8; confidence=0.92 -->
(v) Cleve [Cleve96] applies asymptotic upper bounds for classical binary codes to additive codes.

<a id="pdf-4fa1f624d1c5-p014-b009"></a>
<!-- pdf-source: page=14; block=9; confidence=0.92 -->
(vi) Steane [SteQR] extended Gottesman's construction (cf. Theorem P5) to quantum analogues of Reed–Muller codes; the smallest new code is $[[32,10,6]]$.

<a id="pdf-4fa1f624d1c5-p014-b010"></a>
<!-- pdf-source: page=14; block=10; confidence=0.90 -->
(vii) The $k=0$ upper bounds (except those marked $\beta$) have period 6; this led to an $n/3$ bound for quantum codes (Theorem M3) [RainsQSE] and an analogous $n/6$ bound for classical singly-even binary self-dual codes [RainsSB].

<a id="pdf-4fa1f624d1c5-p014-b011"></a>
<!-- pdf-source: page=14; block=11; confidence=0.90 -->
(viii) The main construction (Section 2) generalizes to primes greater than 2; preliminary work in [AhB],[Knill96],[Knill96a],[RainsNB].

<a id="pdf-4fa1f624d1c5-p014-b012"></a>
<!-- pdf-source: page=14; block=12; confidence=0.90 -->
(ix) Parts (a)–(c) of Theorem P0 have nonadditive analogues: (a),(c) trivial; (b) now asserts that if a pure $((n,K,d))$ code exists with $n\ge2$, then an $((n-1,2K,d-1))$ code exists [RainsQWE].

<a id="pdf-4fa1f624d1c5-p014-b013"></a>
<!-- pdf-source: page=14; block=13; confidence=0.90 -->
(x) Conjecture: restricting to additive codes costs little. Only one good nonadditive code is known, $((5,6,2))$ [RHSS] (best comparable additive is $((5,4,2))$); it generates a family $((2m+1,\,3\cdot2^{2m-3},\,2))$ for $m\ge2$ [RainsQd2]. $((5,6,2))$ is optimal (no $((5,7,2))$ exists). The next candidate is at length 7, where a $((7,1,4))$ code was sought unsuccessfully.

<a id="pdf-4fa1f624d1c5-p014-b014"></a>
<!-- pdf-source: page=14; block=14; confidence=0.90 -->
(xi) Most upper bounds are proved only for additive codes, but the LP bound (Theorem LPW) applies to nonadditive codes with suitable $W$, $W^\perp$ [ShLa] and $S$ [RainsQSE]; the only change is replacing $2^k$ by $K$. Consequently all but ten upper bounds in Table III (those marked $\beta$ or $\gamma$) apply to nonadditive codes too.

<a id="pdf-4fa1f624d1c5-p014-b015"></a>
<!-- pdf-source: page=14; block=15; confidence=0.90 -->
**Conjecture (Purity).** In the range of Table III, the LP bound for pure codes equals that for impure codes, and for several entries a code meeting the LP bound must be pure. Conjecture: let $K$ be the largest number (not necessarily integer) $>1$ for which polynomials $W,W^\perp,S$ exist as in the nonadditive Theorem LPW; then for any such solution $W(1,y)=1+O(y^d)$, i.e. the weight enumerator is pure. Together with a monotonicity result on solutions to Theorem LPW, this would imply equivalence of the pure and impure LP bounds for general (additive or nonadditive) codes.

<a id="pdf-4fa1f624d1c5-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->
The purity conjecture has been verified for all $n\le50$.

<a id="pdf-4fa1f624d1c5-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.90 -->
(xiii) Cases where the extremal $K$ is a power of 2, for $n\le45$ (Table: existence noted):
- **(a) $K=2$:** $((5,2,3))$ (Hamming), $((11,2,5))$ (dodecacode), $((17,2,7))$ (exists), $((23,2,9))$ (?), $((29,2,11))$ (QR code), $((35,2,13))$ (?), $((41,2,15))$ (?).
- **(b) two infinite families:** $((2m,2^{2m-2},2))$, $m\ge1$ (exist); $((n,2^{n-2m},3))$, $n=(4^m-1)/3$, $m\ge2$ (exist: Hamming).
- **(c) sporadic:** $((18,4096,3))$ (?, must be nonadditive), $((16,256,4))$ (?, nonadditive), $((17,512,4))$ (exists), $((22,2^{14},4))$ (?, nonadditive), $((27,2^{15},5))$ (?), $((28,2^{14},6))$ (?), $((40,64,13))$ (?).

<a id="pdf-4fa1f624d1c5-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.90 -->
Candidates with $K$ not a power of 2: the first is $((5,6,2))$ (found); an infinite $d=2$ family, none of which can exist [RainsQd2]. Remaining possibilities for $n\le45$: $((10,24,3))$, $((13,40,4))$, $((21,7168,4))$, $((24,49152,4))$, $((22,384,6))$, $((22,56,7))$, $((24,24,8))$, $((39,24,13))$. Elegant combinatorial constructions for any of these would be of interest.

<a id="pdf-4fa1f624d1c5-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.90 -->
**Remark (xiv).** Theorem SB2 listed all parameter sets $[[n,n-2d+2,d]]$ admitting an additive code, each unique. Extended to nonadditive codes [RainsQd2]: any $((2,1,2))$, $((4,4,2))$, $((5,2,3))$, $((6,1,4))$ code is equivalent to the unique additive $[[2,0,2]]$, $[[4,2,2]]$, $[[5,1,3]]$, $[[6,0,4]]$ code respectively. For all $n>2$, a nonadditive $((2n,2^{2n-2},2))$ code exists.

<a id="pdf-4fa1f624d1c5-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.85 -->
(xv) Narrative: an $8\times8$ orthogonal matrix group Shor investigated turned out identical to the order-5160960 symmetry group of a Grassmannian packing of 70 4-dim subspaces of $\mathbb{R}^8$; both are members of the real Clifford group family $L_R$ (Section 2; for $n=3$, $|L_R|=5160960$) central to [CCKS96]. Sidelnikov's [Sid2] orbit-code matrix group is these Clifford groups in another guise.

<a id="pdf-4fa1f624d1c5-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.95 -->
Thanks to A. Gulliver (quasi-cyclic codes, Section 5) and R. H. Hardin (search for nonadditive codes).

<a id="pdf-4fa1f624d1c5-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.90 -->
Reference list (bibliography) begins here — entries include Aschbacher, Aharonov–Ben-Or, Bennett et al., Bolt–Room–Wall, Bosma–Cannon (Magma), Brouwer–Sloane, Calderbank et al. ([CCKS96], [grass3], [CK86], [CLP95], [CRSS96], [CaSh96]), Cleve, Cleve–Gottesman, Conway–Hardin–Sloane, etc. Not summarized (no theorem content).

<a id="pdf-4fa1f624d1c5-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.97 -->
**References (bibliography).** Closing `thebibliography` list of ~54 cited works. No mathematical statements, definitions, theorems, or proofs are present. Topics of the cited literature include self-dual codes over GF(3)/GF(4), the theory of error-correcting codes, sphere packings and lattices, finite groups (ATLAS, Clifford/Sidelnikov groups), linear-programming bounds for codes, shadow bounds and weight enumerators, and quantum error-correcting codes (stabilizer/CSS codes, fault-tolerant computation, quantum MacWilliams identities, nonbinary and nonadditive quantum codes). Entries consist only of author, title, and publication data.
