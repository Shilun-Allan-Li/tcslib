<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 4bcdc0ee9c8634e05825d3671e9985485b0c7ade9dcd057de00f237a68ff8167 -->

<a id="pdf-4bcdc0ee9c86-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
# Nonbinary Stabilizer Codes over Finite Fields

Avanti Ketkar, Andreas Klappenecker, Santosh Kumar, Pradeep Kiran Sarvepalli (Texas A&M University, Dept. of Computer Science). Dedicated to the memory of Prof. Thomas Beth.

<a id="pdf-4bcdc0ee9c86-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Develops the basic theory of stabilizer codes over finite fields. Introduces a Galois theory relating stabilizer codes and general quantum codes; characterizes nonbinary stabilizer codes over $\F_q$ via classical codes over $\F_{q^2}$ (generalizing additive $\F_4$ codes). Derives lower/upper bounds on minimum distance, several constructions, and families (quantum Hamming, quadratic residue, Melas, BCH, character codes). Generalizes Rains's puncturing theory to additive codes not necessarily pure, and bounds the maximal length of MDS stabilizer codes.

<a id="pdf-4bcdc0ee9c86-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.93 -->
Motivates quantum error correction. Reviews binary and nonbinary stabilizer-code literature. Roadmap: §2 basics of nonbinary stabilizer codes; §3 Galois connection between quantum codes and groups (following Ore's lattice generalization of Galois theory); §4 correspondence of stabilizer codes over $\F_q$ with additive codes over $\F_q$ self-orthogonal under a trace-symplectic form, and with additive codes over $\F_{q^2}$ self-orthogonal under a trace-alternating form; §5 MacWilliams relations; §6 distance bounds; §7 cyclic codes; §§8–11 quantum Hamming/QR/Melas/BCH codes; §12 puncturing; §13 length bounds for MDS stabilizer codes (length $\le q^2+1$ except sporadic cases, under the classical MDS conjecture); §14 character codes; §15 further constructions and open problems.

<a id="pdf-4bcdc0ee9c86-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.97 -->
**Notations.** $\F_q$ is a finite field of characteristic $p$ ($q$ a prime power). Trace from $\F_{q^m}$ to $\F_q$: $\tr_{q^m/q}(x)=\sum_{k=0}^{m-1} x^{q^k}$ (subscripts omitted when $\F_q$ is the prime field). $Z(G)$ = center of group $G$; $C_G(S)$ = centralizer of $S\subseteq G$; $H\le G$ means $H$ is a subgroup; $\Tr(M)$ = trace (sum of diagonal entries) of a square matrix $M$.

<a id="pdf-4bcdc0ee9c86-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->
$\C^q$ is a $q$-dimensional complex space for a quantum system; $\ket{x}$ is a distinguished orthonormal basis indexed by $x\in\F_q$. A quantum error-correcting code $Q$ is a $K$-dimensional subspace of $\C^{q^n}=\C^q\otimes\cdots\otimes\C^q$. Errors are modeled by a basis $\mathcal{E}_n$ of the complex $q^n\times q^n$ matrices; a stabilizer code is a joint eigenspace of a subset of $\mathcal{E}_n$.

<a id="pdf-4bcdc0ee9c86-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Definition (Error Bases).** For $a,b\in\F_q$, unitary operators on $\C^q$: $X(a)\ket{x}=\ket{x+a}$ and $Z(b)\ket{x}=\omega^{\tr(bx)}\ket{x}$, where $\tr$ is the trace from $\F_q$ to $\F_p$ and $\omega=\exp(2\pi i/p)$ is a primitive $p$th root of unity.

<a id="pdf-4bcdc0ee9c86-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
**Definition.** $\mathcal{E}=\{X(a)Z(b)\mid a,b\in\F_q\}$. A set of $q^2$ unitary matrices is a *nice error basis* if: (a) it contains the identity; (b) the product of two members is a scalar multiple of another member; (c) $\Tr(A^\dagger B)=0$ for distinct $A,B$.

<a id="pdf-4bcdc0ee9c86-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.97 -->
**Lemma.** $\mathcal{E}=\{X(a)Z(b)\mid a,b\in\F_q\}$ is a nice error basis on $\C^q$.

<a id="pdf-4bcdc0ee9c86-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.96 -->
**Proof.** (a) $X(0)Z(0)=I$. (b) From $\omega^{\tr(ba)}X(a)Z(b)=Z(b)X(a)$ one gets the multiplication rule (Eq. 1): $X(a)Z(b)\,X(a')Z(b')=\omega^{\tr(ba')}X(a+a')Z(b+b')$, a scalar multiple of an element of $\mathcal{E}$. (c) For $A=X(a)Z(b)$, $B=X(a)Z(b')$: $\Tr(A^\dagger B)=\Tr(Z(b'-b))=\sum_{x\in\F_q}\omega^{\tr((b'-b)x)}$, which is $0$ unless the additive character is trivial, i.e. $b'\ne b$. For $a\ne a'$, $A^\dagger B=Z(-b)X(a'-a)Z(b')$ has zero diagonal, so $\Tr(A^\dagger B)=0$. Hence (c) holds for distinct elements. $\square$

<a id="pdf-4bcdc0ee9c86-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.95 -->
**Example.** For $q=4$, $\F_4=\{0,1,\alpha,\overline{\alpha}\}$ with basis $\ket{0},\ket{1},\ket{\alpha},\ket{\overline{\alpha}}$ of $\C^4$. Using $\idtwo$, $\sigma_x=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, $\sigma_z=\left(\begin{smallmatrix}1&0\\0&-1\end{smallmatrix}\right)$: $X(0)=\idtwo\otimes\idtwo$, $X(1)=\idtwo\otimes\sigma_x$, $X(\alpha)=\sigma_x\otimes\idtwo$, $X(\overline{\alpha})=\sigma_x\otimes\sigma_x$; $Z(0)=\idtwo\otimes\idtwo$, $Z(1)=\sigma_z\otimes\idtwo$, $Z(\alpha)=\sigma_z\otimes\sigma_z$, $Z(\overline{\alpha})=\idtwo\otimes\sigma_z$. This basis is a tensor product of the Pauli basis on $\C^2$.

<a id="pdf-4bcdc0ee9c86-p002-b008"></a>
<!-- pdf-source: page=2; block=8; confidence=0.96 -->
**Lemma.** If $\mathcal{E}_1,\mathcal{E}_2$ are nice error bases, then $\mathcal{E}=\{E_1\otimes E_2\mid E_1\in\mathcal{E}_1, E_2\in\mathcal{E}_2\}$ is a nice error basis. (Proof follows directly from the definitions.)

<a id="pdf-4bcdc0ee9c86-p002-b009"></a>
<!-- pdf-source: page=2; block=9; confidence=0.96 -->
For $\mathbf{a}=(a_1,\dots,a_n)\in\F_q^n$: $X(\mathbf{a})=X(a_1)\otimes\cdots\otimes X(a_n)$ and $Z(\mathbf{a})=Z(a_1)\otimes\cdots\otimes Z(a_n)$, modeling errors acting locally on single systems.

<a id="pdf-4bcdc0ee9c86-p002-b010"></a>
<!-- pdf-source: page=2; block=10; confidence=0.97 -->
**Corollary (th:nice).** $\mathcal{E}_n=\{X(\mathbf{a})Z(\mathbf{b})\mid \mathbf{a},\mathbf{b}\in\F_q^n\}$ is a nice error basis on $\C^{q^n}$.

<a id="pdf-4bcdc0ee9c86-p002-b011"></a>
<!-- pdf-source: page=2; block=11; confidence=0.93 -->
**Remark.** Equivalent error bases appear in prior work; $Z(b)$ is defined here slightly differently to make stabilizer-relevant properties transparent, avoiding an intermediate tensoring of $p\times p$ matrices and yielding the trace-symplectic form directly (cf. Lemma th:commute).

<a id="pdf-4bcdc0ee9c86-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.97 -->
**Definition.** $G_n$ is the group generated by $\mathcal{E}_n$; by the multiplication rule (Eq. 1), $G_n=\{\omega^{c}X(\mathbf{a})Z(\mathbf{b})\mid \mathbf{a},\mathbf{b}\in\F_q^n,\ c\in\F_p\}$, a finite group of order $pq^{2n}$, called the *error group* of $\mathcal{E}_n$.

<a id="pdf-4bcdc0ee9c86-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
**Definition.** A *stabilizer code* $Q$ is a non-zero subspace of $\C^{q^n}$ with $Q=\bigcap_{E\in S}\{v\in\C^{q^n}\mid Ev=v\}$ (Eq. 2) for some subgroup $S\le G_n$; i.e. the joint eigenspace of eigenvalue $1$ of $S$.

<a id="pdf-4bcdc0ee9c86-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.94 -->
**Remark.** A stabilizer code must contain *all* joint eigenvectors of $S$ with eigenvalue $1$; a strictly smaller subspace is not a stabilizer code for $S$.

<a id="pdf-4bcdc0ee9c86-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.94 -->
**Detectability.** $Q$ detects an error $E\in U(q^n)$ iff $\langle c_1|E|c_2\rangle=\lambda_E\langle c_1|c_2\rangle$ for all $c_1,c_2\in Q$. A stabilizer code with stabilizer $S$ detects all errors in $G_n$ that are scalar multiples of elements of $S$ or that fail to commute with some element of $S$ (Lemma th:detectable); a non-detectable error in $G_n$ commutes with all of $S$.

<a id="pdf-4bcdc0ee9c86-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.97 -->
**Lemma (th:commute).** For $E=\omega^cX(\mathbf{a})Z(\mathbf{b})$ and $E'=\omega^{c'}X(\mathbf{a'})Z(\mathbf{b'})$ in $G_n$: $EE'=\omega^{\tr(\mathbf{b\cdot a'-b'\cdot a})}E'E$. Thus $E,E'$ commute iff the trace-symplectic form $\tr(\mathbf{b\cdot a'-b'\cdot a})$ vanishes.

<a id="pdf-4bcdc0ee9c86-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.96 -->
**Proof.** By Eq. 1, $EE'=\omega^{\tr(\mathbf{b\cdot a'})}X(\mathbf{a+a'})Z(\mathbf{b+b'})$ and $E'E=\omega^{\tr(\mathbf{b'\cdot a})}X(\mathbf{a+a'})Z(\mathbf{b+b'})$; multiplying $E'E$ by $\omega^{\tr(\mathbf{b\cdot a'-b'\cdot a})}$ gives $EE'$. $\square$

<a id="pdf-4bcdc0ee9c86-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.97 -->
**Definition.** Symplectic weight of $(\mathbf{a}|\mathbf{b})\in\F_q^{2n}$: $\swt((\mathbf{a}|\mathbf{b}))=|\{k\mid(a_k,b_k)\ne(0,0)\}|$. The weight of $E=\omega^cX(\mathbf{a})Z(\mathbf{b})\in G_n$ is $\w(E)=\swt((\mathbf{a}|\mathbf{b}))$ (number of nonidentity tensor components); a scalar multiple of the identity has weight $0$.

<a id="pdf-4bcdc0ee9c86-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.96 -->
**Definition.** $Q$ has *minimum distance* $d$ iff it detects all errors in $G_n$ of weight $<d$ but not some error of weight $d$. $Q$ is an $((n,K,d))_q$ code if it is a $K$-dimensional subspace of $\C^{q^n}$ with minimum distance $d$; an $((n,q^k,d))_q$ code is also written $[[n,k,d]]_q$.

<a id="pdf-4bcdc0ee9c86-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.95 -->
**Definition.** $Q$ is *pure to* $t$ iff its stabilizer $S$ contains no non-scalar matrices of weight $<t$; $Q$ is *pure* iff pure to its minimum distance. An $[[n,0,d]]_q$ code is assumed pure. Remark: a code detecting a set $\mathcal{D}$ detects its linear span; a code of distance $d$ corrects all errors of weight $\le t=\lfloor(d-1)/2\rfloor$.

<a id="pdf-4bcdc0ee9c86-p003-b010"></a>
<!-- pdf-source: page=3; block=10; confidence=0.94 -->
$\mathcal{Q}$ = set of all subspaces of $\C^{q^n}$, ordered by inclusion, with $\sup\{Q,Q'\}=Q+Q'$ and $\inf\{Q,Q'\}=Q\cap Q'$; thus $\mathcal{Q}$ is a complete lattice. $\mathcal{G}$ = lattice of subgroups of $G_n$. Two order-reversing maps between $\mathcal{G}$ and $\mathcal{Q}$ form a Galois connection, with stabilizer codes the elements of $\mathcal{Q}$ fixed by the round trip.

<a id="pdf-4bcdc0ee9c86-p003-b011"></a>
<!-- pdf-source: page=3; block=11; confidence=0.97 -->
**Definition.** $\Fix(S)=\bigcap_{E\in S}\{v\in\C^{q^n}\mid Ev=v\}$ (Eq. Fix), and $\Stab(Q)=\{E\in G_n\mid Ev=v\ \forall v\in Q\}$ (Eq. Stab).

<a id="pdf-4bcdc0ee9c86-p003-b012"></a>
<!-- pdf-source: page=3; block=12; confidence=0.96 -->
**Properties.** G1: $Q_1\subseteq Q_2\Rightarrow\Stab(Q_2)\le\Stab(Q_1)$. G2: $S_1\le S_2\Rightarrow\Fix(S_2)\le\Fix(S_1)$. G3: $Q\subseteq\Fix(\Stab(Q))$. G4: $S\le\Stab(\Fix(S))$. G1–G2 give order-reversal; G3–G4 give the extension property, so $\Fix,\Stab$ form a Galois connection. Consequently $\Fix(S)=\Fix(\Stab(\Fix(S)))$ and $\Stab(Q)=\Stab(\Fix(\Stab(Q)))$ for all $S\in\mathcal{G}$, $Q\in\mathcal{Q}$.

<a id="pdf-4bcdc0ee9c86-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->
**Definition.** A subspace $Q$ of $\mathbb{C}^{q^n}$ satisfying G3 with equality is a *closed subspace*; a subgroup $S$ of the error group $G_n$ satisfying G4 with equality is a *closed subgroup*.

<a id="pdf-4bcdc0ee9c86-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.97 -->
**Proposition.** The closed subspaces of $\mathbb{C}^{q^n}$ form a complete sublattice $\mathcal{Q}_c$ of $\mathcal{Q}$. The closed subgroups of $G_n$ form a complete sublattice $\mathcal{G}_c$ of $\mathcal{G}$ that is dual isomorphic to $\mathcal{Q}_c$.

<a id="pdf-4bcdc0ee9c86-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.97 -->
**Proof.** Holds for any Galois connection; see Birkhoff, Theorem 10 (p. 56).

<a id="pdf-4bcdc0ee9c86-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.97 -->
**Lemma.** A closed subspace is a stabilizer code or is 0-dimensional.

<a id="pdf-4bcdc0ee9c86-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.96 -->
**Proof.** A closed subspace satisfies $Q=\mathrm{Fix}(\mathrm{Stab}(Q))=\bigcap_{E\in\mathrm{Stab}(Q)}\{v\in\mathbb{C}^{q^n}\mid Ev=v\}$, hence is a stabilizer code or $\{0\}$.

<a id="pdf-4bcdc0ee9c86-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.97 -->
**Lemma (th:stab).** If $Q$ is a nonzero subspace of $\mathbb{C}^{q^n}$, then its stabilizer $S=\mathrm{Stab}(Q)$ is an abelian group satisfying $S\cap Z(G_n)=\{1\}$.

<a id="pdf-4bcdc0ee9c86-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.10 -->
**Proof.** If $E,E'\in S$ do not commute then $EE'=\omega^k E'E$ with $\omega^k\neq1$ (Lemma th:commute); a nonzero $v\in Q$ would give $v=EE'v=\omega^k E'Ev=\omega^k v$, a contradiction, so $S$ is abelian. $S$ can contain $\omega^k\mathbb{1}$ only if $k=0$, giving $S\cap Z(G_n)=\{1\}$.

<a id="pdf-4bcdc0ee9c86-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.97 -->
**Lemma (th:projection).** If $S$ is the stabilizer of a vector space $Q$, an orthogonal projector onto the joint eigenspace $\mathrm{Fix}(S)$ is $P=\frac{1}{|S|}\sum_{E\in S}E$.

<a id="pdf-4bcdc0ee9c86-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.96 -->
**Proof.** $v\in\mathrm{Fix}(S)\Rightarrow Pv=v$, so $\mathrm{Fix}(S)\subseteq\mathrm{im}\,P$; and $EP=P$ for all $E\in S$ makes every image vector a common eigenvector with eigenvalue $1$, so $\mathrm{Fix}(S)=\mathrm{im}\,P$. $P$ is idempotent: $P^2=\frac{1}{|S|}\sum_{E\in S}EP=\frac{1}{|S|}\sum_{E\in S}P=P$. Since $E^\dagger\in S$, $P^\dagger=P$; hence $P$ is an orthogonal projector onto $\mathrm{Fix}(S)$.

<a id="pdf-4bcdc0ee9c86-p004-b010"></a>
<!-- pdf-source: page=4; block=10; confidence=0.95 -->
**Remark.** If $S$ is a nonabelian subgroup of $G_n$ it necessarily contains $Z(G_n)$, and then $P$ is the all-zero matrix. The image of $P$ has dimension $\mathrm{Tr}(P)=q^n/|S|$.

<a id="pdf-4bcdc0ee9c86-p004-b011"></a>
<!-- pdf-source: page=4; block=11; confidence=0.97 -->
**Lemma (th:closedsubgroup).** A subgroup $S\le G_n$ is closed if and only if $S$ is an abelian subgroup with $S\cap Z(G_n)=\{1\}$, or $S=G_n$.

<a id="pdf-4bcdc0ee9c86-p004-b012"></a>
<!-- pdf-source: page=4; block=12; confidence=0.95 -->
**Proof.** If $S$ is closed, $Q=\mathrm{Fix}(S)$ is a stabilizer code or 0-dimensional; $\mathrm{Stab}(\{0\})=G_n$, and if $Q\neq\{0\}$ then $\mathrm{Stab}(Q)=S$ is abelian with $S\cap Z(G_n)=\{\mathbb{1}\}$ (Lemma th:stab). Conversely, for abelian $S$ with $S\cap Z(G_n)=\{1\}$, set $S^*=\mathrm{Stab}(\mathrm{Fix}(S))$; then $\mathrm{Fix}(S^*)=\mathrm{Fix}(S)$ (Galois connection), and by Lemma th:projection $q^n/|S^*|=\mathrm{Tr}\!\left(\frac{1}{|S^*|}\sum_{E\in S^*}E\right)=\mathrm{Tr}\!\left(\frac{1}{|S|}\sum_{E\in S}E\right)=q^n/|S|$. With $S\le S^*$ this gives $S=S^*=\mathrm{Stab}(\mathrm{Fix}(S))$, so $S$ is closed. Also $\mathrm{Fix}(G_n)=\{0\}$, so $G_n$ is closed.

<a id="pdf-4bcdc0ee9c86-p004-b013"></a>
<!-- pdf-source: page=4; block=13; confidence=0.95 -->
**Fact.** An arbitrary quantum code $Q$ is contained in the stabilizer code $Q^*=\mathrm{Fix}(\mathrm{Stab}(Q))$. Any error detectable by $Q^*$ is detectable by $Q$; hence if $Q^*$ has minimum distance $d$, then $Q$ has minimum distance at least $d$.

<a id="pdf-4bcdc0ee9c86-p004-b014"></a>
<!-- pdf-source: page=4; block=14; confidence=0.93 -->
**Section — Additive Codes.** Relates stabilizer codes to classical additive codes over $\mathbb{F}_q$ (or $\mathbb{F}_{q^2}$), which characterize the errors in $G_n$ detectable by a stabilizer code.

<a id="pdf-4bcdc0ee9c86-p004-b015"></a>
<!-- pdf-source: page=4; block=15; confidence=0.95 -->
**Definition.** For $S\le G_n$, the centralizer is $C_{G_n}(S)=\{E\in G_n\mid EF=FE\text{ for all }F\in S\}$, and $SZ(G_n)$ is the group generated by $S$ and the center $Z(G_n)$.

<a id="pdf-4bcdc0ee9c86-p004-b016"></a>
<!-- pdf-source: page=4; block=16; confidence=0.97 -->
**Lemma (th:detectable).** Let $S\le G_n$ be the stabilizer of a stabilizer code $Q$ with $\dim Q>1$. An error $E\in G_n$ is detectable by $Q$ if and only if either $E\in SZ(G_n)$ or $E\notin C_{G_n}(S)$.

<a id="pdf-4bcdc0ee9c86-p004-b017"></a>
<!-- pdf-source: page=4; block=17; confidence=0.94 -->
**Proof.** If $E\in SZ(G_n)$, then $E$ is a scalar multiple of a stabilizer, acting as multiplication by a scalar $\lambda_E$ on $Q$, hence detectable. If $E$ fails to commute with some $F\in S$, then $EF=\lambda FE$ with $\lambda\neq1$ (Lemma th:commute), and for all $u,v\in Q$,
$$\langle u|E|v\rangle=\langle u|EF|v\rangle=\lambda\langle u|FE|v\rangle=\lambda\langle u|E|v\rangle\quad(\text{eq. noncommute}),$$
so $\langle u|E|v\rangle=0$ and $E$ is detectable. (Continued on page 5.)

<a id="pdf-4bcdc0ee9c86-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.94 -->
**Proof (continued).** For $E\in C_{G_n}(S)\setminus SZ(G_n)$, suppose $E$ detectable, so $Ev=\lambda_E v$ for all $v\in Q$. Then $\lambda_E\neq0$, since $E$ commutes with $S$ gives $EP=PEP=\lambda_E P\neq0$. Let $S^*$ be the abelian group generated by $\lambda_E^{-1}E$ and $S$; its eigenvalue-$1$ joint eigenspace has dimension $q^n/|S^*|<\dim Q=q^n/|S|$, so not all $v\in Q$ are invariant under $\lambda_E^{-1}E$, contradicting detectability.

<a id="pdf-4bcdc0ee9c86-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.96 -->
**Corollary.** If a stabilizer code $Q$ has minimum distance $d$ and is pure to $t$, then every $E\in G_n$ with $1\le\mathrm{wt}(E)<\min\{t,d\}$ satisfies $\langle u|E|v\rangle=0$ for all $u,v\in Q$.

<a id="pdf-4bcdc0ee9c86-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
**Proof.** Since $\mathrm{wt}(E)<d$, $E$ is detectable; purity to $t>\mathrm{wt}(E)$ gives $E\notin Z(G_n)S$, hence $E\notin C_{G_n}(S)$, and the claim follows from eq. noncommute.

<a id="pdf-4bcdc0ee9c86-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.94 -->
**Codes over $\mathbb{F}_q$.** Detectability is phase-independent ($E$ detectable iff $\omega E$ detectable). Associating $\omega^cX(\mathbf{a})Z(\mathbf{b})\in G_n$ with $(\mathbf{a}|\mathbf{b})\in\mathbb{F}_q^{2n}$ maps $SZ(G_n)$ to the additive code $C=\{(\mathbf{a}|\mathbf{b})\mid\omega^cX(\mathbf{a})Z(\mathbf{b})\in SZ(G_n)\}=SZ(G_n)/Z(G_n)$. The trace-symplectic form is $\langle(\mathbf{a}|\mathbf{b})\,|\,(\mathbf{a}'|\mathbf{b}')\rangle_s=\mathrm{tr}_{q/p}(\mathbf{b}\cdot\mathbf{a}'-\mathbf{b}'\cdot\mathbf{a})$. The centralizer $C_{G_n}(S)$ maps onto the trace-symplectic dual $C^{\perp_s}=\{(\mathbf{a}|\mathbf{b})\mid\omega^cX(\mathbf{a})Z(\mathbf{b})\in C_{G_n}(S)\}$.

<a id="pdf-4bcdc0ee9c86-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.97 -->
**Theorem (th:stabilizer).** An $((n,K,d))_q$ stabilizer code exists if and only if there exists an additive code $C\le\mathbb{F}_q^{2n}$ with $|C|=q^n/K$ such that $C\le C^{\perp_s}$ and $\mathrm{swt}(C^{\perp_s}\setminus C)=d$ if $K>1$ (and $\mathrm{swt}(C^{\perp_s})=d$ if $K=1$).

<a id="pdf-4bcdc0ee9c86-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.93 -->
**Proof.** ($\Rightarrow$) An $((n,K,d))_q$ code $Q$ yields a closed subgroup $S$ with $|S|=q^n/K$, $Q=\mathrm{Fix}(S)$, $S$ abelian, $S\cap Z(G_n)=1$ (Lemma th:closedsubgroup). Then $C\cong SZ(G_n)/Z(G_n)$ is additive with $|C|=q^n/K$, and $C^{\perp_s}=C_{G_n}(S)/Z(G_n)$; abelian $S$ gives $SZ(G_n)\le C_{G_n}(S)$, so $C\le C^{\perp_s}$. The weight of $\omega^cX(\mathbf{a})Z(\mathbf{b})$ equals $\mathrm{swt}(\mathbf{a}|\mathbf{b})$: if $K=1$, $Q$ is pure so $\mathrm{swt}(C^{\perp_s})=d$; if $K>1$, elements of $C_{G_n}(S)\setminus SZ(G_n)$ have weight $\ge d$ (Lemma th:detectable), giving $\mathrm{swt}(C^{\perp_s}\setminus C)=d$.
($\Leftarrow$) Given such $C$, set $N=\{\omega^cX(\mathbf{a})Z(\mathbf{b})\mid c\in\mathbb{F}_p,\,(\mathbf{a}|\mathbf{b})\in C\}$, an abelian normal subgroup (pre-image of $C=N/Z(G_n)$). Pick a character $\chi$ of $N$ with $\chi(\omega^c\mathbb{1})=\omega^c$; then $P_N=\frac{1}{|N|}\sum_{E\in N}\chi(E^{-1})E$ is an orthogonal projector onto a space $Q$ (idempotent in $\mathbb{C}[G_n]$), with $\dim Q=\mathrm{Tr}\,P_N=|Z(G_n)|q^n/|N|=q^n/|C|=K$. Each coset of $N$ mod $Z(G_n)$ contains one $E$ fixing $Q$; $S=\{E\in N\mid Ev=v\ \forall v\in Q\}$ is abelian with $|S|=q^n/K$ and $Q=\mathrm{Fix}(S)$. An element of $C_{G_n}(S)\setminus SZ(G_n)$ cannot have weight $<d$ (else $(\mathbf{a}|\mathbf{b})\in C^{\perp_s}\setminus C$ would), and if $K=1$ all nonidentity elements of $C_{G_n}(S)$ have weight $\ge d$; so $Q$ is an $((n,K,d))_q$ stabilizer code.

<a id="pdf-4bcdc0ee9c86-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.90 -->
**Codes over $\mathbb{F}_{q^2}$.** Motivates replacing the unusual symplectic weight by the Hamming weight via additive codes over $\mathbb{F}_{q^2}$, generalizing the binary $\mathbb{F}_4$ construction of Calderbank et al.; cites prior partial approaches and an alternative symplectic-form approach due to Barnum.

<a id="pdf-4bcdc0ee9c86-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.96 -->
**Definition (trace-alternating form).** With $(\beta,\beta^q)$ a normal basis of $\mathbb{F}_{q^2}/\mathbb{F}_q$, for $v,w\in\mathbb{F}_{q^2}^n$:
$$\langle v|w\rangle_a=\mathrm{tr}_{q/p}\!\left(\frac{v\cdot w^q-v^q\cdot w}{\beta^{2q}-\beta^2}\right)\quad(\text{eq. alternating}).$$
The argument is invariant under $x\mapsto x^q$, hence lies in $\mathbb{F}_q$, so the form is well-defined.

<a id="pdf-4bcdc0ee9c86-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->
**Properties.** The trace-alternating form is bi-additive, $\mathbb{F}_p$-linear (not $\mathbb{F}_q$-linear unless $q=p$), and alternating ($\langle u|u\rangle_a=0$ for all $u$). Write $u\perp_a w$ iff $\langle u|w\rangle_a=0$.

<a id="pdf-4bcdc0ee9c86-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.95 -->
**Definition (map $\phi$).** The bijection $\phi:\mathbb{F}_q^{2n}\to\mathbb{F}_{q^2}^n$, $\phi((\mathbf{a}|\mathbf{b}))=\beta\mathbf{a}+\beta^q\mathbf{b}$, is isometric: the symplectic weight of $(\mathbf{a}|\mathbf{b})$ equals the Hamming weight of $\phi((\mathbf{a}|\mathbf{b}))$.

<a id="pdf-4bcdc0ee9c86-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.97 -->
**Lemma (th:isometry).** For $c,d\in\mathbb{F}_q^{2n}$, $\langle c|d\rangle_s=\langle\phi(c)|\phi(d)\rangle_a$. In particular $c\perp_s d$ iff $\phi(c)\perp_a\phi(d)$.

<a id="pdf-4bcdc0ee9c86-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.95 -->
**Proof.** With $c=(\mathbf{a}|\mathbf{b})$, $d=(\mathbf{a}'|\mathbf{b}')$:
$$\phi(c)\cdot\phi(d)^q=\beta^{q+1}\mathbf{a}\cdot\mathbf{a}'+\beta^{2}\mathbf{a}\cdot\mathbf{b}'+\beta^{2q}\mathbf{b}\cdot\mathbf{a}'+\beta^{q+1}\mathbf{b}\cdot\mathbf{b}',$$
$$\phi(c)^q\cdot\phi(d)=\beta^{q+1}\mathbf{a}\cdot\mathbf{a}'+\beta^{2q}\mathbf{a}\cdot\mathbf{b}'+\beta^{2}\mathbf{b}\cdot\mathbf{a}'+\beta^{q+1}\mathbf{b}\cdot\mathbf{b}'.$$
Hence $\langle\phi(c)|\phi(d)\rangle_a=\mathrm{tr}_{q/p}(\mathbf{b}\cdot\mathbf{a}'-\mathbf{a}\cdot\mathbf{b}')=\langle c|d\rangle_s$.

<a id="pdf-4bcdc0ee9c86-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.97 -->
**Theorem (th:alternating).** An $((n,K,d))_q$ stabilizer code exists if and only if there exists an additive subcode $D\le\mathbb{F}_{q^2}^n$ with $|D|=q^n/K$ such that $D\le D^{\perp_a}$ and $\mathrm{wt}(D^{\perp_a}\setminus D)=d$ if $K>1$ (and $\mathrm{wt}(D^{\perp_a})=d$ if $K=1$).

<a id="pdf-4bcdc0ee9c86-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.96 -->
**Proof.** Apply the isometry $\phi$ to Theorem th:stabilizer.

<a id="pdf-4bcdc0ee9c86-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.90 -->
**Corollary 16.** If there exists a classical $[n,k]_{q^2}$ additive code $D\le\mathbb{F}_{q^2}$ such that $D\le D^{\perp_a}$ and $d^{\perp_a}=\mathrm{wt}(D^{\perp_a})$, then there exists an $[[n,n-2k,\ge d^{\perp_a}]]_q$ stabilizer code that is pure to $d^{\perp_a}$.

<a id="pdf-4bcdc0ee9c86-p006-b009"></a>
<!-- pdf-source: page=6; block=9; confidence=0.94 -->
**Remark.** A normal basis is not required. With a polynomial basis $(1,\gamma)$ of $\mathbb{F}_{q^2}/\mathbb{F}_q$ one may set $\phi((\mathbf{a}|\mathbf{b}))=\mathbf{a}+\gamma\mathbf{b}$ and use $\langle v|w\rangle_{a'}=\mathrm{tr}_{q/p}\!\left(\frac{v\cdot w^q-v^q\cdot w}{\gamma-\gamma^q}\right)$; Lemma th:isometry still holds.

<a id="pdf-4bcdc0ee9c86-p006-b010"></a>
<!-- pdf-source: page=6; block=10; confidence=0.94 -->
**Classical codes.** Relates trace-alternating self-orthogonality to euclidean/hermitian orthogonality. The hermitian inner product of $\mathbf{x},\mathbf{y}\in\mathbb{F}_{q^2}^n$ is $\mathbf{x}^q\cdot\mathbf{y}$; write $\mathbf{x}\perp_h\mathbf{y}$ iff $\mathbf{x}^q\cdot\mathbf{y}=0$.

<a id="pdf-4bcdc0ee9c86-p006-b011"></a>
<!-- pdf-source: page=6; block=11; confidence=0.96 -->
**Lemma (th:hermitian).** If $\mathbf{x}\perp_h\mathbf{y}$ then $\mathbf{x}\perp_a\mathbf{y}$. In particular, for $D\le\mathbb{F}_{q^2}^n$, $D^{\perp_h}\le D^{\perp_a}$.

<a id="pdf-4bcdc0ee9c86-p006-b012"></a>
<!-- pdf-source: page=6; block=12; confidence=0.95 -->
**Proof.** $\mathbf{x}^q\cdot\mathbf{y}=0$ implies $\mathbf{x}\cdot\mathbf{y}^q=0$, whence $\langle\mathbf{x}|\mathbf{y}\rangle_a=\mathrm{tr}_{q/p}\!\left(\frac{\mathbf{x}\cdot\mathbf{y}^q-\mathbf{x}^q\cdot\mathbf{y}}{\beta^{2q}-\beta^2}\right)=0$.

<a id="pdf-4bcdc0ee9c86-p006-b013"></a>
<!-- pdf-source: page=6; block=13; confidence=0.93 -->
Thus every hermitian self-orthogonal code is trace-alternating self-orthogonal. In general $D^{\perp_h}$ and $D^{\perp_a}$ differ, but they coincide when $D$ is $\mathbb{F}_{q^2}$-linear.

<a id="pdf-4bcdc0ee9c86-p006-b014"></a>
<!-- pdf-source: page=6; block=14; confidence=0.97 -->
**Lemma (th:classical).** If $D\le\mathbb{F}_{q^2}^n$ is $\mathbb{F}_{q^2}$-linear, then $D^{\perp_h}=D^{\perp_a}$.

<a id="pdf-4bcdc0ee9c86-p006-b015"></a>
<!-- pdf-source: page=6; block=15; confidence=0.95 -->
**Proof.** Let $q=p^m$ with $p$ prime. If $D$ is $k$-dimensional over $\mathbb{F}_{q^2}$, then $D^{\perp_h}$ is $(n-k)$-dimensional. Viewing $D$ as a $2mk$-dimensional subspace of $\mathbb{F}_p^{2mn}$ and $D^{\perp_a}$ as $2m(n-k)$-dimensional; since $D^{\perp_h}\subseteq D^{\perp_a}$ and the two have equal cardinality, $D^{\perp_a}=D^{\perp_h}$.

<a id="pdf-4bcdc0ee9c86-p006-b016"></a>
<!-- pdf-source: page=6; block=16; confidence=0.95 -->
**Corollary (co:classical).** If there exists an $\mathbb{F}_{q^2}$-linear $[n,k,d]_{q^2}$ code $B$ with $B^{\perp_h}\le B$, then there exists an $[[n,2k-n,\ge d]]_q$ quantum code that is pure to $d$.

<a id="pdf-4bcdc0ee9c86-p006-b017"></a>
<!-- pdf-source: page=6; block=17; confidence=0.94 -->
**Proof.** The hermitian product is nondegenerate, so $D:=B^{\perp_h}$ has hermitian dual $B$. The $[n,n-k]_{q^2}$ code $D$ is $\mathbb{F}_{q^2}$-linear, so $D^{\perp_h}=D^{\perp_a}$ (Lemma th:classical); the claim then follows from Corollary co:alternating.

<a id="pdf-4bcdc0ee9c86-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->
Hermitian forms suffice for $\mathbb{F}_{q^2}$-linear codes; the trace-alternating form is needed for additive codes not linear over $\mathbb{F}_{q^2}$. Introduces the CSS code construction (Calderbank–Shor 1996, Steane 1996) as the most direct link to classical coding theory.

<a id="pdf-4bcdc0ee9c86-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.98 -->
**Lemma (CSS Code Construction, th:css).** Let $C_1,C_2$ be classical linear codes with parameters $[n,k_1,d_1]_q$ and $[n,k_2,d_2]_q$ such that $C_2^\perp\le C_1$. Then there exists an $[[n,k_1+k_2-n,d]]_q$ stabilizer code with minimum distance $d=\min\{\mathrm{wt}(c)\mid c\in(C_1\setminus C_2^\perp)\cup(C_2\setminus C_1^\perp)\}$ that is pure to $\min\{d_1,d_2\}$.

<a id="pdf-4bcdc0ee9c86-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->
**Proof.** Set $C=C_1^\perp\times C_2^\perp\le\mathbb{F}_q^{2n}$. For $(c_1\mid c_2),(c_1'\mid c_2')\in C$, $\mathrm{tr}(c_2\cdot c_1'-c_2'\cdot c_1)=\mathrm{tr}(0-0)=0$, so $C\le C^{\perp s}$ (trace-symplectic self-orthogonal). The trace-symplectic dual contains $C_2\times C_1$, and a dimension count gives $C^{\perp s}=C_2\times C_1$. Since $|C|=q^{2n-(k_1+k_2)}$, the stabilizer code has dimension $q^{k_1+k_2-n}$ by the stabilizer theorem (th:stabilizer). Minimum distance and purity are immediate from the construction.

<a id="pdf-4bcdc0ee9c86-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.98 -->
**Corollary (th:css2).** If $C$ is a classical linear $[n,k,d]_q$ code containing its dual, $C^\perp\le C$, then there exists an $[[n,2k-n,\ge d]]_q$ stabilizer code that is pure to $d$.

<a id="pdf-4bcdc0ee9c86-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.99 -->
**Section — Weight Enumerators.**

<a id="pdf-4bcdc0ee9c86-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.10 -->
**Definition.** For an $((n,K))_q$ quantum code $Q$ with orthogonal projector $P$, the Shor–Laflamme weight enumerators are $\sum_{i=0}^n A_i^{\textsc{sl}}z^i$ and $\sum_{i=0}^n B_i^{\textsc{sl}}z^i$ with
$$A_i^{\textsc{sl}}=\frac{1}{K^2}\sum_{E\in G_n,\,\mathrm{wt}(E)=i}\mathrm{Tr}(E^\dagger P)\mathrm{Tr}(EP),\qquad B_i^{\textsc{sl}}=\frac{1}{K}\sum_{E\in G_n,\,\mathrm{wt}(E)=i}\mathrm{Tr}(E^\dagger P E P).$$
For the additive code $C\le\mathbb{F}_q^{2n}$ associated with $Q$, the symplectic weight enumerators are given by $A_i=|\{c\in C\mid \mathrm{swt}(c)=i\}|$ and $B_i=|\{c\in C^{\perp s}\mid \mathrm{swt}(c)=i\}|$.

<a id="pdf-4bcdc0ee9c86-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.97 -->
**Lemma.** The Shor–Laflamme weights of an $((n,K))_q$ stabilizer code $Q$ satisfy $A_i^{\textsc{sl}}=pA_i$ and $B_i^{\textsc{sl}}=pB_i$ for $0\le i\le n$, where $p=\mathrm{char}\,\mathbb{F}_q$.

<a id="pdf-4bcdc0ee9c86-p007-b008"></a>
<!-- pdf-source: page=7; block=8; confidence=0.10 -->
**Proof.** With $P=\frac{1}{|S|}\sum_{E\in S}E$ for the stabilizer group $S$, $\mathrm{Tr}(EP)\neq0$ iff $E^\dagger\in SZ(G_n)$; when so, $\mathrm{Tr}(E^\dagger P)\mathrm{Tr}(EP)=(q^n/|S|)^2=K^2$. Hence $A_i^{\textsc{sl}}$ counts weight-$i$ elements of $SZ(G_n)$: $A_i^{\textsc{sl}}=|Z(G_n)|\cdot|\{c\in C\mid\mathrm{swt}(c)=i\}|=pA_i$. If $E$ commutes with all of $S$ then $\mathrm{Tr}(E^\dagger PEP)=\mathrm{Tr}(P^2)=\mathrm{Tr}(P)=K$; otherwise $E$ is detectable and $PEP=0$ (proof of th:detectable), so $\mathrm{Tr}(E^\dagger PEP)=0$. Thus $B_i^{\textsc{sl}}$ counts weight-$i$ elements of $C_{G_n}(S)$, giving $B_i^{\textsc{sl}}=|Z(G_n)|\cdot|\{c\in C^{\perp s}\mid\mathrm{swt}(c)=i\}|=pB_i$.

<a id="pdf-4bcdc0ee9c86-p007-b009"></a>
<!-- pdf-source: page=7; block=9; confidence=0.93 -->
SL enumerators of arbitrary quantum codes obey a MacWilliams identity (rains98, shor97); for stabilizer codes the symplectic enumerators $A(z)=\sum_i A_i z^i$ and $B(z)=\sum_i B_i z^i$ can be related directly, in the spirit of MacWilliams' original proof for euclidean dual codes.

<a id="pdf-4bcdc0ee9c86-p007-b010"></a>
<!-- pdf-source: page=7; block=10; confidence=0.98 -->
**Theorem.** Let $C$ be an additive subcode of $\mathbb{F}_q^{2n}$ with symplectic weight enumerator $A(z)$. Then the symplectic weight enumerator of $C^{\perp s}$ is
$$B(z)=\frac{(1+(q^2-1)z)^n}{|C|}\,A\!\left(\frac{1-z}{1+(q^2-1)z}\right).$$

<a id="pdf-4bcdc0ee9c86-p007-b011"></a>
<!-- pdf-source: page=7; block=11; confidence=0.94 -->
**Proof.** Let $\chi$ be a nontrivial additive character of $\mathbb{F}_p$; for $b\in\mathbb{F}_q^{2n}$ define $\chi_b(c)=\chi(\langle c\mid b\rangle_s)$ on $C$ via the trace-symplectic form. Then $\chi_b$ is trivial iff $b\in C^{\perp s}$, so by character orthogonality $\sum_{c\in C}\chi_b(c)=|C|$ for $b\in C^{\perp s}$ and $0$ otherwise. Hence (eq:mac)
$$\sum_{c\in C}\sum_{b\in\mathbb{F}_q^{2n}}\chi_b(c)z^{\mathrm{swt}(b)}=\sum_b z^{\mathrm{swt}(b)}\sum_{c\in C}\chi_b(c)=|C|\,B(z).$$
Writing $c=(c_1,\dots,c_n\mid d_1,\dots,d_n)$ and expanding, the inner sum factors as $\prod_{k=1}^n\sum_{(a_k\mid b_k)\in\mathbb{F}_q^2}z^{\mathrm{swt}(a_k\mid b_k)}\chi(\mathrm{tr}(d_ka_k-b_kc_k))$. Since $(a_k\mid b_k)\mapsto\chi(\mathrm{tr}(d_ka_k-b_kc_k))$ is a nontrivial character of $\mathbb{F}_q^2$ when $(c_k\mid d_k)\neq(0\mid0)$, each factor equals $1+(q^2-1)z$ if $(c_k\mid d_k)=(0,0)$ and $1-z$ otherwise. Thus
$$\sum_b\chi_b(c)z^{\mathrm{swt}(b)}=(1-z)^{\mathrm{swt}(c)}(1+(q^2-1)z)^{n-\mathrm{swt}(c)}.$$
Substituting into (eq:mac) yields $B(z)=\frac{(1+(q^2-1)z)^n}{|C|}\sum_{c\in C}\left(\frac{1-z}{1+(q^2-1)z}\right)^{\mathrm{swt}(c)}=\frac{(1+(q^2-1)z)^n}{|C|}A\!\left(\frac{1-z}{1+(q^2-1)z}\right)$.

<a id="pdf-4bcdc0ee9c86-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.98 -->
**Corollary (th:krawtchouk).** The coefficient of $z^j$ in $(1+(q^2-1)z)^{n-x}(1-z)^x$ is the Krawtchouk polynomial $K_j(x)=\sum_{s=0}^j(-1)^s(q^2-1)^{j-s}\binom{x}{s}\binom{n-x}{j-s}$. With the notation of the previous theorem, $B_j=\frac{1}{|C|}\sum_{x=0}^n K_j(x)A_x$.

<a id="pdf-4bcdc0ee9c86-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.97 -->
**Proof.** From the theorem, $B(z)=\frac{(1+(q^2-1)z)^n}{|C|}A\!\left(\frac{1-z}{1+(q^2-1)z}\right)=\frac{1}{|C|}\sum_{x=0}^n A_x(1-z)^x(1+(q^2-1)z)^{n-x}$. Comparing coefficients of $z^j$ gives the result.

<a id="pdf-4bcdc0ee9c86-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->
**Section — Bounds.** (SL enumerator theory of shor97 was extended by Rains in rains98–rains00.) These bounds constrain the achievable minimum distance of quantum stabilizer codes.

<a id="pdf-4bcdc0ee9c86-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.97 -->
**Theorem.** If an $((n,K,d))_q$ stabilizer code with $K>1$ exists, then there is a solution to: minimize $\sum_{j=1}^{d-1}A_j$ subject to (1) $A_0=1$ and $A_j\ge0$ for $1\le j\le n$; (2) $\sum_{j=0}^n A_j=q^n/K$; (3) $B_j=\frac{K}{q^n}\sum_{r=0}^n K_j(r)A_r$ for $0\le j\le n$; (4) $A_j=B_j$ for $0\le j<d$ and $A_j\le B_j$ for $d\le j\le n$; (5) $(p-1)\mid A_j$ for $1\le j\le n$.

<a id="pdf-4bcdc0ee9c86-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.95 -->
**Proof.** The symplectic weight distribution of the associated additive code $C$ satisfies (1) and (2). Since $\alpha c\in C$ for all $\alpha\in\mathbb{F}_p^*$ and nonzero $c\in C$, (5) holds. Corollary th:krawtchouk gives (3), and minimum distance $d$ gives (4).

<a id="pdf-4bcdc0ee9c86-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.96 -->
**Remark.** For $\mathbb{F}_{q^2}$-linear codes, condition (5) can be replaced by $(q^2-1)\mid A_j$, which helps even in characteristic 2.

<a id="pdf-4bcdc0ee9c86-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.97 -->
**Theorem (th:lp2).** Let $Q$ be an $((n,K,d))_q$ stabilizer code with $K>1$. Let $S$ be a nonempty subset of $\{0,\dots,d-1\}$ and $N=\{0,\dots,n\}$. Let $f(x)=\sum_{i=0}^n f_i K_i(x)$ satisfy (i) $f_x>0$ for $x\in S$ and $f_x\ge0$ otherwise; (ii) $f(x)\le0$ for all $x\in N\setminus S$. Then $K\le\frac{1}{q^n}\max_{x\in S}\frac{f(x)}{f_x}$. (Delsarte's LP method; binary versions by Ashikhmin–Litsyn.)

<a id="pdf-4bcdc0ee9c86-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.95 -->
**Proof.** Let $C\le\mathbb{F}_q^{2n}$ be the additive code of $Q$. Applying th:krawtchouk to $C^{\perp s}$ gives $A_i=\frac{1}{|C^{\perp s}|}\sum_{x=0}^n K_i(x)B_x$. Then
$$|C^{\perp s}|\sum_{i\in S}f_iA_i\le|C^{\perp s}|\sum_{i=0}^n f_iA_i=\sum_{x=0}^n B_x\sum_{i=0}^n f_iK_i(x)=\sum_{x=0}^n B_x f(x).$$
By condition (ii), $\sum_x B_x f(x)\le\sum_{x\in S}B_x f(x)=\sum_{x\in S}A_x f(x)$, using $A_x=B_x$ for $0\le x<d$. Hence $|C^{\perp s}|\le\left(\sum_{x\in S}A_x f(x)\right)/\left(\sum_{x\in S}f_xA_x\right)\le\max_{x\in S}\frac{f(x)}{f_x}$, and $|C^{\perp s}|=q^nK$ gives the claim.

<a id="pdf-4bcdc0ee9c86-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.98 -->
**Corollary (Quantum Singleton Bound, th:singleton).** An $((n,K,d))_q$ stabilizer code with $K>1$ satisfies $K\le q^{n-2d+2}$.

<a id="pdf-4bcdc0ee9c86-p008-b010"></a>
<!-- pdf-source: page=8; block=10; confidence=0.90 -->
**Proof.** Take $S=\{0,\dots,d-1\}$ and $f(x)=q^{n-d+1}\prod_{j=d}^n(1-x/j)$, so $f(x)=0$ on $N\setminus S$; equivalently $f(x)=q^{n-d+1}\binom{n-x}{n-d+1}/\binom{n}{n-d+1}$. Its Krawtchouk coefficients are $f_i=q^{-2n}\sum_x f(x)K_x(i)=q^{1-d-n}\sum_x K_x(i)\binom{n-x}{n-d+1}/\binom{n}{n-d+1}$. Using $\sum_x K_x(i)\binom{n-x}{n-d+1}=\binom{n-i}{d-1}q^{2(d-1)}$ (levenshtein95), $f_i=q^{d-1-n}\binom{n-i}{d-1}/\binom{n}{n-d+1}>0$. Then $r(x):=f(x)/f_x=q^{2n-2d+2}\binom{n-x}{n-d+1}/\binom{n-x}{d-1}$, with $r(x)/r(x+1)=\frac{n-x-d+1}{d-x-1}$. Assuming a code with $2d\ge n+2$, $r(x)/r(x+1)\le1$, so $r(d-1)$ is the max on $S$; th:lp2 gives $K\le r(d-1)/q^n=q^{n-2d+2}/\binom{n-d+1}{d-1}$, contradicting $K>1$ since $\binom{n-d+1}{d-1}K$ cannot be below $q^{n-2d+2}\le1$.

<a id="pdf-4bcdc0ee9c86-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.93 -->
**Proof (continued).** If $2d<n+2$, then $r(x)/r(x+1)>1$, so $r(0)=f(0)/f_0$ is the largest of the $r(x)$ for $x\in\{0,\dots,d-1\}$. Since $r(0)=q^{2n-2d+2}$, th:lp2 gives $K\le q^{-n}\max_{0\le x<d}f(x)/f_x=q^{n-2d+2}$, proving the claim. (Binary case: Knill–Laflamme; generalized by Rains via weight enumerators.)

<a id="pdf-4bcdc0ee9c86-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.94 -->
The quantum Hamming bound states any pure $((n,K,d))_q$ stabilizer code satisfies $\sum_{i=0}^{\lfloor(d-1)/2\rfloor}\binom{n}{i}(q^2-1)^i\le q^n/K$ (gottesman96, feng04). Gottesman showed impure single/double error-correcting binary codes cannot beat it; th:lp2 recovers the Hamming bound for small distance, illustrated below for single-error-correcting codes.

<a id="pdf-4bcdc0ee9c86-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.98 -->
**Corollary (Quantum Hamming Bound, th:hamming).** An $((n,K,3))_q$ stabilizer code with $K>1$ satisfies $K\le q^n/(n(q^2-1)+1)$.

<a id="pdf-4bcdc0ee9c86-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.93 -->
**Proof.** The intersection numbers of the Hamming scheme $H(n,q^2)$, $p_{ij}^k=|\{z\in\mathbb{F}_{q^2}^n\mid d(x,z)=i,\,d(y,z)=j\}|$ (for $d(x,y)=k$), satisfy $p_{ij}^k=q^{-2n}\sum_{u=0}^n K_i^n(u)K_j^n(u)K_u^n(k)$ (barg00). Let $f(x)=\sum_{j,k=0}^1\sum_{i=0}^n K_j^n(i)K_k^n(i)K_i^n(x)=q^{2n}(p_{00}^x+p_{10}^x+p_{01}^x+p_{11}^x)$. The triangle inequality gives $f(x)=0$ for $x>2$, and $f_i=(K_0(i)+K_1(i))^2\ge0$. Computing: $f(0)=q^{2n}(n(q^2-1)+1)$, $f_0=(n(q^2-1)+1)^2$; $f(1)=q^{2n+2}$, $f_1=((n-1)(q^2-1))^2$; $f(2)=2q^{2n}$, $f_2=((n-2)(q^2-1)-1)^2$. Then $\max\{f(0)/f_0,f(1)/f_1,f(2)/f_2\}\le q^{2n}/(n(q^2-1)+1)$ for all $n\ge5$, so th:lp2 gives the claim for $n\ge5$; for $n<5$ it follows from the quantum Singleton bound.

<a id="pdf-4bcdc0ee9c86-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.94 -->
**Paragraph — Lower Bounds.** A drawback of th:lp2 is that the term count grows with $d$. This section gives quantum Gilbert–Varshamov existence bounds via a counting argument, generalizing Gottesman's binary proof.

<a id="pdf-4bcdc0ee9c86-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.98 -->
**Lemma (th:gilbert).** An $((n,K,\ge d))_q$ stabilizer code with $K>1$ exists provided (eq:gilbert)
$$(q^nK-q^n/K)\sum_{j=1}^{d-1}\binom{n}{j}(q^2-1)^j<(q^{2n}-1)(p-1).$$

<a id="pdf-4bcdc0ee9c86-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.93 -->
**Proof.** Let $L=\{C^{\perp s}\setminus C\mid C\le C^{\perp s}\le\mathbb{F}_q^{2n},\,|C|=q^n/K\}$; its elements correspond to dimension-$K$ stabilizer codes. $L\neq\emptyset$ since a code generated by elements $(a\mid0)$ has size $q^n/K$ and satisfies $C\le C^{\perp s}$. Because $\mathrm{Sp}(2n,\mathbb{F}_q)$ acts transitively on $\mathbb{F}_q^{2n}\setminus\{0\}$ (grove01, Prop. 3.2), all nonzero vectors lie in equally many sets of $L$: any nonzero vector occurs in $|L|(q^nK-q^n/K)/(q^{2n}-1)$ elements, and a vector shares its sets with its $\mathbb{F}_p^\times$-multiples. Deleting every set containing a nonzero vector of symplectic weight $<d$ removes at most $\frac{\sum_{j=1}^{d-1}\binom{n}{j}(q^2-1)^j}{p-1}\,|L|\frac{(q^nK-q^n/K)}{q^{2n}-1}$ sets, which by hypothesis is $<|L|$; hence a suitable code exists.

<a id="pdf-4bcdc0ee9c86-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.98 -->
**Lemma (th:lingilbert).** If $k\ge1$, $n\equiv k\bmod 2$, and (eq:lingilbert)
$$(q^{n+k}-q^{n-k})\sum_{j=1}^{d-1}\binom{n}{j}(q^2-1)^{j-1}<(q^{2n}-1),$$
then there exists an $\mathbb{F}_{q^2}$-linear $[[n,k,d]]_q$ stabilizer code.

<a id="pdf-4bcdc0ee9c86-p009-b009"></a>
<!-- pdf-source: page=9; block=9; confidence=0.90 -->
**Proof.** As in the previous lemma but restricting to linear codes $C$ (with $\phi(C)$ an $\mathbb{F}_{q^2}$-vector space), using the multiset $L=\{C^{\perp s}\setminus C\mid C\le C^{\perp s}\le\mathbb{F}_q^{n},\,|C|=q^{n-k},\,\phi(C)\text{ is }\mathbb{F}_{q^2}\text{-linear}\}$. Each set now contains all $\mathbb{F}_{q^2}^\times$-multiples of a nonzero vector rather than just the $\mathbb{F}_p^\times$-multiples, which yields the statement.

<a id="pdf-4bcdc0ee9c86-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->
Feng and Ma extended the previous result to prove existence of *pure* stabilizer codes, but via more delicate counting arguments [feng04]; no short proof is known. The preceding lemma yields good quantum codes, especially over larger alphabets, illustrated next by MDS stabilizer codes (cf. Section MDS).

<a id="pdf-4bcdc0ee9c86-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.10 -->
**Corollary.** If $2\le d\le \lceil n/2\rceil$ and $q^2-1\ge \binom{n}{d}$, then there exists a linear $[[n,n-2d+2,d]]_q$ stabilizer code.

<a id="pdf-4bcdc0ee9c86-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.94 -->
**Proof.** Since $d\le\lceil n/2\rceil$, the binomials satisfy $\binom{n}{1}\le\cdots\le\binom{n}{d}$, so all are $\le q^2-1$. Set $k=n-2d+2$; then $k\ge1$ and $n\equiv k\bmod 2$. It remains to verify (eq:lingilbert). For this $k$ its left side equals
$$(q^{2n-2d+2}-q^{2d-2})\sum_{j=1}^{d-1}\binom{n}{j}(q^2-1)^{j-1}\le (q^{2n-2d+2}-q^{2d-2})\sum_{j=1}^{d-1}(q^2-1)^j=(q^{2n-2d+2}-q^{2d-2})\frac{(q^2-1)^d-(q^2-1)}{q^2-2}.$$
This is $<q^{2n}-1$ provided (eq:ineq) $q^{2n-2d+2}\frac{(q^2-1)^d-(q^2-1)}{q^2-2}\le q^{2n}$, which is equivalent to $(q^2-1)^d\le q^{2d}-2q^{2d-2}+q^2-1$. Using $q^{2d}=((q^2-1)+1)^d=(q^2-1)^d+\sum_{j=0}^{d-1}\binom{d}{j}(q^2-1)^j$ and Pascal's identity,
$$q^{2d}-2q^{2d-2}-(q^2-1)^d=\sum_{j=0}^{d-1}\big(\binom{d}{j}-2\binom{d-1}{j}\big)(q^2-1)^j=\sum_{j=0}^{d-1}\alpha(j)(q^2-1)^j,\quad \alpha(j):=\binom{d-1}{j-1}-\binom{d-1}{j}.$$
Since $\alpha(j)=-\alpha(d-j)$ and $\alpha(j)\ge0$ for $j\ge d/2$, negative terms are cancelled by larger positive ones, giving $q^{2d}-2q^{2d-2}-(q^2-1)^d\ge0$ for $d\ge2$. This proves (eq:ineq), hence (eq:lingilbert). $\square$

<a id="pdf-4bcdc0ee9c86-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->
**Example.** No $[[7,1,4]]_2$ code exists [calderbank98], yet the corollary guarantees $[[7,1,4]]_q$ for all prime powers $q\ge7$, as well as $[[6,2,3]]_q$ for $q\ge5$ and $[[7,3,3]]_q$ for $q\ge7$ (generalizing [feng02]).

<a id="pdf-4bcdc0ee9c86-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.98 -->
**Section: Cyclic Codes.**

<a id="pdf-4bcdc0ee9c86-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.95 -->
Restricting to linear quantum codes, derive families from classical linear codes via the hermitian and CSS constructions (Lemmas co:classical–th:css2); this requires classical codes self-orthogonal w.r.t. the hermitian or euclidean product, or nested families such as BCH codes. Let $\sigma$ be the automorphism of $\F_{q^2}$ with $\sigma(x)=x^q$, acting on $\F_{q^2}[x]$ by $h(x)=\sum_{k=0}^n h_k x^k\mapsto h^\sigma(x)=\sum_{k=0}^n\sigma(h_k)x^k$.

<a id="pdf-4bcdc0ee9c86-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.96 -->
**Lemma (th:cyclic).** Let $B$ be a classical cyclic $[n,k,d]_{q^2}$ code with generator polynomial $g(x)$ and check polynomial $h(x)=(x^n-1)/g(x)$. If $g(x)$ divides $\sigma(h_0)^{-1}x^k h^\sigma(1/x)$, then $B^{\perp_h}\subseteq B$ and there exists an $[[n,2k-n,\ge d]]_q$ stabilizer code pure to $d$.

<a id="pdf-4bcdc0ee9c86-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.95 -->
**Proof.** If $h(x)$ is the check polynomial of $B$, then $h^\sigma(x)$ is the check polynomial of $\sigma(B)$, and the generator polynomial of $\sigma(B)^\perp=B^{\perp_h}$ is the normalized reciprocal $\sigma(h_0)^{-1}x^k h^\sigma(1/x)$. Hence $g(x)$ dividing this polynomial is equivalent to $B^{\perp_h}\subseteq B$. The stabilizer code follows from Corollary co:classical. $\square$

<a id="pdf-4bcdc0ee9c86-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.95 -->
$x^n-1\in\F_{q^2}[x]$ has simple roots iff $\gcd(n,q)=1$; then some $\F_{q^{2m}}$ contains a primitive $n$th root of unity $\beta$, and a cyclic code with generator $g(x)$ is described by its defining set $Z=\{k\mid g(\beta^k)=0,\ 0\le k<n\}$.

<a id="pdf-4bcdc0ee9c86-p010-b010"></a>
<!-- pdf-source: page=10; block=10; confidence=0.96 -->
**Lemma (th:cyclic2).** Let $\gcd(n,q^2)=1$ and $C$ be a classical cyclic $[n,k,d]_{q^2}$ code with generator $g(x)$ and defining set $Z$. If any of the equivalent conditions holds: (i) $x^n-1\equiv0\bmod g(x)g^*(x)$ with $g^*(x)=x^{n-k}g^\sigma(1/x)$; (ii) $Z\subseteq\{-qz\mid z\in N\setminus Z\}$; (iii) $Z\cap Z^{-q}=\emptyset$, where $Z^{-q}=\{-qz\mid z\in Z\}$; then $C^{\perp_h}\subseteq C$ and there exists an $[[n,2k-n,\ge d]]_q$ stabilizer code pure to $d$.

<a id="pdf-4bcdc0ee9c86-p010-b011"></a>
<!-- pdf-source: page=10; block=11; confidence=0.93 -->
**Proof.** Let $h(x)=(x^n-1)/g(x)$. Then $h^\sigma(x)=\sigma((x^n-1)/g(x))=(x^n-1)/g^\sigma(x)$. By th:cyclic, $C$ contains its hermitian dual iff $g(x)\mid\sigma(h_0)^{-1}x^k h^\sigma(1/x)$, i.e. $g(x)\mid\sigma(h_0)^{-1}(1-x^n)/(x^{n-k}g^\sigma(1/x))$, which implies $x^n-1\equiv0\bmod g(x)g^*(x)$, proving (i). [continued next page]

<a id="pdf-4bcdc0ee9c86-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.93 -->
**Proof (continued).** With $g(x)=\prod_{z\in Z}(x-\beta^z)$, the check polynomial is $h(x)=\prod_{z\in N\setminus Z}(x-\beta^z)$, so $h^\sigma(x)=\prod_{z\in N\setminus Z}(x-\beta^{qz})$. The generator of $C^{\perp_h}$ is
$$h^\sigma(0)^{-1}x^k h^\sigma(1/x)=h^\sigma(0)^{-1}\prod_{z\in N\setminus Z}(1-\beta^{qz}x)=\prod_{z\in N\setminus Z}(x-\beta^{-qz}),$$
using $h^\sigma(0)^{-1}=\prod_{z\in N\setminus Z}(-\beta^{-qz})$. By th:cyclic, $B^{\perp_h}\subseteq B$ iff $g(x)$ divides this, equivalently $Z\subseteq\{-qz\mid z\in N\setminus Z\}$, giving (ii). This says $Z^{-q}\subseteq N\setminus Z$, hence $Z\cap Z^{-q}=\emptyset$, giving (iii). The $[[n,2k-n,\ge d]]_q$ stabilizer code follows from Corollary co:classical. $\square$

<a id="pdf-4bcdc0ee9c86-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->
Cyclic codes containing their euclidean duals admit an analogous characterization via generator polynomials and defining sets, extending the binary case.

<a id="pdf-4bcdc0ee9c86-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.96 -->
**Lemma (th:csscyclic).** Let $C$ be an $[n,k,d]_q$ cyclic code with $\gcd(n,q)=1$, defining set $Z$, generator $g(x)$. If any equivalent condition holds: (i) $x^n-1\equiv0\bmod g(x)g^{\dagger}(x)$ with $g^{\dagger}(x)=x^{n-k}g(1/x)$; (ii) $Z\subseteq\{-z\mid z\in N\setminus Z\}$; (iii) $Z\cap Z^{-1}=\emptyset$, $Z^{-1}=\{-z\bmod n\mid z\in Z\}$; then $C^\perp\subseteq C$ and there exists an $[[n,2k-n,\ge d]]_q$ stabilizer code pure to $d$.

<a id="pdf-4bcdc0ee9c86-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.94 -->
**Proof.** Check polynomial $h(x)=(x^n-1)/g(x)$ gives the (unnormalized) generator of $C^\perp$: $h^\dagger(x)=x^k h(x^{-1})=(1-x^n)/(x^{n-k}g(x^{-1}))=-(x^n-1)/g^\dagger(x)$. If $C^\perp\subseteq C$ then $g(x)\mid h^\dagger(x)$, i.e. $g(x)\mid(x^n-1)/g^\dagger(x)$, so $x^n-1\equiv0\bmod g(x)g^\dagger(x)$. The defining set of $C^\perp$ is $\{-z\bmod n\mid z\in N\setminus Z\}$ with $N=\{0,\dots,n-1\}$; thus $C^\perp\subseteq C$ gives $Z\subseteq\{-z\bmod n\mid N\setminus Z\}$, i.e. $Z\cap Z^{-1}=\emptyset$. The code $[[n,2k-n,\ge d]]_q$ follows from Corollary th:css2. $\square$

<a id="pdf-4bcdc0ee9c86-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.95 -->
A larger class of cyclic quantum codes arises from constacyclic or conjucyclic codes [calderbank98, xiaoyan04].

<a id="pdf-4bcdc0ee9c86-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.98 -->
**Section: Cyclic Hamming Codes.**

<a id="pdf-4bcdc0ee9c86-p011-b007"></a>
<!-- pdf-source: page=11; block=7; confidence=0.95 -->
For integer $m>1$ with $\gcd(q-1,m)=1$, the classical cyclic Hamming code $H_q(m)$ has parameters $[n,n-m,3]_q$, length $n=(q^m-1)/(q-1)$. With $\beta$ a primitive $n$th root of unity in $\F_{q^m}$, its generator polynomial is $g(x)=\prod_{i=0}^{m-1}(x-\beta^{q^i})$ (eq:hamminggen) $\in\F_q[x]$; equivalently $H_q(m)$ is defined by the cyclotomic coset $C_1=\{q^i\bmod n\mid i\in\Z\}$.

<a id="pdf-4bcdc0ee9c86-p011-b008"></a>
<!-- pdf-source: page=11; block=8; confidence=0.97 -->
**Lemma (th:hammingdual).** The Hamming code $H_{q^2}(m)$ contains its hermitian dual: $H_{q^2}(m)^{\perp_h}\le H_{q^2}(m)$.

<a id="pdf-4bcdc0ee9c86-p011-b009"></a>
<!-- pdf-source: page=11; block=9; confidence=0.93 -->
**Proof.** The claim is equivalent to $C_1\subseteq N_1=\{-qz\bmod n\mid z\in N\setminus C_1\}$, where $N=\{0,\dots,n-1\}$, $n=(q^{2m}-1)/(q^2-1)$. Writing (eq:cosets) $C_1=\{(1-n)q^{2k}\bmod n\mid k\in\Z\}=\{-qzq^{2k}\bmod n\mid k\in\Z\}$ with $z=q(q^{2m-2}-1)/(q^2-1)$, the condition holds iff $C_z\subseteq N\setminus C_1$, where $C_z=\{zq^{2j}\bmod n\mid j\in\Z\}$. If $C_1,C_z$ shared an element they would coincide, forcing some $k>0$ with $q^{2k}=q(q^{2m-2}-1)/(q^2-1)$, i.e. $q^{2k-1}\mid q^{2m-2}-1$, which is absurd. Hence $C_z\subseteq N\setminus C_1$, proving the claim. $\square$

<a id="pdf-4bcdc0ee9c86-p011-b010"></a>
<!-- pdf-source: page=11; block=10; confidence=0.10 -->
**Theorem.** For each $m\ge2$ with $\gcd(m,q^2-1)=1$, there exists a pure $[[n,n-2m,3]]_q$ stabilizer code of length $n=(q^{2m}-1)/(q^2-1)$.

<a id="pdf-4bcdc0ee9c86-p011-b011"></a>
<!-- pdf-source: page=11; block=11; confidence=0.94 -->
**Proof.** If $\gcd(m,q^2-1)=1$ there is a classical $[n,n-m,3]_{q^2}$ Hamming code $H_{q^2}(m)$; by th:hammingdual it contains its hermitian dual, so a pure $[[n,n-2m,3]]_q$ stabilizer code exists by Corollary co:classical. Purity holds since $H_{q^2}(m)^{\perp_h}$ has minimum distance $q^{2m-2}\ge3$ for $m\ge2$ [huffman03, Thm 1.8.3]. $\square$

<a id="pdf-4bcdc0ee9c86-p011-b012"></a>
<!-- pdf-source: page=11; block=12; confidence=0.94 -->
These quantum Hamming codes are optimal, attaining the quantum Hamming bound (Cor th:hamming). Noncyclic perfect quantum codes appear in [bierbrauer00]. Quantum codes from Hamming codes containing their euclidean duals are also constructible but do not meet the quantum Hamming bound.

<a id="pdf-4bcdc0ee9c86-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.97 -->
**Lemma.** If $\gcd(m,q-1)=1$ and $m\ge2$, there exists a pure $[[n,n-2m,3]]_q$ quantum code, where $n=(q^m-1)/(q-1)$.

<a id="pdf-4bcdc0ee9c86-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.94 -->
**Proof.** The $[n,n-m,3]_q$ Hamming code has generator (eq:hamminggen) with $\beta$ of order $n$, existing iff $\gcd(m,q-1)=1$. By th:csscyclic a cyclic code contains its dual if $x^n-1\equiv0\bmod g(x)g^\dagger(x)$, $g^\dagger(x)=x^{n-k}g(x^{-1})$; and if $g(x)$ is not self-reciprocal then $g(x)g^\dagger(x)\mid x^n-1$ [vatan99]. Since the Hamming generator is not self-reciprocal, the code contains its euclidean dual, yielding by th:csscyclic a $[[n,n-2m,3]]_q$ code. Purity follows since duals of Hamming codes are simplex codes of weight $q^{m-1}\ge3$ [huffman03, Thm 1.8.3] for $m\ge2$. $\square$

<a id="pdf-4bcdc0ee9c86-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.98 -->
**Section: Quadratic Residue Codes.**

<a id="pdf-4bcdc0ee9c86-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.95 -->
Rains constructed quadratic residue codes for prime alphabet [rains99]; here two series of quantum codes are built from classical QR codes over arbitrary fields by elementary methods.

<a id="pdf-4bcdc0ee9c86-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.10 -->
**Theorem (Quadratic Residue Codes).** Let $n$ be a prime with $n\equiv3\bmod4$, and $q$ a prime power not divisible by $n$. If $q$ is a quadratic residue mod $n$, then there exists a pure $[[n,1,d]]_q$ stabilizer code with minimum distance $d$ satisfying $d^2-d+1\ge n$.

<a id="pdf-4bcdc0ee9c86-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.94 -->
**Proof.** Let $\alpha$ be a primitive $n$th root of unity over $\F_q$ and $R=\{r^2\bmod n\mid 1\le r\le(n-1)/2\}$ the quadratic residues. Define $C_R$ as the cyclic code of length $n$ over $\F_q$ generated by $q(x)=\prod_{r\in R}(x-\alpha^r)$; it has parameters $[n,(n+1)/2,d]_q$. For $n\equiv3\bmod4$, the dual $C_R^\perp$ is generated by $(x-1)q(x)$, the even-like subcode of $C_R$, so $C_R^\perp\le C_R$. The distance satisfies $d^2-d+1\ge n$ [betten98, pp.114–119], and $\wt(C_R\setminus C_R^\perp)=\wt(C_R)=d$ [huffman03, Thm 6.6.22]. By Corollary th:css2 a pure $[[n,(n+1)-n,d]]_q=[[n,1,d]]_q$ stabilizer code exists. $\square$

<a id="pdf-4bcdc0ee9c86-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.95 -->
**Example.** $p=3$ is a quadratic residue mod $n=23$, so a $[[23,1,d]]_3$ stabilizer code exists with $d\ge6$.

<a id="pdf-4bcdc0ee9c86-p012-b008"></a>
<!-- pdf-source: page=12; block=8; confidence=0.95 -->
For an odd prime $n\equiv1\bmod4$, QR codes can also be constructed, but one must use Lemma th:css since $C_R$ does not contain its dual.

<a id="pdf-4bcdc0ee9c86-p012-b009"></a>
<!-- pdf-source: page=12; block=9; confidence=0.97 -->
**Theorem.** Let $n$ be a prime with $n\equiv1\bmod4$ and $q$ a prime power not divisible by $n$. If $q$ is a quadratic residue mod $n$, then there exists a pure $[[n,1,d]]_q$ stabilizer code with $d\ge\sqrt{n}$.

<a id="pdf-4bcdc0ee9c86-p012-b010"></a>
<!-- pdf-source: page=12; block=10; confidence=0.94 -->
**Proof.** Let $\alpha$ be a primitive $n$th root of unity, $R$ the quadratic residues and $N$ the non-residues mod $n$. Let $C_R,C_N$ be the cyclic codes of length $n$ generated by $q_R(x)=\prod_{r\in R}(x-\alpha^r)$ and $q_N(x)=\prod_{r\in N}(x-\alpha^r)$; both have parameters $[n,(n+1)/2,d]_q$ with $d^2\ge n$ [betten98, pp.114–119]. The dual of $C_R$ is the even-like subcode of $C_N$: $C_R^\perp$ is generated by $(x-1)q_N(x)$, so $C_R^\perp\le C_N$. Moreover $\wt(C_R\setminus C_N^\perp)=\wt(C_N\setminus C_R^\perp)=d$ [huffman03, Thm 6.6.22]. By Lemma th:css this yields a pure $[[n,(n+1)/2+(n+1)/2-n,d]]_q=[[n,1,d]]_q$ code. $\square$

<a id="pdf-4bcdc0ee9c86-p012-b011"></a>
<!-- pdf-source: page=12; block=11; confidence=0.98 -->
**Section: Quantum Melas Codes.**

<a id="pdf-4bcdc0ee9c86-p012-b012"></a>
<!-- pdf-source: page=12; block=12; confidence=0.95 -->
Melas codes are an early family for burst-error correction, of interest for their algebraic-geometry/number-theory connections. The Melas code $\mathcal{M}_q(m)$ is a cyclic $[n,n-2m,\ge3]_q$ code with $n=q^m-1$, generator $g(x)=\prod_{i=0}^{m-1}(x-\alpha^{q^i})(x-\alpha^{-q^i})$ where $\alpha$ is primitive in $\F_{q^m}$; equivalently defining set $Z=C_1\cup C_{-1}=\{\pm q^i\bmod n\mid 0\le i<m\}$. (Footnote: classical Melas codes are over a prime field $\F_p$ with parameters $[p^m-1,p^m-m-1,\ge3]_p$; this is a generalization to arbitrary finite fields.)

<a id="pdf-4bcdc0ee9c86-p012-b013"></a>
<!-- pdf-source: page=12; block=13; confidence=0.97 -->
**Lemma (th:melas_orth).** The Melas code $\mathcal{M}_{q^2}(m)$ contains its hermitian dual.

<a id="pdf-4bcdc0ee9c86-p012-b014"></a>
<!-- pdf-source: page=12; block=14; confidence=0.94 -->
**Proof.** By Lemma th:cyclic2 it suffices that $Z\cap Z^{-q}=\emptyset$. Assume otherwise; since $\gcd(q^2,q^{2m}-1)=1$, there would be $i$ with $0\le i<m$ and $q^{2i}\equiv\pm q\bmod n$, which is impossible. Hence $Z\cap Z^{-q}=\emptyset$. $\square$

<a id="pdf-4bcdc0ee9c86-p012-b015"></a>
<!-- pdf-source: page=12; block=15; confidence=0.96 -->
**Lemma (th:melas_dist).** If $q$ is even, the minimum distance of the Melas code $\mathcal{M}_{q^2}(m)$ is at least $3$.

<a id="pdf-4bcdc0ee9c86-p012-b016"></a>
<!-- pdf-source: page=12; block=16; confidence=0.94 -->
**Proof.** The parity-check matrix is $H=\begin{pmatrix}1&\alpha&\alpha^2&\cdots&\alpha^{n-1}\\ 1&\alpha^{-1}&\alpha^{-2}&\cdots&\alpha^{-(n-1)}\end{pmatrix}$. It has rank $2$ iff no two columns are scalar multiples. Suppose $(\alpha^x,\alpha^{-x})^T=\alpha^t(\alpha^y,\alpha^{-y})^T$ for distinct $x,y$; then $\alpha^{2t}=1$, so $t\in\{0,n/2\}$. For $q$ even, $n$ is odd, so $t\ne n/2$; and $t=0$ gives $x=y$, a contradiction. Hence $H$ has rank $2$ and the minimum distance is at least $3$. $\square$

<a id="pdf-4bcdc0ee9c86-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.97 -->
**Theorem (Quantum Melas codes).** If $q$ is even and $n=q^{2m}-1$, there exist quantum Melas codes with parameters $[[n,n-4m,\ge 3]]_q$ that are pure to 3.

<a id="pdf-4bcdc0ee9c86-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.96 -->
**Proof.** By Lemma (melas\_orth), $\mathcal{M}_{q^2}(m)^{\perp h}\subseteq \mathcal{M}_{q^2}(m)$; by Lemma (melas\_dist) the distance is $\ge 3$; hence by Corollary (classical) an $[[n,n-4m,\ge 3]]_q$ code exists.

<a id="pdf-4bcdc0ee9c86-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.90 -->
# Quantum BCH Codes

Constructs nonbinary quantum stabilizer codes from classical BCH codes; the CSS construction is useful because BCH codes form a nested family. For primitive BCH codes over prime fields the dual distance is lower-bounded by the generalized Carlitz–Uchiyama bound, yielding bounds on the quantum minimum distance.

<a id="pdf-4bcdc0ee9c86-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->
**Definition (BCH code).** Let $q$ be a prime power and $n$ coprime to $q$. A BCH code $C$ of length $n$ and designed distance $\delta$ over $\mathbb{F}_q$ is a cyclic code whose defining set is $Z=\bigcup_{x=b}^{b+\delta-2} C_x$, where $C_x=\{xq^r \bmod n \mid r\in\mathbb{Z},\ r\ge 0\}$. Generator polynomial $g(x)=\prod_{z\in Z}(x-\beta^z)$, with $\beta$ a primitive $n$-th root of unity in an extension of $\mathbb{F}_q$. This gives a cyclic $[n,k,d]_q$ code with $k=n-|Z|$ and $d\ge\delta$. If $b=1$ the code is narrow-sense; if $n=q^m-1$ it is primitive.

<a id="pdf-4bcdc0ee9c86-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.90 -->
First construction derives stabilizer codes from BCH codes over prime fields, using the Iverson bracket $[statement]$ (1 if true, else 0).

<a id="pdf-4bcdc0ee9c86-p013-b006"></a>
<!-- pdf-source: page=13; block=6; confidence=0.95 -->
**Lemma (Generalized Carlitz–Uchiyama Bound).** Let $p$ be prime and $C$ a narrow-sense BCH code of length $n=p^m-1$ over $\mathbb{F}_p$ with designed distance $\delta=2t+1$. Then the minimum distance $d^\perp$ of the euclidean dual $C^\perp$ satisfies
$$d^\perp \ge \Big(1-\tfrac{1}{p}\Big)\left(p^m-\tfrac{\delta-2-[\delta-1\equiv 0\bmod p]}{2}\big\lfloor 2p^{m/2}\big\rfloor\right).\quad (\text{eq. carlitzdist})$$

<a id="pdf-4bcdc0ee9c86-p013-b007"></a>
<!-- pdf-source: page=13; block=7; confidence=0.96 -->
**Proof.** See [stichtenoth94, Thm 7]; background [macwilliams77, p.280].

<a id="pdf-4bcdc0ee9c86-p013-b008"></a>
<!-- pdf-source: page=13; block=8; confidence=0.95 -->
**Theorem.** Let $p$ be prime, $C$ a $[p^m-1,k,\ge\delta]_p$ narrow-sense BCH code with $\delta=2t+1$, and $C^*$ a $[p^m-1,k^*,d^*]_p$ BCH code with $C\subseteq C^*$. Then there exists a $[[p^m-1,\ k^*-k,\ \ge\min\{d^*,d^\perp\}]]_p$ stabilizer code, where $d^\perp$ is given by (eq. carlitzdist).

<a id="pdf-4bcdc0ee9c86-p013-b009"></a>
<!-- pdf-source: page=13; block=9; confidence=0.95 -->
**Proof.** Apply the Carlitz–Uchiyama Lemma to $C$ and Lemma (css) to $C$ and $C^*$.

<a id="pdf-4bcdc0ee9c86-p013-b010"></a>
<!-- pdf-source: page=13; block=10; confidence=0.93 -->
**Remark.** (i) The bound is trivial for larger designed distances. (ii) [moreno94, Cor 2]: for binary BCH codes of design distance $d$, the bound (carlitzdist) is attained when $n=2^{2ab}-1$, where $a$ is the smallest integer with $d-2\mid 2^a+1$ and $b$ is odd. (iii) Further tightening in [moreno98, Thm 2].

<a id="pdf-4bcdc0ee9c86-p013-b011"></a>
<!-- pdf-source: page=13; block=11; confidence=0.90 -->
Extends the results to non-prime finite fields; for small designed distances sharper results hold. Results are reviewed here with proofs in companion [preprint0501126]. For small designed distance the cyclotomic cosets all have maximal size.

<a id="pdf-4bcdc0ee9c86-p013-b012"></a>
<!-- pdf-source: page=13; block=12; confidence=0.95 -->
**Lemma.** A narrow-sense, primitive BCH code with design distance $2\le\delta\le q^{\lceil m/2\rceil}+1$ has parameters $[q^m-1,\ q^m-1-m\lceil(\delta-1)(1-1/q)\rceil,\ \ge\delta]_q$.

<a id="pdf-4bcdc0ee9c86-p013-b013"></a>
<!-- pdf-source: page=13; block=13; confidence=0.95 -->
**Proof.** See [preprint0501126, Thm A]; binary case due to Steane [steane99].

<a id="pdf-4bcdc0ee9c86-p013-b014"></a>
<!-- pdf-source: page=13; block=14; confidence=0.94 -->
**Lemma.** A narrow-sense, primitive BCH code over $\mathbb{F}_q$ (length $n=q^m-1$, $m\ge 2$) contains its euclidean dual iff its design distance satisfies $2\le\delta\le q^{\lceil m/2\rceil}-1-(q-2)[m\text{ odd}]$.

<a id="pdf-4bcdc0ee9c86-p013-b015"></a>
<!-- pdf-source: page=13; block=15; confidence=0.96 -->
**Proof.** See [preprint0501126, Thm C].

<a id="pdf-4bcdc0ee9c86-p013-b016"></a>
<!-- pdf-source: page=13; block=16; confidence=0.95 -->
**Theorem.** If $C$ is a narrow-sense primitive BCH code over $\mathbb{F}_q$ with design distance $2\le\delta\le q^{\lceil m/2\rceil}-1-(q-2)[m\text{ odd}]$ and $m\ge 2$, then there exists a $[[q^m-1,\ q^m-1-2m\lceil(\delta-1)(1-1/q)\rceil,\ \ge\delta]]_q$ stabilizer code pure to $\delta$.

<a id="pdf-4bcdc0ee9c86-p013-b017"></a>
<!-- pdf-source: page=13; block=17; confidence=0.95 -->
**Proof.** Combine the two preceding Lemmas (BCH dimension and euclidean dual containment) and apply the CSS construction.

<a id="pdf-4bcdc0ee9c86-p013-b018"></a>
<!-- pdf-source: page=13; block=18; confidence=0.95 -->
**Theorem.** If $C$ is a narrow-sense primitive BCH code over $\mathbb{F}_{q^2}$ with design distance $2\le\delta\le q^m-1$, then there exists a $[[q^{2m}-1,\ q^{2m}-1-2m\lceil(\delta-1)(1-1/q^2)\rceil,\ \ge\delta]]_q$ stabilizer code pure to $\delta$.

<a id="pdf-4bcdc0ee9c86-p013-b019"></a>
<!-- pdf-source: page=13; block=19; confidence=0.96 -->
**Proof.** See [preprint0501126] for details.

<a id="pdf-4bcdc0ee9c86-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.93 -->
For $m=1$, BCH codes coincide with Reed–Solomon codes, handled in [grassl04]; a Reed–Muller perspective is in [klappenecker05p1].

<a id="pdf-4bcdc0ee9c86-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.92 -->
Extending a stabilizer code is not always possible since the classical codes must be self-orthogonal; narrow-sense BCH codes of certain lengths can be extended.

<a id="pdf-4bcdc0ee9c86-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->
**Lemma.** Let $\mathbb{F}_{q^2}$ have characteristic $p$. If $C$ is a narrow-sense $[n,k,\ge d]_{q^2}$ BCH code with $C^{\perp h}\subseteq C$ and $n\equiv -1\bmod p$, then there exists an $[[n,2k-n,\ge d]]_q$ stabilizer code pure to $d$, which can be extended to an $[[n+1,2k-n-1,\ge d+1]]_q$ stabilizer code pure to $d+1$.

<a id="pdf-4bcdc0ee9c86-p014-b004"></a>
<!-- pdf-source: page=14; block=4; confidence=0.90 -->
**Proof.** By Corollary (classical), $C^{\perp h}\subseteq C$ gives an $[[n,2k-n,\ge d]]_q$ code pure to $d$. Being narrow-sense, $C$ has parity check matrix $H$ with rows $(\ 1,\ \alpha^i,\ \alpha^{2i},\dots,\alpha^{(n-1)i}\ )$ for $i=1,\dots,d-1$, $\alpha$ a primitive $n$-th root of unity. Extend to $H_e$ by prepending an all-ones row and appending a last column $(1,0,\dots,0)^T$, giving an $[n+1,k,d+1]$ code $C_e$.

Show $C_e^{\perp h}$ is self-orthogonal: for rows $R_i$, $2\le i\le d$, $\langle R_i|R_j\rangle_h=0$ by self-orthogonality of $H$. For the all-ones row $\mathbf{1}$: for $2\le i\le d$, $\langle R_i|\mathbf{1}\rangle_h=\sum_{j=0}^{n-1}\alpha^{ij}=(\alpha^{in}-1)/(\alpha^i-1)=0$ since $\alpha^n=1,\ \alpha^i\ne 1$; for $i=1$, $\langle\mathbf{1}|\mathbf{1}\rangle_h=n+1\bmod p=0$ by $n\equiv-1\bmod p$.

Rank of $H_e$ is $d$: any $d$ columns excluding the last form a nonsingular $d\times d$ Vandermonde; any $d$ columns including the last, expanded along that column, give a nonzero $(d-1)\times(d-1)$ Vandermonde determinant. So minimum distance $\ge d+1$, and $C_e$ is an $[n+1,k,\ge d+1]_{q^2}$ extended cyclic code with $C_e^{\perp h}\subseteq C_e$. By Corollary (classical) it yields an $[[n+1,2k-n-1,\ge d+1]]_q$ code pure to $d+1$.

<a id="pdf-4bcdc0ee9c86-p014-b005"></a>
<!-- pdf-source: page=14; block=5; confidence=0.94 -->
**Corollary.** For all prime powers $q$, integers $m\ge 1$, and all $\delta$ with $2\le\delta\le q^m-1$, there exists a $$[[q^{2m},\ q^{2m}-2-2m\lceil(\delta-1)(1-1/q^2)\rceil,\ \ge\delta+1]]_q$$ stabilizer code pure to $\delta+1$.

<a id="pdf-4bcdc0ee9c86-p014-b006"></a>
<!-- pdf-source: page=14; block=6; confidence=0.94 -->
**Proof.** The codes of the hermitian-dual Theorem come from primitive narrow-sense BCH codes; if $p=\operatorname{char}\mathbb{F}_{q^2}$ then $q^{2m}-1\equiv-1\bmod p$, so they can be extended via the BCH extension Lemma.

<a id="pdf-4bcdc0ee9c86-p014-b007"></a>
<!-- pdf-source: page=14; block=7; confidence=0.92 -->
An analogue of the BCH extension Lemma holds for BCH codes that contain their euclidean duals.

<a id="pdf-4bcdc0ee9c86-p014-b008"></a>
<!-- pdf-source: page=14; block=8; confidence=0.90 -->
# Puncturing Stabilizer Codes

Puncturing deletes one coordinate of a classical code; for stabilizer codes this can break commutativity. Rains [rains99] solves puncturing for linear stabilizer codes and constructs stabilizer codes from arbitrary linear codes via a puncture code: if the puncture code has a codeword of weight $r$, a self-orthogonal code of length $r$ exists with distance $\ge$ the original. Further criteria in [grassl04]. This section generalizes puncturing to arbitrary stabilizer codes and punctures quantum BCH codes.

<a id="pdf-4bcdc0ee9c86-p014-b009"></a>
<!-- pdf-source: page=14; block=9; confidence=0.94 -->
**Definition (Puncture Code).** Write the pointwise product $uv=(u_iv_i)_{i=1}^n$ for $u,v\in\mathbb{F}_q^n$. For an arbitrary additive code $C\le\mathbb{F}_q^{2n}$, the associated puncture code is
$$P_s(C)=\big\{(b_ka_k'-b_k'a_k)_{k=1}^n \mid (a|b),(a'|b')\in C\big\}^\perp\subseteq\mathbb{F}_q^n.$$

<a id="pdf-4bcdc0ee9c86-p014-b010"></a>
<!-- pdf-source: page=14; block=10; confidence=0.10 -->
**Theorem.** Let $C$ be an arbitrary additive subcode of $\mathbb{F}_q^{2n}$ with $|C|=q^n/K$ and $\mathrm{swt}(C^{\perp s}\setminus C)=d$. If $P_s(C)$ contains a codeword of Hamming weight $r$, then there exists an $((r,K^*,d^*))_q$ stabilizer code with $K^*\ge K/q^{n-r}$ and $d^*\ge d$ when $K^*>1$. If $\mathrm{swt}(C^{\perp s})=d$, the punctured code is pure to $d$.

<a id="pdf-4bcdc0ee9c86-p014-b011"></a>
<!-- pdf-source: page=14; block=11; confidence=0.90 -->
**Proof.** Let $x$ be a weight-$r$ codeword in $P_s(C)$. Define $C_x=\{(a|bx)\mid(a|b)\in C\}$. For $(a|bx),(a'|b'x)\in C_x$,
$$\langle(a|bx)\,|\,(a'|b'x)\rangle_s=\mathrm{tr}\Big(\sum_{k=1}^n(b_ka_k'-b_k'a_k)x_k\Big)=0\quad(\text{eq. puncturedual})$$
by definition of $P_s(C)$; hence $C_x\le(C_x)^{\perp s}$.

<a id="pdf-4bcdc0ee9c86-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.88 -->
**Proof (cont.).** Let $C_x^R=\{(a_k|b_k)_{k\in S}\mid(a|b)\in C_x\}$ be the restriction to the support $S$ of $x$. Since (puncturedual) depends only on the nonzero coordinates of $x$, $C_x^R\le(C_x^R)^{\perp s}$. From $|C|\ge|C_x^R|$,
$$K^*\ge q^r/|C_x^R|\ge q^r/|C|=q^r/(q^n/K)=K/q^{n-r}.$$
To show $\mathrm{swt}((C_x^R)^{\perp s}\setminus C_x^R)\ge d$: suppose $u_x^R\in(C_x^R)^{\perp s}\setminus C_x^R$ with $\mathrm{swt}(u_x^R)<d$. Let $u_x=(a|b)\in(C_x)^{\perp s}$ be zero outside $S$ and equal to $u_x^R$ on $S$. Then $(ax|b)\in C^{\perp s}$ with $\mathrm{swt}(ax|b)<d$, so $(ax|b)\in C$ (since $\mathrm{swt}(C^{\perp s}\setminus C)=d$). Hence $(ax|bx)\in C_x\le(C_x)^{\perp s}$; iterating gives $(ax^2|bx)\in C$, $(ax^2|bx^2)\in C_x$, and eventually $v_x=(ax^{q-1}|bx^{q-1})\in C_x$, where $x^{q-1}$ is the characteristic vector of $S$. Restricting $v_x$ to $S$ gives $u_x^R\in C_x^R$, a contradiction. Purity follows by generalizing the argument of [grassl04].

<a id="pdf-4bcdc0ee9c86-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.94 -->
**Lemma.** If $C_1,C_2$ are additive subcodes of $\mathbb{F}_q^n$, then $P_s(C_1\times C_2)=\{ab\mid a\in C_1,\ b\in C_2\}^\perp\le\mathbb{F}_q^n$.

<a id="pdf-4bcdc0ee9c86-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.93 -->
**Proof.** Since $\langle ab\mid a\in C_1,b\in C_2\rangle=\langle(ba'-b'a)\mid a,a'\in C_1,\ b,b'\in C_2\rangle$, their orthogonal complements coincide.

<a id="pdf-4bcdc0ee9c86-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=0.93 -->
**Definition.** For a self-orthogonal code $C\le C^\perp$, write $P_e(C)=P_s(C\times C)=\{ab\mid a,b\in C\}^\perp$.

<a id="pdf-4bcdc0ee9c86-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.90 -->
**Setup (Puncturing BCH Codes).** Let $\mathcal{B}_q^m(\delta)$ denote a primitive, narrow-sense $q$-ary BCH code of length $n=q^m-1$ and designed distance $\delta$. Let $L_m(\nu)$ be the subspace of $\mathbb{F}_q[x_1,\dots,x_m]$ of polynomials of degree $\le\nu$, and $(P_0,\dots,P_{n-1})$ an enumeration of $\mathbb{F}_q^m$ with $P_0=\mathbf{0}$. The cyclic generalized Reed–Muller code of order $\nu$, length $n=q^m-1$, is $\mathrm{RM}^*_q(\nu,m)=\{\,\mathrm{ev}\,f\mid f\in L_m(\nu)\,\}$ with $\mathrm{ev}\,f=(f(P_1),\dots,f(P_{n-1}))$. Its dimension is $k^*(\nu)=\sum_{j=0}^m(-1)^j\binom{m}{j}\binom{m+\nu-jq}{\nu-jq}$, and minimum distance $d^*(\nu)=(R+1)q^Q-1$ where $m(q-1)-\nu=(q-1)Q+R$, $0\le R<q-1$. Its dual is $\mathrm{RM}^*_q(\nu,m)^\perp=\{\mathrm{ev}\,f\mid f\in L_m^*(\nu^\perp)\}$ (eq. RMdualdefn), where $\nu^\perp=m(q-1)-\nu-1$ and $L_m^*(\nu)$ is the subspace of nonconstant polynomials in $L_m(\nu)$.

<a id="pdf-4bcdc0ee9c86-p015-b006"></a>
<!-- pdf-source: page=15; block=6; confidence=0.91 -->
A primitive, narrow-sense BCH code contains a cyclic generalized RM code [kasami68, Thm 5]; the largest such subcode is determined next.

<a id="pdf-4bcdc0ee9c86-p015-b007"></a>
<!-- pdf-source: page=15; block=7; confidence=0.94 -->
**Lemma.** $\mathrm{RM}^*_q(\nu,m)\subseteq\mathcal{B}_q^m(\delta)$ for $\nu=(m-Q)(q-1)-R$, with $Q=\lfloor\log_q(\delta+1)\rfloor$ and $R=\lceil(\delta+1)/q^Q\rceil-1$. For all orders $\nu'>\nu$, $\mathrm{RM}^*_q(\nu',m)\not\subseteq\mathcal{B}_q^m(\delta)$.

<a id="pdf-4bcdc0ee9c86-p015-b008"></a>
<!-- pdf-source: page=15; block=8; confidence=0.90 -->
**Proof.** With $d^*(\nu)=(R+1)q^Q-1$ and $m(q-1)-\nu=(q-1)Q+R$, [kasami68, Thm 5] gives $\mathrm{RM}^*_q(\nu,m)\subseteq\mathcal{B}_q^m((R+1)q^Q-1)$. Since $(R+1)q^Q-1=\lceil(\delta+1)/q^Q\rceil q^Q-1\ge\delta$, we have $\mathcal{B}_q^m((R+1)q^Q-1)\subseteq\mathcal{B}_q^m(\delta)$, so $\mathrm{RM}^*_q(\nu,m)\subseteq\mathcal{B}_q^m(\delta)$.

For the second claim, show $\mathrm{RM}^*_q(\nu+1,m)\not\subseteq\mathcal{B}_q^m(\delta)$ via $d^*(\nu+1)<\delta$. Here $m(q-1)-(\nu+1)=(q-1)Q+R-1$ for $R\ge 1$, and $=(q-1)(Q-1)+q-2$ for $R=0$. Hence $d^*(\nu+1)=(\lceil(\delta+1)/q^Q\rceil-1)q^Q-1$ for $R\ge1$, and $=(q-1)q^{Q-1}-1$ for $R=0$; in both cases $d^*(\nu+1)<\delta$.

<a id="pdf-4bcdc0ee9c86-p015-b009"></a>
<!-- pdf-source: page=15; block=9; confidence=0.10 -->
**Theorem.** If $\delta<q^{\lfloor m/2\rfloor}-1$, then $\mathrm{RM}^*_q(\mu,m)\subseteq P_e(\mathcal{B}_q^m(\delta)^\perp)$ for all orders $\mu$ with $0\le\mu\le m(q-1)-2(R+(q-1)Q)+1$, where $Q=\lfloor\log_q(\delta+1)\rfloor$ and $R=\lceil(\delta+1)/q^Q\rceil-1$.

<a id="pdf-4bcdc0ee9c86-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.95 -->
**Proof.** By the "largest RM in BCH" lemma, $\RM_q^*(\nu,m)\subseteq\B_q^m(\delta)$ with $\nu=(m-Q)(q-1)-R$, so $\B_q^m(\delta)^\perp\subseteq\RM_q^*(\nu,m)^\perp$ and by definition of the puncture code $\pc_e(\B_q^m(\delta)^\perp)\supseteq\pc_e(\RM_q^*(\nu,m)^\perp)$. Moreover $\pc_e(\RM_q^*(\nu,m)^\perp)=\{ev f\cdot ev g\mid f,g\in L_m^*(\nu^\perp)\}^\perp\supseteq\{ev f\mid f\in L_m^*(2\nu^\perp)\}^\perp=\RM_q^*((2\nu^\perp)^\perp,m)$, the last equality by (eq:RMdualdefn). This needs $(2\nu^\perp)^\perp\geq0$, equivalently $\nu\geq(m(q-1)-1)/2$. Since $\delta<q^{\lfloor m/2\rfloor}-1$, we get $Q\leq\lfloor m/2\rfloor-1$ and $\nu=(m-Q)(q-1)-R\geq\lceil m/2+1\rceil(q-1)-R\geq\lceil m/2\rceil(q-1)+1\geq(m(q-1)-1)/2$. As $\RM_q^*(\mu,m)\subseteq\RM_q^*((2\nu^\perp)^\perp,m)$ for $0\leq\mu\leq(2\nu^\perp)^\perp$, conclude $\RM_q^*(\mu,m)\subseteq\pc_e(\B_q^m(\delta)^\perp)$. $\square$

<a id="pdf-4bcdc0ee9c86-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.95 -->
Weight distribution of generalized cyclic Reed–Muller codes is unknown; but $\pc_e(\B_q^m(\delta)^\perp)$ contains the nested chain $\RM_q^*(0,m)\subseteq\cdots\subseteq\RM_q^*(m(q-1)-2(R+(q-1)Q)+1,m)$, hence codewords of their respective minimum distances.

<a id="pdf-4bcdc0ee9c86-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.96 -->
**Corollary (th:bchpunc).** For integers $2\leq\delta<q^{\lfloor m/2\rfloor}-1$ and $0\leq\mu\leq m(q-1)-2(R+(q-1)Q)+1$, where $Q=\lfloor\log_q(\delta+1)\rfloor$ and $R=\lceil(\delta+1)/q^Q\rceil-1$, there exists a $[[d^*(\mu),\geq d^*(\mu)-2m\lceil(\delta-1)(1-1/q)\rceil,\geq\delta]]_q$ stabilizer code of length $d^*(\mu)=(\rho+1)q^\sigma-1$, where $\sigma,\rho$ satisfy $m(q-1)-\mu=(q-1)\sigma+\rho$ and $0\leq\rho<q-1$.

<a id="pdf-4bcdc0ee9c86-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.95 -->
**Proof.** For $2\leq\delta<q^{\lfloor m/2\rfloor}-1$, Theorem (co:bcheuclideandual) gives a $[[q^m-1,\,q^m-1-2m\lceil(\delta-1)(1-1/q)\rceil,\geq\delta]]_q$ code. Lemma (th:bchP(C)) gives $\pc_e(\B_q^m(\delta)^\perp)\supseteq\RM_q^*(\mu,m)$ for $0\leq\mu\leq m(q-1)-2(q-1)Q-2R+1$. By Theorem (th:punc_symplectic), a weight-$r$ vector in $\pc_e(\B_q^m(\delta)^\perp)$ punctures the code to $[[r,\geq r-2m\lceil(\delta-1)(1-1/q)\rceil,d\geq\delta]]_q$. The minimum distance of $\RM_q^*(\mu,m)$ is $d^*(\mu)=(\rho+1)q^\sigma-1$, $0\leq\rho<q-1$ [kasami68, Thm 5], giving the stated code. $\square$

<a id="pdf-4bcdc0ee9c86-p016-b005"></a>
<!-- pdf-source: page=16; block=5; confidence=0.94 -->
Quantum codes from Hermitian-self-orthogonal classical codes can also be punctured; see [grassl04], [klappenecker05p1].

<a id="pdf-4bcdc0ee9c86-p016-b006"></a>
<!-- pdf-source: page=16; block=6; confidence=0.97 -->
## MDS Codes

A quantum code attaining the quantum Singleton bound is a quantum MDS code. This section studies the maximal length of MDS stabilizer codes.

<a id="pdf-4bcdc0ee9c86-p016-b007"></a>
<!-- pdf-source: page=16; block=7; confidence=0.97 -->
**Lemma (Rains, th:d_purity).** An $[[n,k,d]]_q$ quantum MDS code with $k\geq1$ is pure up to $n-d+2$.

<a id="pdf-4bcdc0ee9c86-p016-b008"></a>
<!-- pdf-source: page=16; block=8; confidence=0.97 -->
**Corollary (th:mds_purity).** All quantum MDS codes are pure.

<a id="pdf-4bcdc0ee9c86-p016-b009"></a>
<!-- pdf-source: page=16; block=9; confidence=0.96 -->
**Proof.** If $k=0$ the code is pure by definition; if $k\geq1$ it is pure up to $n-d+2$. The quantum Singleton bound $n-2d+2=k\geq0$ gives $n-d+2\geq d$, so the code is pure. $\square$

<a id="pdf-4bcdc0ee9c86-p016-b010"></a>
<!-- pdf-source: page=16; block=10; confidence=0.96 -->
**Lemma (th:mds_classical).** For any $[[n,n-2d+2,d]]_q$ quantum MDS stabilizer code with $n-2d+2>0$, the corresponding classical codes $C\subseteq C^{\adual}$ are also MDS.

<a id="pdf-4bcdc0ee9c86-p016-b011"></a>
<!-- pdf-source: page=16; block=11; confidence=0.96 -->
**Proof.** By Theorem (th:alternating), the $[[n,n-2d+2,d]]_q$ code yields an additive $[n,d-1]_{q^2}$ code $C$ with $C\subseteq C^{\adual}$. By Corollary (th:mds_purity), $C^{\adual}$ has minimum distance $d$, so $C^{\adual}$ is an $[n,n-d+1,d]_{q^2}$ MDS code. By Lemma (th:d_purity), $\wt(C)\geq n-d+2$, so $C$ is an $[n,d-1,n-d+2]_{q^2}$ MDS code. $\square$

<a id="pdf-4bcdc0ee9c86-p016-b012"></a>
<!-- pdf-source: page=16; block=12; confidence=0.93 -->
**Definition.** A classical $[n,k,d]_q$ MDS code is *trivial* if $k\leq1$ or $k\geq n-1$. Trivial MDS codes can have arbitrary length; nontrivial ones cannot.

<a id="pdf-4bcdc0ee9c86-p016-b013"></a>
<!-- pdf-source: page=16; block=13; confidence=0.96 -->
**Lemma (th:mds_nontrivial).** For a classical additive $(n,q^k,d)_q$ MDS code $C$: (i) if trivial, arbitrary length; (ii) if nontrivial, then $2\leq k\leq\min\{n-2,q-1\}$ and $n\leq q+k-1\leq 2q-2$.

<a id="pdf-4bcdc0ee9c86-p016-b014"></a>
<!-- pdf-source: page=16; block=14; confidence=0.95 -->
**Proof.** (i) obvious. (ii) By the MacWilliams relations (the linear proof of [macwilliams77, p.320–321] applies unchanged), the number of weight-$(n-k+2)$ codewords is $A_{n-k+2}=\binom{n}{k-2}(q-1)(q-n+k-1)$. Nonnegativity of $A_{n-k+2}$ yields the claim. $\square$

<a id="pdf-4bcdc0ee9c86-p016-b015"></a>
<!-- pdf-source: page=16; block=15; confidence=0.93 -->
**Definition.** A quantum $[[n,k,d]]_q$ MDS code is *trivial* iff $d\leq2$. Trivial ones have unbounded length; nontrivial ones are length-bounded (next lemma).

<a id="pdf-4bcdc0ee9c86-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.96 -->
**Theorem (th:mds_length, Maximal Length of MDS Stabilizer Codes).** A nontrivial $[[n,k,d]]_q$ MDS stabilizer code satisfies: (i) $4\leq n\leq q^2+d-2\leq 2q^2-2$; (ii) $\max\{3,\,n-q^2+2\}\leq d\leq\min\{n-1,\,q^2\}$.

<a id="pdf-4bcdc0ee9c86-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.95 -->
**Proof.** Singleton bound $n-2d+2=k\geq0$ gives $n\geq2d-2\geq4$ for nontrivial codes. By Lemma (th:mds_classical), the code yields classical MDS codes $C=[n,d-1,n-d+2]_{q^2}$ and $C^{\adual}=[n,n-d+1,d]_{q^2}$; for $n\geq4$, $d\leq(n+2)/2\leq n-1$, so $C$ is nontrivial. By Lemma (th:mds_nontrivial), $2\leq d-1\leq\min\{n-2,q^2-1\}$, i.e. $3\leq d\leq\min\{n-1,q^2\}$, and $n\leq q^2+(d-1)-1\leq 2q^2-2$. Combining gives the claim. $\square$

<a id="pdf-4bcdc0ee9c86-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.95 -->
**Example.** For $q=2$, nontrivial MDS stabilizer code length cannot exceed $2q^2-2=6$; the only ones [calderbank98] are $[[5,1,3]]_2$ and $[[6,0,4]]_2$, so no further ones exist.

<a id="pdf-4bcdc0ee9c86-p017-b004"></a>
<!-- pdf-source: page=17; block=4; confidence=0.92 -->
Motivated by [grassl04] (all its MDS stabilizer codes had length $\leq q^2$), the classical MDS conjecture is invoked.

<a id="pdf-4bcdc0ee9c86-p017-b005"></a>
<!-- pdf-source: page=17; block=5; confidence=0.96 -->
**MDS Conjecture.** If a nontrivial $[n,k]_q$ MDS code exists, then $n\leq q+1$, except when $q$ is even and $k=3$ or $k=q-1$, in which case $n\leq q+2$.

<a id="pdf-4bcdc0ee9c86-p017-b006"></a>
<!-- pdf-source: page=17; block=6; confidence=0.95 -->
**Corollary.** If the classical MDS conjecture holds, no nontrivial MDS stabilizer codes have length exceeding $q^2+1$, except when $q$ is even and $d=4$ or $d=q^2$, in which case $n\leq q^2+2$.

<a id="pdf-4bcdc0ee9c86-p017-b007"></a>
<!-- pdf-source: page=17; block=7; confidence=0.95 -->
## Quantum Character Codes

Group character codes [ding00] resemble binary Reed–Muller codes but are defined over nonbinary fields. This section derives quantum codes from them via the CSS construction.

<a id="pdf-4bcdc0ee9c86-p017-b008"></a>
<!-- pdf-source: page=17; block=8; confidence=0.95 -->
**Definition (Group character codes).** Let $G$ be an additive abelian group of order $n$ and exponent $m$, and $\F_q$ a finite field with $\gcd(n,q)=1$ and $m\mid q-1$. The characters $\Hom(G,\F_q^*)=\{\chi_x\mid x\in G\}$ form a group isomorphic to $G$, indexed so $\chi_0$ is trivial and $\chi_{-x}=\chi_x^{-1}$.

<a id="pdf-4bcdc0ee9c86-p017-b009"></a>
<!-- pdf-source: page=17; block=9; confidence=0.90 -->
**Definition.** For $X\subseteq G$, the character code is $C_X=\{c\in\F_q^n\mid\sum_{i=0}^{n-1}c_i\chi_{x_i}(y)=0\ \forall y\in X\}$, an $[n,k]_q$ code with $n=|G|$, $k=n-|X|$. With $X=\{x_0,\dots,x_{n-k-1}\}$, the parity-check matrix is $H_X=(\chi_{x_j}(x_i))$ (rows $i=0..n-k-1$, cols $j=0..n-1$) and the generator matrix (eq:def_grp2) is $G_X=(\chi_{x_j}(-x_i))$ for rows $i=n-k..n-1$. The orthogonality relation $\sum_{x\in G}\chi_x(y)\chi_x(z)=n$ if $y+z=\mathbf0$ else $0$ implies $G_X H_X^T=0$.

<a id="pdf-4bcdc0ee9c86-p017-b010"></a>
<!-- pdf-source: page=17; block=10; confidence=0.94 -->
**Definition (Elementary abelian 2-groups).** Take $G=\mathbf Z_2^m$, $m\geq1$, and $\F_q$ of odd characteristic (so $2\mid q-1$, $\gcd(2^m,q)=1$); characters are $\chi_x(y)=(-1)^{x\cdot y}$. Define $\mathcal C_q(r,m)=C_X$ with $X=\{x\in\mathbf Z_2^m\mid \mathrm{wt}(x)>r\}$. It is an $[n,k(r),d(r)]_q$ code with (eq:grp2_dim) $k(r)=\sum_{j=0}^r\binom mj$ and $d(r)=2^{m-r}$ [ding00, Lemma 4, Thm 6].

<a id="pdf-4bcdc0ee9c86-p017-b011"></a>
<!-- pdf-source: page=17; block=11; confidence=0.97 -->
**Lemma (th:grp2_contain).** If $r_1\leq r_2$, then $\mathcal C_q(r_1,m)\subseteq\mathcal C_q(r_2,m)$.

<a id="pdf-4bcdc0ee9c86-p017-b012"></a>
<!-- pdf-source: page=17; block=12; confidence=0.94 -->
**Proof.** By (eq:def_grp2) the generator rows of $\mathcal C_q(r,m)$ are $(\chi_{x_0}(x_i),\dots,\chi_{x_{n-1}}(x_i))=(\chi_{x_0}(-x_i),\dots)$ for $x_i$ with $\wt(x_i)\leq r$. Hence the generator matrix of $\mathcal C_q(r_1,m)$ is a submatrix of that of $\mathcal C_q(r_2,m)$, giving the inclusion. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.97 -->
**Lemma (th:grp2_dual).** The dual $\mathcal C_q(r,m)^\perp$ is equivalent to $\mathcal C_q(m-r-1,m)$.

<a id="pdf-4bcdc0ee9c86-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.97 -->
**Proof.** See [ding00, Theorem 8]. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.96 -->
**Theorem (th:grp2_css0).** If $0\leq r_1<r_2\leq m$ and $q$ is a power of an odd prime, there exists an $[[n,\,k(r_2)-k(r_1),\,\min\{2^{m-r_2},2^{r_1+1}\}]]_q$ quantum code, where $n=2^m$ and $k(r)$ is as in (eq:grp2_dim).

<a id="pdf-4bcdc0ee9c86-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.95 -->
**Proof.** For $r_1<r_2$, $C_1=\mathcal C_q(r_1,m)\subseteq\mathcal C_q(r_2,m)=C_2$ by Lemma (th:grp2_contain). From (eq:grp2_dim), $\wt(C_2\setminus C_1)=2^{m-r_2}$; and by Lemma (th:grp2_dual), $\wt(C_1^\perp\setminus C_2^\perp)=\wt(\mathcal C_q(m-r_1-1)\setminus\mathcal C_q(m-r_2-1))=2^{r_1+1}$. By the CSS lemma (th:css), an $[[n,k(r_2)-k(r_1),\min\{2^{m-r_2},2^{r_1+1}\}]]_q$ stabilizer code exists. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.94 -->
More quantum codes could come from puncturing, but only the weight distribution of $\mathcal C_q(1,m)$ is known, so available codes are undetermined.

<a id="pdf-4bcdc0ee9c86-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.92 -->
## Code Constructions

Collects simple facts for constructing stabilizer codes. Lemmas (th:lengthening)–(th:smallerdim) lengthen, shorten, or reduce the dimension of a stabilizer code. Table (table:cc) summarizes how a pure $[[n,k,d]]_q$ code implies codes at neighboring $(n\pm1,k\pm1)$ parameters (e.g. $[[n-1,k+1,d-1]]$ pure, $[[n+1,k,d]]$ impure, $[[n,k-1,d]]$ pure).

<a id="pdf-4bcdc0ee9c86-p018-b007"></a>
<!-- pdf-source: page=18; block=7; confidence=0.97 -->
**Lemma (th:lengthening).** If an $[[n,k,d]]_q$ stabilizer code exists with $k>0$, then an impure $[[n+1,k,d]]_q$ stabilizer code exists.

<a id="pdf-4bcdc0ee9c86-p018-b008"></a>
<!-- pdf-source: page=18; block=8; confidence=0.92 -->
**Proof.** The code gives an additive $C\leq\F_q^{2n}$ with $|C|=q^{n-k}$, $C\leq C^{\sdual}$, $\swt(C^{\sdual}\setminus C)=d$. Define $C'=\{(a\alpha\mid b0)\mid\alpha\in\F_q,(a\mid b)\in C\}$; then $|C'|=q^{n-k+1}$ and $C'$ is trace-symplectic self-orthogonal since $\langle(a\alpha\mid b0)\mid(a'\alpha'\mid b'0)\rangle_s=\langle(a\mid b)\mid(a'\mid b')\rangle_s+\tr(\alpha\cdot0-\alpha'\cdot0)=0$. Its dual consists of $(a\alpha\mid b0)$ with $(a\mid b)\in C^{\sdual}$, $\alpha\in\F_q$, and $\swt(C'^{\sdual}\setminus C')=\swt(C^{\sdual}\setminus C)=d$. By Theorem (th:stabilizer) an $[[n+1,k,d]]_q$ code exists; if $d>1$ it is impure since $C'^{\sdual}$ contains $(0\alpha\mid00)$ of symplectic weight 1. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b009"></a>
<!-- pdf-source: page=18; block=9; confidence=0.97 -->
**Lemma (th:shorterlength).** If a pure $[[n,k,d]]_q$ stabilizer code exists with $n\geq2$ and $d\geq2$, then a pure $[[n-1,k+1,d-1]]_q$ stabilizer code exists.

<a id="pdf-4bcdc0ee9c86-p018-b010"></a>
<!-- pdf-source: page=18; block=10; confidence=0.10 -->
**Proof.** The pure code gives trace-alternating self-orthogonal $D\leq\F_{q^2}^n$ with $|D|=q^{n-k}$, $\wt(D^{\adual})=d$. Let $D_0^{\adual}$ be $D^{\adual}$ punctured in the first coordinate; since $\wt(D^{\adual})\geq2$, $|D_0^{\adual}|=|D^{\adual}|$ and $\wt(D_0^{\adual})=d-1$. Its dual is $\{u\in\F_{q^2}^{n-1}\mid 0u\in D\}=D_0$, which is self-orthogonal; $|D_0|=q^{(n-1)-(k+1)}$ from $\dim D_0+\dim D_0^{\adual}=\dim\F_{q^2}^{n-1}$ (as $\F_p$-spaces). Hence a pure $[[n-1,k+1,d-1]]_q$ code exists. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b011"></a>
<!-- pdf-source: page=18; block=11; confidence=0.96 -->
**Lemma (th:smallerdim).** If a (pure) $[[n,k,d]]_q$ stabilizer code exists with $k\geq2$ ($k\geq1$ in the pure case), then a (pure) $[[n,k-1,d^*]]_q$ stabilizer code exists with $d^*\geq d$.

<a id="pdf-4bcdc0ee9c86-p018-b012"></a>
<!-- pdf-source: page=18; block=12; confidence=0.93 -->
**Proof.** The code gives $D\leq\F_{q^2}^n$ with $D\leq D^{\adual}$, $\wt(D^{\adual}\setminus D)=d$, $|D|=q^{n-k}$. Choose $D_b$ with $|D_b|=q^{n-k+1}$ and $D\leq D_b\leq D^{\adual}$; then $D_b^{\adual}\leq D^{\adual}$ and $\Sigma_b=D_b^{\adual}\setminus D_b\subseteq D^{\adual}\setminus D$, so its minimum weight $d^*\geq d$, giving an $[[n,k-1,d^*]]$ code. If pure, $\wt(D^{\adual})=d$ and $D_b^{\adual}\leq D^{\adual}$ give $\wt(D_b^{\adual})\geq d$, so the smaller code is pure. $\square$

<a id="pdf-4bcdc0ee9c86-p018-b013"></a>
<!-- pdf-source: page=18; block=13; confidence=0.96 -->
**Corollary.** If a pure $[[n,k,d]]_q$ stabilizer code with $n\geq2$ and $d\geq2$ exists, then a pure $[[n-1,k,d-1]]_q$ stabilizer code exists.

<a id="pdf-4bcdc0ee9c86-p018-b014"></a>
<!-- pdf-source: page=18; block=14; confidence=0.96 -->
**Proof.** Combine Lemmas (th:shorterlength) and (th:smallerdim). $\square$

<a id="pdf-4bcdc0ee9c86-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.10 -->
**Lemma (direct sum).** If an $((n,K,d))_q$ and an $((n',K',d'))_q$ stabilizer code exist, then an $((n+n',\,KK',\,\min(d,d')))_q$ stabilizer code exists.

<a id="pdf-4bcdc0ee9c86-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=0.10 -->
**Proof.** Let $P,P'$ be the orthogonal projectors onto the two codes. Then $P\otimes P'$ projects onto a $KK'$-dimensional subspace $Q^*$ of $\mathbb{C}^{q^{n+n'}}$. With stabilizer groups $S,S'$, the group $S^*=\{E\otimes E'\mid E\in S,\,E'\in S'\}$ stabilizes $Q^*$. If $F\otimes F'\in G_{n+n'}$ is not detectable, then $F$ commutes with all of $S$ and $F'$ with all of $S'$. Both $F\in Z(G_n)S$ and $F'\in Z(G_{n'})S'$ cannot hold simultaneously (that would make $F\otimes F'$ detectable), so either $F$ or $F'$ is undetectable; hence $\operatorname{wt}(F\otimes F')\ge\min(d,d')$. $\blacksquare$

<a id="pdf-4bcdc0ee9c86-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.10 -->
**Lemma.** Let $Q_1,Q_2$ be pure stabilizer codes with parameters $[[n,k_1,d_1]]_q$ and $[[n,k_2,d_2]]_q$. If $Q_2\subseteq Q_1$, then a pure $[[2n,\,k_1+k_2,\,d]]_q$ stabilizer code exists with $d\ge\min\{2d_2,d_1\}$.

<a id="pdf-4bcdc0ee9c86-p019-b004"></a>
<!-- pdf-source: page=19; block=4; confidence=0.88 -->
**Proof.** The hypotheses give additive subcodes $D_1\le D_2\le\mathbb{F}_{q^2}^n$ with $D_m\le D_m^{\perp_a}$, $|D_m|=q^{n-k_m}$, $\operatorname{wt}(D_m^{\perp_a})=d_m$. Set $D=\{(u,u+v)\mid u\in D_1,\,v\in D_2\}\le\mathbb{F}_{q^2}^{2n}$, so $|D|=q^{2n-(k_1+k_2)}$. Its trace-alternating dual is $D^{\perp_a}=\{(u'+v',v')\mid u'\in D_1^{\perp_a},\,v'\in D_2^{\perp_a}\}$: one checks $\langle(u,u+v)\mid(u'+v',v')\rangle_a=\langle u\mid u'+v'\rangle_a+\langle u+v\mid v'\rangle_a=0$. Thus $D\le D^{\perp_a}$ (self-orthogonal), and any $(u'+v',v')\in D^{\perp_a}\setminus D$ has weight $\ge\min\{2d_2,d_1\}$. $\blacksquare$

<a id="pdf-4bcdc0ee9c86-p019-b005"></a>
<!-- pdf-source: page=19; block=5; confidence=0.92 -->
**Lemma (difference).** Let $q$ be an even prime power. If a pure $[[n,k_1,d_1]]_q$ code $Q_1$ has a pure subcode $Q_2\subseteq Q_1$ with parameters $[[n,k_2,d_2]]_q$ and $k_1>k_2$, then a pure $[[2n,\,k_1-k_2,\,d]]_q$ stabilizer code exists with $d\ge\min\{2d_1,d_2\}$.

<a id="pdf-4bcdc0ee9c86-p019-b006"></a>
<!-- pdf-source: page=19; block=6; confidence=0.10 -->
**Proof.** Take additive codes $D_m\le\mathbb{F}_{q^2}^n$ with $D_m\le D_m^{\perp_a}$, $\operatorname{wt}(D_m^{\perp_a})=d_m$, $|D_m|=q^{n-k_m}$; the inclusion $Q_2\subseteq Q_1$ gives $D_1\le D_2$. Let $D=\{(u,u+v)\mid u\in D_2^{\perp_a},\,v\in D_1\}$. Claim: $D^{\perp_a}=\{(u',u'+v')\mid u'\in D_1^{\perp_a},\,v'\in D_2\}$. Expanding $\langle v_1\mid v_2\rangle_a=\langle u\mid u'\rangle_a+\langle u\mid u'\rangle_a+\langle u\mid v'\rangle_a+\langle v\mid u'\rangle_a+\langle v\mid v'\rangle_a$: the first two cancel (even characteristic), the next two vanish (dual spaces), the last vanishes ($v,v'\in D_2$ self-orthogonal); so $v_1\perp v_2$. The claimed set has cardinality $q^{2n+k_1-k_2}$ [as written], forcing equality by dimension. Any $(u',u'+v')\in D^{\perp_a}$ has weight $\ge\min\{2d_1,d_2\}$ since $u'\in D_1^{\perp_a}$ and $v'\in D_2\le D_2^{\perp_a}$. $\blacksquare$

<a id="pdf-4bcdc0ee9c86-p019-b007"></a>
<!-- pdf-source: page=19; block=7; confidence=0.95 -->
**Lemma (code expansion).** Let $q$ be a prime power. If an $((n,K,d))_{q^m}$ stabilizer code exists, then an $((nm,K,\ge d))_q$ stabilizer code exists. Conversely, if an $((nm,K,d))_q$ stabilizer code exists, then an $((n,K,\ge\lfloor d/m\rfloor))_{q^m}$ stabilizer code exists.

<a id="pdf-4bcdc0ee9c86-p019-b008"></a>
<!-- pdf-source: page=19; block=8; confidence=0.97 -->
Remark: this lemma is implicitly contained in Ashikhmin and Knill [ashikhmin01].

<a id="pdf-4bcdc0ee9c86-p019-b009"></a>
<!-- pdf-source: page=19; block=9; confidence=0.86 -->
**Proof.** Let $B=\{\beta_1,\dots,\beta_m\}$ be a basis of $\mathbb{F}_{q^m}/\mathbb{F}_q$. The map $(x,y)\mapsto\operatorname{tr}_{q^m/q}(xy)$ is a nondegenerate symmetric form, so the Gram matrix $M=(\operatorname{tr}_{q^m/q}(\beta_i\beta_j))_{1\le i,j\le m}$ is nonsingular and $\operatorname{tr}_{q^m/q}(xy)=e_B(x)^tM\,e_B(y)$, where $e_B(a)=(a_1,\dots,a_m)$ with $a=\sum_i a_i\beta_i$. Define the $\mathbb{F}_p$-isomorphism $\varphi_B:\mathbb{F}_{q^m}^{2n}\to\mathbb{F}_q^{2nm}$ by $\varphi_B((a\mid b))=((e_B(a_1),\dots,e_B(a_n))\mid(M e_B(b_1),\dots,M e_B(b_n)))$. Using $\operatorname{tr}_{q^m/q}(\operatorname{tr}_{q/p}(x))=\operatorname{tr}_{q^m/p}(x)$, one has $(a\mid b)\perp_s(c\mid d)$ iff $\varphi_B((a\mid b))\perp_s\varphi_B((c\mid d))$. If an $((n,K,d))_{q^m}$ code exists there is an additive $C\le\mathbb{F}_{q^m}^{2n}$, $|C|=q^{nm}/K$, $C\le C^{\perp_s}$, with $\operatorname{swt}(C^{\perp_s}\setminus C)=d$ ($K>1$) or $\operatorname{swt}(C^{\perp_s})=d$ ($K=1$). Then $\varphi_B(C)$ over $\mathbb{F}_q$ has size $q^{nm}/K$, satisfies $\varphi_B(C)\le\varphi_B(C)^{\perp_s}$ with the same swt property, giving an $((nm,K,d))_q$ code. Conversely, $\varphi_B^{-1}$ maps each nonzero block of $m$ symbols to a nonzero $\mathbb{F}_{q^m}$-symbol, yielding the stated minimum distance. $\blacksquare$

<a id="pdf-4bcdc0ee9c86-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->
Remark: if $q$ is even, or $q$ and $m$ are both odd, there is a basis $B$ making $M$ the identity, so $\varphi_B$ merely expands each symbol into its $B$-coordinates. No such basis exists when $q$ is odd and $m$ is even.

<a id="pdf-4bcdc0ee9c86-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.98 -->
## Conclusions and Open Problems

<a id="pdf-4bcdc0ee9c86-p020-b003"></a>
<!-- pdf-source: page=20; block=3; confidence=0.85 -->
Summary of the section: develops nonbinary stabilizer code theory over finite fields with Galois-theoretic methods relating them to general quantum codes, then derives many code families (see Table). Notes error-basis dependence (an alternative choice yields self-orthogonal additive subcodes of $\mathbb{Z}_q^n\times\mathbb{Z}_q^n$). Open problems stated: (i) assuming the classical MDS conjecture, an MDS stabilizer code over $\mathbb{F}_q$ has length $\le q^2+1$ except in sporadic cases — is length of a $q$-ary quantum MDS code $\le q^2+1$ for all but finitely many $n$? (ii) single and double error-correcting nonbinary stabilizer codes cannot beat the quantum Hamming bound; conjecture (unproved): no quantum error-correcting code exceeds the quantum Hamming bound. Omitted topics (tables of best codes, alternate constructions, encoding/decoding, combinatorics) and acknowledgments/funding noted.

<a id="pdf-4bcdc0ee9c86-p020-b004"></a>
<!-- pdf-source: page=20; block=4; confidence=0.80 -->
**Table (tb:families).** Families of quantum codes with $[[n,k,d]]_q$ parameters, purity, and ranges:

| Family | $[[n,k,d]]_q$ | Purity | Ranges / refs |
|---|---|---|---|
| Short MDS | $[[n,n-2d+2,d]]_q$ | pure | $2\le d\le\lceil n/2\rceil$, $q^2-1\ge\binom{n}{d}$ |
| Hermitian Hamming | $[[n,n-2m,3]]_q$ | pure | $m\ge2$, $\gcd(m,q^2-1)=1$, $n=(q^{2m}-1)/(q^2-1)$ |
| Euclidean Hamming | $[[n,n-2m,3]]_q$ | pure | $m\ge2$, $\gcd(m,q-1)=1$, $n=(q^m-1)/(q-1)$ |
| Quadratic Residue I | $[[n,1,d]]_q$ | pure | $n$ prime, $n\equiv3\ (4)$, $q\not\equiv0\ (n)$, $q$ a QR mod $n$, $d^2-d+1\ge n$ |
| Quadratic Residue II | $[[n,1,d]]_q$ | pure | $n$ prime, $n\equiv1\ (4)$, $q\not\equiv0\ (n)$, $q$ a QR mod $n$, $d\ge\sqrt{n}$ |
| Melas | $[[n,n-4m,\ge3]]_q$ | pure (to 3) | $q$ even, $n=q^{2m}-1$ |
| Euclidean BCH | $[[n,\,n-2m\lceil(\delta-1)(1-1/q)\rceil,\ge\delta]]_q$ | pure to $\delta$ | $2\le\delta\le q^{\lceil m/2\rceil}-1-(q-2)[m\text{ odd}]$, $n=q^m-1$, $m\ge2$ |
| Punctured BCH | $[[d^*(\mu),\ge d^*(\mu)-2m\lceil(\delta-1)(1-1/q)\rfloor,\ge\delta]]_q$ | pure? | $\delta<q^{\lfloor m/2\rceil}-1$, Cor. th:bchpunc |
| Hermitian BCH | $[[n,\,n-2m\lceil(\delta-1)(1-1/q^2)\rceil,\ge\delta]]_q$ | pure to $\delta$ | $2\le\delta\le q^m-1$, $n=q^{2m}-1$ |
| Extended BCH | $[[n+1,\,n-2m\lceil(\delta-1)(1-1/q^2)\rceil-1,\ge\delta+1]]_q$ | pure to $\delta+1$ | — |
| Trivial MDS | $[[n,n-2,2]]_q$; $[[n,n,1]]_q$ | pure | $n\equiv0\ (p)$; $n\ge1$ |
| Character | $[[n,\,k(r_2)-k(r_1),\,\min\{2^{m-r_2},2^{r_1+1}\}]]_q$ | pure | $n=2^m$, $q$ odd, $0\le r_1<r_2\le m$, $k(r)=\sum_{j=0}^r\binom{m}{j}$ |
| CSS GRM | $[[q^m,\,k(\nu_2)-k(\nu_1),\,\min\{d(\nu_2),d(\nu_1^\perp)\}]]_q$ | pure | $k(\nu)=\sum_{j=0}^m(-1)^j\binom{m}{j}\binom{m+\nu-jq}{\nu-jq}$, $\nu^\perp=m(q-1)-\nu-1$, $0\le\nu_1\le\nu_2\le m(q-1)-1$, $\nu^\perp+1=(q-1)Q+R$, $d(\nu)=(R+1)q^Q$ |
| Punctured GRM (CSS) | $[[d(\mu),\ge k(\nu_2)-k(\nu_1)-(n-d(\mu)),\ge d]]_q$ | pure? | $d\ge\min\{d(\nu_2),d(\nu_1^\perp)\}$, $0\le\mu\le\nu_2-\nu_1$; [klappenecker05p1] |
| Hermitian GRM | $[[q^{2m},\,q^{2m}-2k(\nu),\,d(\nu^\perp)]]_q$ | pure | $k(\nu)=\sum_{j=0}^m(-1)^j\binom{m}{j}\binom{m+\nu-jq^2}{\nu-jq^2}$, $\nu^\perp=m(q^2-1)-\nu-1$, $0\le\nu\le m(q-1)-1$, $\nu^\perp+1=(q^2-1)Q+R$, $d(\nu)=(R+1)q^{2Q}$ |
| Punctured GRM (Herm.) | $[[d(\mu^\perp),\ge d(\mu^\perp)-2k(\nu),\ge d(\nu^\perp)]]_q$ | pure? | $(\nu+1)q\le\mu\le m(q^2-1)-1$; [klappenecker05p1] |
| Punctured MDS | $[[q^2-q\alpha,\,q^2-q\alpha-2\nu-2,\,\nu+2]]_q$ | pure | $0\le\nu\le q-2$, $0\le\alpha\le q-\nu-1$; [klappenecker05p1] |
| Euclidean MDS | $[[n,n-2d+2,d]]_q$ | pure | $3\le n\le q$, $1\le d\le n/2+1$; [grassl03] |
| Hermitian MDS | $[[q^2-s,\,q^2-s-2d+2,\,d]]_q$ | pure | $1\le d\le q$, $s=0,1$; [grassl03] |
| Twisted | $[[q^2+1,q^2-3,3]]_q$ | pure? | [bierbrauer00] |
| Extended Twisted | $[[q^r,q^r-r-2,3]]_q$; $[[n,n-r-2,3]]_q$ | pure | $r\ge2$; and $n=(q^{r+2}-q^3)/(q^2-1)$, $r\ge1$ odd; [bierbrauer00] |
| Perfect | $[[n,n-r-2,3]]_q$ | pure | $n=(q^{r+2}-1)/(q^2-1)$, $r\ge2$ even; [bierbrauer00] |

<a id="pdf-4bcdc0ee9c86-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.96 -->
Bibliography (references, no mathematical content to index). Citation keys present on this page: aharonov97, preprint0501126, arvind03, ashikhmin01, ashikhmin99, ashikhmin01b, ashikhmin00a, ashikhmin00b, assmus92, assmus98, barg00, barnum00, barnum02, beth98, betten98, bierbrauer00, birkhoff61, calderbank97, calderbank98, calderbank96, camara05, charpin98, chau97, chau97b, chen01b, chen01, cleve97b, cleve97, cohen99, danielsen05, delsarte72, ding00, ekert96, feng02.

<a id="pdf-4bcdc0ee9c86-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.90 -->
**References (bibliography), part 1.** Reference-list entries [feng02b]–[macwilliams63], no mathematical content. Cited works concern quantum error-correcting and stabilizer codes (Feng; Feng–Ma finite Gilbert–Varshamov bound; Gottesman's quantum Hamming-bound-saturating codes, code pasting, stabilizer-code thesis, higher-dimensional fault tolerance, and surveys; Freedman–Meyer planar codes; Kitaev; Knill/Laflamme error bases and QEC theory; Klappenecker–Rötteler Clifford codes), quantum code families (Grassl et al. quantum BCH, cyclic, Reed–Solomon, MDS, and circuit constructions; Kim et al. codes from GF(4) self-orthogonal codes and algebraic curves; Li–Li distance-3/4 constructions; MacKay et al. sparse-graph codes), classical coding-theory texts and results (Grove; Hiramatsu–Köhler; Huffman–Pless; Kasami–Lin–Peterson generalized Reed–Muller; Lachaud–Wolfmann Goppa dual weights; Levenshtein Krawtchouk bounds; MacWilliams weight-distribution theorem), and related items (Ore Galois connexions; Matsumoto/Uyematsu bounds).

<a id="pdf-4bcdc0ee9c86-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.90 -->
**References (bibliography), part 2.** Reference-list entries [macwilliams77]–[xiaoyan04], concluding `\end{thebibliography}`; no mathematical content. Cited works include the MacWilliams–Sloane text; quantum-code bounds and introductions (Martin; Matsumoto Ashikhmin–Litsyn–Tsfasman improvement; Matsumoto–Uyematsu p^m-state constructions; McEliece et al. Delsarte–MacWilliams rate bounds); Rains's quantum weight/shadow enumerators, LP-bound monotonicity, nonbinary and minimum-distance-two codes, and polynomial invariants; graph/stabilizer-code equivalences (Schlingemann; Schlingemann–Werner); Shor and Shor–Laflamme foundational QEC and quantum MacWilliams identities; Steane's quantum Reed–Muller, CSS-code enlargement, and simple QEC codes; generalized Hamming weights and weight-distribution results (Stichtenoth–Voß; van der Geer–van der Vlugt Melas codes; Schoof et al.; Moreno et al. BCH-dual bounds); and further quantum constructions (Rötteler et al. MDS; Sarvepalli–Klappenecker nonbinary Reed–Muller; Thangaraj–McLaughlin cyclic GF(4^m) codes; Vatan et al. burst-correcting codes; Xiaoyan constacyclic codes; Postol quantum LDPC).
