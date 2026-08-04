<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 1ac7bb3b99ccdf62d030950bdeb31f5b8c6a3e1636142eadf899093d0203b829 -->

<a id="pdf-1ac7bb3b99cc-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Nonbinary Quantum Stabilizer Codes

Alexei Ashikhmin (Bell Laboratories, Lucent Technologies); Emanuel Knill (Los Alamos National Laboratory).

<a id="pdf-1ac7bb3b99cc-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
Constructs nonbinary quantum stabilizer codes from nonbinary error bases, generalizing the known correspondence between selforthogonal codes over $F_4$ and binary quantum codes to a correspondence between selforthogonal codes over $F_{q^2}$ and $q$-ary quantum codes for any prime power $q$.

<a id="pdf-1ac7bb3b99cc-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.98 -->
## 1 Introduction

<a id="pdf-1ac7bb3b99cc-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.88 -->
Quantum stabilizer codes (Shor; Steane; Gottesman; Calderbank et al.) are the central class of binary quantum codes, with the standard link to classical selforthogonal codes due to Calderbank et al. Nonbinary codes have been comparatively neglected; prior work (refs [10,11], Rains) treated codes over $Z_n$ / $p$-ary codes via nice error bases. This paper constructs $p^m$-ary quantum codes from classical selforthogonal codes over $F_{p^{2m}}$, where selforthogonality can be identified with that arising from a field-theoretically defined simplectic form; good selforthogonal codes with respect to this form (Bierbrauer and Edel) yield associated quantum codes.

<a id="pdf-1ac7bb3b99cc-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.98 -->
## 2 Basic Definitions

<a id="pdf-1ac7bb3b99cc-p001-b006"></a>
<!-- pdf-source: page=1; block=6; confidence=0.92 -->
**Definition.** $F_{p^m}$ is the Galois field of $p^m$ elements ($p$ prime). Fix a basis $\alpha_1,\dots,\alpha_m$ of $F_{p^m}$ over $F_p$ and a nonzero $F_p$-linear functional $\mathrm{tr}: F_{p^m}\to F_p$ (a **trace function**), satisfying

$$\mathrm{tr}(a+b)=\mathrm{tr}(a)+\mathrm{tr}(b),\qquad \mathrm{tr}(\alpha a)=\alpha\,\mathrm{tr}(a)$$

for $a,b\in F_{p^m}$, $\alpha\in F_p$. For $x\in F_{p^m}$, $\mathrm{tr}_x(a)=\mathrm{tr}(xa)$ is another trace function, and all trace functions arise this way. The standard trace is $\mathrm{tr}(a)=\sum_{i=0}^{m-1} a^{p^i}$.

<a id="pdf-1ac7bb3b99cc-p001-b007"></a>
<!-- pdf-source: page=1; block=7; confidence=0.92 -->
**Definition.** Let $t\mid m$. A classical $p^t$-linear code $C$ over $F_{p^m}$ of length $n$ and size $(p^t)^k$ is a $k$-dimensional $p^t$-linear subspace of $F_{p^m}^n$: for $a,b\in C$ and $\alpha,\beta\in F_{p^t}$, $\alpha a+\beta b\in C$. Given an $F_{p^t}$-bilinear form (inner product) $*$, $C$ is **selforthogonal** with respect to $*$ if for all $a,b\in C$

$$a * b = 0. \tag{1}$$

<a id="pdf-1ac7bb3b99cc-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.93 -->
**Definition.** The dual of $C$ with respect to $(1)$ is $C^{\perp}=\{v : v * a = 0 \ \forall a\in C\}$.

<a id="pdf-1ac7bb3b99cc-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.92 -->
**Definition.** A $q$-ary quantum code $Q$ of length $n$ and size $K$ is a $K$-dimensional subspace of a $q^n$-dimensional Hilbert space, identified with the $n$-fold tensor product of $q$-dimensional spaces $\mathbb{C}^q$. If $Q$ has minimum distance $d$ it can detect any $d-1$ errors and correct any $\lfloor (d-1)/2\rfloor$ errors; a precise definition of minimum distance follows after introducing error bases.

<a id="pdf-1ac7bb3b99cc-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.98 -->
## 3 Error Basis

<a id="pdf-1ac7bb3b99cc-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->
**Definition.** A general quantum error on a $p^m$-ary system is a linear operator on $\mathbb{C}^{p^m}$; on a state $|v\rangle$ it acts as $E|v\rangle$. Fix a basis $e_1,\dots,e_{p^{2m}}$ of the operator space on $\mathbb{C}^{p^m}$, with $e_1=I_{p^m}$ the identity. On $n$ systems, errors have the form

$$E=\sigma_1\otimes\sigma_2\otimes\cdots\otimes\sigma_n,\qquad \sigma_i\in\{e_1,e_2,\dots,e_{p^{2m}}\}. \tag{2}$$

Any operator on the $n$-fold tensor product of $\mathbb{C}^{p^m}$ is a linear combination of operators $(2)$, and correcting a set $\mathcal{E}$ of errors implies correcting their linear span, so attention restricts to operators of form $(2)$. The **weight** of $E$ in $(2)$ is

$$\mathrm{wt}(E)=|\{\,\sigma_i\neq I_{p^m}\,\}|. \tag{3}$$

<a id="pdf-1ac7bb3b99cc-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.90 -->
**Definition.** In the depolarizing channel model, $e_2,e_3,\dots$ satisfy $\mathrm{Tr}(e_i^\dagger e_j)=p^m\delta_{i,j}$. For a transmitted system the probability of being untouched (identity) is $1-r$ and of being hit by $e_i$ ($i>1$) is $r/(p^{2m}-1)$, so error probability decreases exponentially with weight, motivating correction/detection of all errors up to a given weight. Let $P$ be the orthogonal projection onto $Q$. An error $E$ is detectable by $Q$ iff

$$PEP = cEP \tag{4}$$

for a scalar $c$. The **minimum distance** is the largest $d$ such that every error of weight $\le d-1$ is detectable by the code.

<a id="pdf-1ac7bb3b99cc-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.85 -->
**Definition.** Define operators $T,R$ on $\mathbb{C}^p$ by

$$T_{i,j}=\delta_{i,\,j-1 \bmod p},\qquad R_{i,j}=\xi^i\delta_{i,j},$$

where $\xi=e^{\iota 2\pi/p}$, $\iota=\sqrt{-1}$, indices $0..p-1$. Then

$$TR=\xi RT, \tag{5}$$
$$T^iR^j=\xi^{ij}R^jT^i, \tag{6}$$
$$(T^iR^j)(T^kR^l)=\xi^{il-jk}(T^kR^l)(T^iR^j)=\xi^{-jk}T^{i+k}R^{j+l}. \tag{7}$$

Hermitian transposes: $(T^i)^\dagger=(T^i)^{p-1}$, $(R^i)^\dagger=(R^i)^{p-1}$. $\tag{8}$

<a id="pdf-1ac7bb3b99cc-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.86 -->
**Definition.** From the relations, $T^p=R^p=I_p$ $(9)$, and for $p>2$

$$(T^iR^j)^p=\xi^{-ij(1+2+\cdots+(p-1))}=I_p. \tag{10}$$

Since $\mathrm{Tr}(T^iR^j)=0$ except when $i\equiv j\equiv 0 \bmod p$, the $T^iR^j$ form an orthogonal operator basis under $\langle A,B\rangle=\mathrm{Tr}(A^\dagger B)$. For $a,b\in F_{p^m}$ written in the fixed basis as $a=\sum a_i\alpha_i$, $b=\sum b_i\alpha_i$ ($a_i,b_i\in F_p$), define

$$T_aR_b=(T^{a_1}\otimes\cdots\otimes T^{a_m})(R^{b_1}\otimes\cdots\otimes R^{b_m}),$$

an orthonormal basis, and $\langle a,b\rangle=\sum_{i=1}^m a_ib_i\in F_p$ $(11)$. Then

$$(T_aR_b)(T_cR_d)=\xi^{-\langle b,c\rangle}T_{a+c}R_{b+d}, \tag{12}$$
$$(T_aR_b)(T_cR_d)=\xi^{\langle a,d\rangle-\langle b,c\rangle}(T_cR_d)(T_aR_b). \tag{13}$$

<a id="pdf-1ac7bb3b99cc-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
## 4 Nonbinary Stabilizer Codes

<a id="pdf-1ac7bb3b99cc-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.87 -->
**Definition.** For $a=(a^{(1)},\dots,a^{(n)})$, $b=(b^{(1)},\dots,b^{(n)})\in F_{p^m}^n$ (superscripts label systems), the relevant error operators are

$$E_{a,b}=T_{a^{(1)}}R_{b^{(1)}}\otimes T_{a^{(2)}}R_{b^{(2)}}\otimes\cdots\otimes T_{a^{(n)}}R_{b^{(n)}}. \tag{14}$$

Define the inner product $\langle a,d\rangle=\sum_{i=1}^n \langle a^{(i)},d^{(i)}\rangle$ $(15)$ with $\langle\cdot,\cdot\rangle$ from $(11)$. Then

$$E_{a,b}E_{c,d}=\xi^{\langle a,d\rangle-\langle b,c\rangle}E_{c,d}E_{a,b}, \tag{16}$$
$$E_{a,b}E_{c,d}=\xi^{-\langle b,c\rangle}E_{a+c,\,b+d}, \tag{17}$$

and for $p>2$, $E_{a,b}^p=I_{p^{mn}}$ $(18)$.

<a id="pdf-1ac7bb3b99cc-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.85 -->
**Definition.** The operators $\mathcal{E}=\{\xi^i E_{a,b} : 0\le i\le p-1\}$ form a group of order $p^{2mn+1}$, with center $\mathcal{Z}$ generated by $\xi I$ (order $p$). A quantum stabilizer code is a joint eigenspace of a commutative subgroup $S\le\mathcal{E}$; assume $\mathcal{Z}\subseteq S$ (else extend $S$ by $\mathcal{Z}$), so $|S|=p^{r+1}$. Eigenspaces correspond to linear characters $\mu$ of $S$ with $\mu(\xi I)=\xi$; there are $p^r$ such characters. $Q$ is the eigenspace for a chosen $\mu$, with projection

$$P=\frac{1}{|S|}\sum_{E\in S}\bar\mu(E)E.
$$

Since $\mathrm{Tr}\,E=0$ for $E\in\mathcal{E}\setminus\mathcal{Z}$,

$$\dim Q=\mathrm{Tr}\,P=\frac{1}{|S|}\sum_{i=0}^{p-1}\bar\mu(\xi^i I)\,\mathrm{Tr}(\xi^i I)=\frac{1}{p^{r+1}}\sum_{i=0}^{p-1}p^{mn}=p^{mn-r}.$$

Hence $Q$ is an $[[n,\ mn-r]]_{p^m}$ quantum stabilizer code.

<a id="pdf-1ac7bb3b99cc-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.82 -->
Since the error basis is a tensor product of p-ary error bases, p^m-ary stabilizer codes can be treated as standard p-ary stabilizer codes (as with classical linear codes over F_{p^m}). To protect p^m-ary systems, the aim is to relate p^m-ary stabilizer codes to classical codes over F_{p^{2m}}.

<a id="pdf-1ac7bb3b99cc-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->
**Construction.** Let $\varphi$ be an isomorphism of the vector space $F_p^m$. Define $C=\{(a,\varphi^{-1}b):E_{a,b}\in S\}$, an $F_p$-linear code of length $2n$ and size $p^r$. Since all operators in $S$ commute, for any $(a,b),(a',b')\in C$,

$$\langle a,\varphi(b')\rangle-\langle a',\varphi(b)\rangle=0. \tag{19}$$

Hence $C$ is selforthogonal under the inner product $(a,b)*(a',b')=\langle a,\varphi(b')\rangle-\langle a',\varphi(b)\rangle$. $\varphi$ is later chosen to relate this product to the structure of $F_{p^m}$.

<a id="pdf-1ac7bb3b99cc-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.80 -->
**Claim.** The minimum distance of the stabilizer code defined by S equals min{ wt(v) : v ∈ C⊥ \ C }, where C⊥ is the dual of C w.r.t. (19) and, for v = (a,b) ∈ F_{p^m}^{2n}, wt(v) = |{ i : a(i) ≠ 0 or b(i) ≠ 0 }|. Let S⊥ = { ξ^i E_{a,b} : (a,b) ∈ C⊥ } be the operators commuting with all of S. The result follows from: E' is detectable iff E' ∉ S⊥ \ S.

<a id="pdf-1ac7bb3b99cc-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->
**Proof.** With $P$ the code projector, consider three cases for $E'$.

(1) $E'\in S$: $E'P=\frac{1}{|S|}\sum_{E\in S}\bar\mu((E')^\dagger E)\,E=\mu(E')P$, so $PE'P=\mu(E')P$ and $E'$ is detectable.

(2) $E'\notin S^\perp$: let $S_i=\{E\in S:E'E=\xi^i EE'\}$; by (16) and the hypothesis $|S_i|=|S|/p$. Then

$$|S|\,PE'P=\sum_{E\in S}\bar\mu(E)EE'P=E'\sum_{i=0}^{p-1}\sum_{E\in S_i}\xi^i P=E'\sum_{i=0}^{p-1}\xi^i P\,|S|/p \tag{21}$$
$$=0, \tag{22}$$

using (20). Hence $E'$ is detectable.

(3) $E'\in S^\perp\setminus S$: let $T$ be the commutative subgroup generated by $S$ and $E'$; extending the character $\mu$ to $T$ yields a subcode $Q'$ of $Q$ whose dimension is smaller by a factor $p$, so $Q$ is not an eigenspace of $E'$. Since $E'$ commutes with $S$ it preserves $Q$, so $PE'P$ is not proportional to $P$.

<a id="pdf-1ac7bb3b99cc-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.80 -->
**Standardization of φ.** The set of codes is independent of φ. Relative to the distinguished basis {α_i} of F_{p^m}, φ is an m×m matrix M over F_p defined by M_{i,j} = tr(α_i α_j). For a = (a_1,…,a_m), b = (b_1,…,b_m),

a^T M b = Σ_i Σ_j a_i b_j tr(α_i α_j) = Σ_i Σ_j tr(a_i b_j α_i α_j) = tr((Σ_i a_i α_i)(Σ_i b_i α_i)) = tr(ab). (20)

<a id="pdf-1ac7bb3b99cc-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.83 -->
**Standardized inner product.** The trace product is multiplication in F_{p^m}. For a, b ∈ F_{p^m}^n, ⟨a,b⟩* = Σ_i a(i) b(i). With this φ, C is self-orthogonal w.r.t.

(a,b)·(a',b') = tr( ⟨a, b'⟩* − ⟨a', b⟩* ). (23)

<a id="pdf-1ac7bb3b99cc-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.82 -->
**Construction.** Given a classical self-orthogonal code C with |C| = p^r and an F_p-basis v_i = (a_i, b_i), 0 ≤ i ≤ r−1, the p^r operators E_{a_i, φ(b_i)} together with ξ I_{p^{mn}} generate a commuting group of order p^{r+1}, defining an [[n, mn − r]]_{p^m} stabilizer code with minimum distance d = min{ wt(v) : v ∈ C⊥ \ C }.

<a id="pdf-1ac7bb3b99cc-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
In [5] a number of families of good classical codes selforthogonal with respect to the inner product

$$(\mathbf{a},\mathbf{b})*(\mathbf{a}',\mathbf{b}')=\langle\mathbf{a},\mathbf{b}'\rangle_*-\langle\mathbf{a}',\mathbf{b}\rangle_* \tag{24}$$

were constructed. Since a code selforthogonal with respect to (24) is also selforthogonal with respect to (23), our results establish a previously missing connection between the classical codes of [5] and quantum codes, so we already have many good nonbinary stabilizer codes. For instance, from [5] we can obtain quantum stabilizer codes with parameters $[[q^r,\,q^r-(r+2),\,3]]_q$, $[[q^2+1,\,q^2-3,\,3]]_q$, $[[(q^{r+2}-1)/(q^2-1),\,(q^{r+2}-1)/(q^2-1)-(r+2),\,3]]_q$ ($r$ even), $[[q^3(q^{r-1}-1)/(q^2-1),\,q^3(q^{r-1}-1)/(q^2-1)-(r+2),\,3]]_q$ ($r$ odd), and others.

<a id="pdf-1ac7bb3b99cc-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.85 -->
An F_{p^m}-linear code self-orthogonal w.r.t. (23) is automatically self-orthogonal w.r.t. (24). Since this fails for general F_p-linear codes, better codes self-orthogonal w.r.t. (23) are expected within the F_{p^m}-linear class.

<a id="pdf-1ac7bb3b99cc-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.95 -->
E. K. supported by funding from NSA and DOE.

<a id="pdf-1ac7bb3b99cc-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.90 -->
Bibliography (condensed): [1] Ashikhmin–Litsyn, upper bounds on quantum code size; [2],[3] Ashikhmin–Barg–Knill–Litsyn, Quantum Error Detection I & II; [4] Bennett–DiVincenzo–Smolin–Wootters, mixed-state entanglement and QECCs; [5] Bierbrauer–Edel, 'Quantum Twisted Codes'; [6],[7] Calderbank–Rains–Shor–Sloane, orthogonal geometry and codes over GF(4); [8],[9] Gottesman, Hamming-bound-saturating codes and thesis; [10],[11] Knill, nonbinary unitary error bases / group representations; [12] Knill–Laflamme, theory of QECCs; [13] Knill–Laflamme–Viola, QEC for general noise.

<a id="pdf-1ac7bb3b99cc-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.92 -->
Bibliography (condensed): [14] MacWilliams–Sloane, The Theory of Error-Correcting Codes; [15] Rains, nonbinary quantum codes; [16] Shor, prime factorization / discrete-log algorithms; [17] Shor, reducing decoherence in quantum memory; [18] Shor–Laflamme, quantum analog of MacWilliams identities; [19],[20] Steane, simple QEC codes and multiple-particle interference.
