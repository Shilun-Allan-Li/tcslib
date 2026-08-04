<!-- generated-by: proofmatch Claude visual repair (claude -p cleanup blocked by content filter; repaired from gs-rendered page images) -->
<!-- source-pdf-sha256: bbdd8e5c39493ec02f6852ab4a6ac223d49a452f0b7d0bd31df5f1982f095a2d -->

<a id="pdf-bbdd8e5c3949-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Theory of quantum error-correcting codes

Emanuel Knill and Raymond Laflamme, Los Alamos National Laboratory (Received 14 June 1996). Physical Review A, Volume 55, Number 2, February 1997, pages 900–911.

<a id="pdf-bbdd8e5c3949-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.95 -->
**Abstract.** Quantum error correction is needed to preserve coherent states against noise in quantum computation and communication. The paper develops a general theory of quantum error correction based on encoding states into larger Hilbert spaces subject to known interactions. It obtains necessary and sufficient conditions for perfect recovery of an encoded state after degradation by an interaction; the conditions depend only on the behavior of the logical states. These are used to give a recovery-operator-independent definition of error-correcting codes, related to four other characterizations: existence of a left inverse of the interaction, an explicit representation of the error syndrome using tensor products, perfect recovery of the completely entangled state, and an information-theoretic identity. Two notions of fidelity and error for imperfect recovery are introduced, for pure and for entangled states, and the error for entangled states is bounded linearly by the error for pure states. A formal definition of independent interactions for qubits leads to lower bounds on the number of qubits required to correct $e$ errors, and a proof that the classical bounds on the probability of error of $e$-error-correcting codes apply to $e$-error-correcting quantum codes provided the interaction is dominated by an identity component.

<a id="pdf-bbdd8e5c3949-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
## I. Introduction

Quantum computation and communication have evolved rapidly, but the quantum states required to carry out a computation are very sensitive to hardware imperfections and above all to decoherence caused by interaction with the environment. The fragility of a quantum computer is tied to its function: it acts as a sophisticated nonlinear interferometer whose coherent interference pattern is essential for quantum parallelism. Ensuring that this fragility does not destroy the ability to extract the desired interference pattern requires techniques for correcting errors.

<a id="pdf-bbdd8e5c3949-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
A parallel is drawn with classical computers of the 1940s, whose reliability doubts disappeared after the discovery of powerful error-correction techniques. Doubts about large-scale quantum computing are partially based on the belief that an error-correction step requires exact knowledge of the computer's state, which would destroy quantum mechanical properties. However, Shor showed that in a restricted error model it is possible to restore a state using only partial knowledge of the state, and many codes correcting specific interactions have since been discovered. These ideas opened the path to a general theory of quantum error correction: the subject of this paper.

<a id="pdf-bbdd8e5c3949-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.93 -->
Organization: Sec. II gives an intuitive approach to quantum error correction with simple examples. Sec. III formalizes these concepts, introducing the notions of fidelity and error of a code; instead of explicit encoding and decoding operators, recovery superoperators are introduced, and quantum error-correcting codes permitting complete restoration of the encoded state are characterized by necessary and sufficient conditions for recovering the state of a system after evolution through a superoperator. The conditions depend only on the subspace of the code, and several equivalent characterizations are given.

<a id="pdf-bbdd8e5c3949-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.94 -->
Four further characterizations are given: one based on the existence of a left inverse of the interaction superoperator, one using the explicit representation of the coding space as a tensor product of the code with a quantum error syndrome, one exploiting the effect of the operators on a completely entangled state, and one using an information-theoretic identity. Sec. IV discusses methods for implementing the recovery operator in practice. Sec. V discusses independent interactions for strings of qubits — the natural generalization of classical independent errors — proves that a one-error-correcting code for one qubit cannot use a coding space of only four qubits, generalizes this to a theorem about correcting $e$ errors, characterizes $e$-error-correcting codes, and addresses fidelity of codes with imperfect recovery operators, showing the fidelity of recovery of an entangled state can be bounded below in terms of the pure-state fidelity. Sec. VI concludes.

<a id="pdf-bbdd8e5c3949-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.94 -->
## II. An intuitive approach

Coherent quantum states are used in quantum communication and computation; both involve manipulation of states by unitary operations with information extracted by measurement. Loss of coherence occurs while executing operations or preserving states in memory, reducing the probability of a correct answer. For larger distances and long calculations errors are inevitable, and a scheme for returning the state to the desired one is needed. The focus here is preserving a coherent state subject to unwanted interactions in a quantum memory or channel.

<a id="pdf-bbdd8e5c3949-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.94 -->
In classical systems corrupted information can be restored by redundancy (copying), but the no-cloning theorem prevents duplication of quantum information. It is nevertheless possible to correct a state against certain known errors by spreading the information over many qubits through an encoding. The simplest nontrivial case encodes a single qubit $|\Psi\rangle = \alpha|0\rangle + \beta|1\rangle$ into a higher-dimensional Hilbert space using ancilla qubits initially in $|0\rangle$:

$$(\alpha|0\rangle + \beta|1\rangle)\,|000\cdots\rangle \;\to\; \alpha|0_L\rangle + \beta|1_L\rangle. \tag{1}$$

This defines the code; $|0_L\rangle$ and $|1_L\rangle$ are the logical zero and one. Any error should map the encoded state into one of a family of two-dimensional subspaces preserving the relative coherence of the quantum information. A measurement projects the state into one of these subspaces, and the original state is recovered by a unitary transformation depending on which subspace was observed. Sec. IV establishes that for every error-correcting code, the original state can be recovered by a measurement followed by a unitary operation determined by the outcome.

<a id="pdf-bbdd8e5c3949-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
Errors arise from interaction with an environment. If the initial state is $\Psi_i$, the computer is left in the reduced density matrix $\rho_f = \$(|\Psi_i\rangle)$ (Eq. 2), where $\$$ is the superoperator associated with the interaction. When the environment is not initially entangled with the system, $\rho_f$ can be written in the form

$$\rho_f = \sum_a A_a \rho_i A_a^{\dagger} \tag{3}$$

where the interaction operators $A_a$ can be determined from an orthonormal basis $|\mu_a\rangle$ of the environment, the environment's initial state $|e\rangle$, and the evolution operator $U$ of the whole system: $A_a = \langle \mu_a | U | e \rangle$ (Eq. 4).

<a id="pdf-bbdd8e5c3949-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.94 -->
The interaction operators satisfy the superoperator (trace-preservation) constraint

$$\sum_a A_a^{\dagger} A_a = I. \tag{5}$$

The $A_a$ are linear operators on the Hilbert space of the system describing the effect of the environment; any family satisfying Eq. (5) defines a superoperator. The choice of interaction operators is not unique — two sets differing only by the choice of environment basis are physically equivalent. For systems of qubits a reasonable approximation is that the interaction with the environment is independent for each qubit, so the interaction operators are tensor products of one-qubit interaction operators. If one one-qubit operator, say $A_0$, is near the identity, the number of errors of an interaction is the number of tensor factors which are not $A_0$.

<a id="pdf-bbdd8e5c3949-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.95 -->
**Necessary and sufficient conditions for recovery** of the state $|\Psi_i\rangle$ are (see Sec. III):

$$\langle 0_L | A_a^{\dagger} A_b | 1_L \rangle = 0, \tag{6}$$

$$\langle 0_L | A_a^{\dagger} A_b | 0_L \rangle = \langle 1_L | A_a^{\dagger} A_b | 1_L \rangle. \tag{7}$$

The first condition states that logical zero and one must go to orthogonal states under any error. The second implies that the lengths and inner products of the projections of the corrupted logical zero and one should be the same. A sufficient but not necessary condition is that Eq. (7) is zero when $A_a \neq A_b$, meaning each error maps the initial state to orthogonal subspaces; the more general Eq. (7) allows two different errors to map onto the same two-dimensional subspace — a possibility allowed by the superposition principle which cannot occur in classical error correction.

<a id="pdf-bbdd8e5c3949-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.93 -->
For realistic quantum computers only a subset of possible errors can be corrected. The quality of a recovered code is measured by the fidelity: the overlap between the final state $\rho_f$ and the original state $|\Psi_i\rangle$. If the combined superoperator (interaction followed by recovery) is $\mathcal{A} = \{A_0, \ldots\}$, the fidelity is

$$F(|\Psi_i\rangle, \mathcal{A}) = \langle \Psi_i | \rho_f | \Psi_i \rangle = \sum_a \langle \Psi_i | A_a | \Psi_i \rangle \langle \Psi_i | A_a^{\dagger} | \Psi_i \rangle, \tag{8}$$

the probability that the final state passes a test checking agreement with the initial state. Since the encoded state is not known in advance, the minimum (worst-case) fidelity $F_{\min} = \min_{|\Psi\rangle} \langle \Psi | \rho_f | \Psi \rangle$ (Eq. 9) is used; the best quantum code maximizes $F_{\min}$.

<a id="pdf-bbdd8e5c3949-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.92 -->
**Decoherence example.** Decoherence randomizes the phase of the initial state: for one qubit

$$|\Psi_i\rangle = \alpha|0\rangle + \beta|1\rangle \;\to\; \rho\begin{pmatrix} \alpha\alpha^* & \alpha\beta^* e^{-\gamma} \\ \alpha^*\beta e^{-\gamma} & \beta\beta^* \end{pmatrix}, \tag{10}$$

where $e^{-\gamma}$ ($\gamma \ge 0$) parametrizes the amount of decoherence, understood via the environment interaction $|e\rangle|0\rangle \to |e_0\rangle|0\rangle$, $|e\rangle|1\rangle \to |e_1\rangle|1\rangle$ with $\langle e_0|e_1\rangle = e^{-\gamma}$ (Eq. 11). Using the environment basis $|\mu_0\rangle = |e_0\rangle$ and $|\mu_1\rangle = (|e_1\rangle - e^{-\gamma}|e_0\rangle)/\sqrt{1 - e^{-2\gamma}}$ the interaction operators are

$$A_0 = \begin{pmatrix} 1 & 0 \\ 0 & e^{-\gamma} \end{pmatrix}; \quad A_1 = \begin{pmatrix} 0 & 0 \\ 0 & \sqrt{1 - e^{-2\gamma}} \end{pmatrix}. \tag{12}$$

For a single qubit corrupted by decoherence the minimum fidelity is $F = (1 + e^{-\gamma})/2 \sim 1 - \gamma/2 + \cdots$ (Eq. 13).

<a id="pdf-bbdd8e5c3949-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.92 -->
Assuming independent environments per qubit, a one-qubit code correcting this error type using three qubits (Refs. [11,12]) is understood by changing the environment basis to $|\mu_\pm\rangle \propto |e_0\rangle \pm |e_1\rangle$, giving one-qubit interaction operators

$$A_+ = a_+\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}; \quad A_- = a_-\begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \tag{14}$$

with $a_+ = \sqrt{(1+e^{-\gamma})/2}$ and $a_- = \sqrt{(1-e^{-\gamma})/2}$: the environment either leaves the system alone or flips the sign of $|1\rangle$. The encoding is

$$|0_L\rangle = (|0\rangle+|1\rangle)(|0\rangle+|1\rangle)(|0\rangle+|1\rangle), \quad |1_L\rangle = (|0\rangle-|1\rangle)(|0\rangle-|1\rangle)(|0\rangle-|1\rangle). \tag{15}$$

<a id="pdf-bbdd8e5c3949-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.93 -->
A corrupted qubit can be detected by majority rule: assuming at most one incorrect qubit, the interaction maps $|0_L\rangle$ to one of the possibilities $A_+|0_L\rangle$ or $A_-^r|0_L\rangle$ (sign flipped on qubit $r$), Eq. (16), and similarly for $|1_L\rangle$. The recovery operator is the superoperator determined by the interactions

$$R_+ = |0_L\rangle\langle 0_L| + |1_L\rangle\langle 1_L|, \quad R_-^r = (|0_L\rangle\langle 0_L| + |1_L\rangle\langle 1_L|)\,\sigma_z^r, \tag{17}$$

where $\sigma_z^r$ is the $z$ Pauli matrix on the $r$th qubit. In practice recovery is implemented by a measurement determining which error occurred (via controlled-NOT gates and measurements); the measurements collapse the system to two-dimensional subspaces, after which the initial state is recovered by an appropriate unitary. The code corrects perfectly only if at most one error occurs; for small decoherence the minimum fidelity is bounded below by

$$F = 1 - (a_-^3 + 3a_-^2 a_+) \approx 1 - \tfrac{3}{4}\gamma^2 + \cdots, \tag{18}$$

an improvement over the single-qubit evolution for small enough $\gamma$. A $2n+1$-bit generalization achieves fidelity $1 - O(\gamma^{n+1})$.

<a id="pdf-bbdd8e5c3949-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->
## III. Quantum error-correcting codes

### A. Fundamentals

**Definition (quantum code).** An $(n,k)$ quantum code is a $2^k$-dimensional subspace $\mathcal{C}$ of a $2^n$-dimensional Hilbert space $\mathcal{H}$ (the coding space). An encoding operator for $\mathcal{C}$ is a unitary operator $E$ from a $k$-dimensional Hilbert space $\mathcal{Q}$ onto $\mathcal{C}$; a decoding operator is a right inverse of an encoding operator. The encoding can be implemented as a unitary on $\mathcal{Q}^{\otimes k} \otimes \mathcal{Q}^{\otimes n-k} \otimes \mathcal{Q}^{\otimes a}$ with $a$ ancillary qubits intended to begin and end in $|0\rangle$; the ancillas can serve as scratch-pad memory during the measurement process needed to recover $\mathcal{C}$.

<a id="pdf-bbdd8e5c3949-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.94 -->
For discussing error-correcting properties, recovery superoperators replace explicit encoding/decoding operators. A recovery (super)operator $\mathcal{R}$ is a superoperator on the coding space used to restore a state to the code after it has been affected by an interaction with the environment. A quantum error-correcting code is a pair $(\mathcal{C}, \mathcal{R})$ of a quantum code and a recovery operator. Let $\mathcal{A}$ be a family of linear operators (interaction operators as in Eq. 3). The fidelity of the error-correcting code is determined by the fidelity of the composition $\mathcal{R}\mathcal{A}$ restricted to $\mathcal{C}$:

$$F(\mathcal{C}, \mathcal{R}\mathcal{A}) = \min_{|\Psi\rangle \in \mathcal{C}} F(|\Psi\rangle, \mathcal{R}\mathcal{A}) = \min_{|\Psi\rangle \in \mathcal{C}} \sum_{r,a} |\langle \Psi | R_r A_a | \Psi \rangle|^2.$$

For families not satisfying the superoperator constraint the error of the code is considered instead.

<a id="pdf-bbdd8e5c3949-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.93 -->
The error of the code is defined as

$$E(\mathcal{C}, \mathcal{R}\mathcal{A}) = \max_{|\Psi\rangle \in \mathcal{C}} \sum_{r,a} \left| \left( R_r A_a - \langle \Psi | R_r A_a | \Psi \rangle \right) |\Psi\rangle \right|^2.$$

Fig. 1 gives the geometric picture: fidelity is the sum of projections (for each interaction operator) along the state; the error gives the "distance" from the original state per interaction operator. For superoperators the error is $1 - F(\mathcal{C},\mathcal{R}\mathcal{A})$, the worst-case probability of not observing the desired state. The pair $(\mathcal{C},\mathcal{R})$ is an $\mathcal{A}$-correcting code if $E(\mathcal{C},\mathcal{R}\mathcal{A}) = 0$; equivalently $E(\mathcal{C},\mathcal{R}A_a) = 0$ for each $A_a$, so one can speak of $\mathcal{A}$-correcting codes even if $\mathcal{A}$ is not finite.

<a id="pdf-bbdd8e5c3949-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.94 -->
**Theorem III.1.** The operator $A_a$ is in $\mathcal{A}(\mathcal{C},\mathcal{R})$ (the family of operators corrected by $(\mathcal{C},\mathcal{R})$) iff when restricted to $\mathcal{C}$, $R_r A_a = \lambda_{ra} I$ for each $R_r \in \mathcal{R}$. The family $\mathcal{A}(\mathcal{C},\mathcal{R})$ is linearly closed and $(\mathcal{C},\mathcal{R})$ is $\mathcal{A}(\mathcal{C},\mathcal{R})$-correcting.

**Proof.** To be $A_a$-correcting requires that for $|\Psi\rangle \in \mathcal{C}$, $|(R_r A_a - \langle\Psi|R_r A_a|\Psi\rangle)|\Psi\rangle| = 0$, i.e. $R_r A_a |\Psi\rangle = \lambda_{ra}(|\Psi\rangle)|\Psi\rangle$. By linearity of $R_r A_a$, $\lambda_{ra}(|\Psi\rangle)$ cannot depend on $|\Psi\rangle$. The rest is immediate. QED.

<a id="pdf-bbdd8e5c3949-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->
### B. Characterizations of $\mathcal{A}$-correcting codes

The characterizations below allow defining $\mathcal{A}$-correcting codes without reference to the recovery operator. Let $|i_L\rangle$ denote elements of an orthonormal basis of the code $\mathcal{C}$.

**Theorem III.2.** The code $\mathcal{C}$ can be extended to an $\mathcal{A}$-correcting code iff for all basis elements $|i_L\rangle$, $|j_L\rangle$ ($i \neq j$) and operators $A_a, A_b$ in $\mathcal{A}$:

$$\langle i_L | A_a^{\dagger} A_b | i_L \rangle = \langle j_L | A_a^{\dagger} A_b | j_L \rangle \tag{19}$$

and

$$\langle i_L | A_a^{\dagger} A_b | j_L \rangle = 0. \tag{20}$$

These conditions are more general than those given in [23], which are sufficient but not necessary. Being independent of a recovery operator, an $\mathcal{A}$-correcting code can be defined as one satisfying Eqs. (19) and (20) for any one (and therefore every) basis of the code.

<a id="pdf-bbdd8e5c3949-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.93 -->
**Proof (Theorem III.2, forward direction).** Assume $(\mathcal{C},\mathcal{R})$ is $\mathcal{A}$-correcting. Compute $\langle i_L|A_a^{\dagger}A_b|j_L\rangle$ explicitly by inserting $\sum_r R_r^{\dagger} R_r$:

$$\langle i_L|A_a^{\dagger}A_b|j_L\rangle = \sum_r \langle i_L|A_a^{\dagger}R_r^{\dagger} R_r A_b|j_L\rangle = \sum_r \langle i_L|\bar{\lambda}_{ar}\lambda_{br}|j_L\rangle = \alpha_{ab}\,\delta_{ij},$$

using the superoperator properties of $\mathcal{R}$ and Theorem III.1. The forward direction follows by inspection.

<a id="pdf-bbdd8e5c3949-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.93 -->
**Proof (Theorem III.2, reverse direction — construction of a recovery operator).** Suppose Eqs. (19) and (20) hold. Call $\mathcal{V}^i$ the subspace spanned by $A_a|i_L\rangle$ (for all $a$). By Eq. (20) the $\mathcal{V}^i$ are orthogonal subspaces. Let $|v_r^i\rangle$ be an orthonormal basis for $\mathcal{V}^i$; the $|v_r^i\rangle$ are mutually orthogonal, so there exist unitary $V_r$ which return $|v_r^i\rangle$ to the corresponding $|i_L\rangle$: $V_r|v_r^i\rangle = |i_L\rangle$ (Eq. 21). The recovery operator is given by the interaction operators

$$\mathcal{R} = \{\mathcal{O}, R_1, \ldots, R_r, \ldots\}, \tag{22}$$

where $\mathcal{O}$ is the projection onto the orthogonal complement of $\oplus_i \mathcal{V}^i$ (the part of the Hilbert space not reached by acting on the code with the $A_a$), and

$$R_r = V_r \sum_i |v_r^i\rangle\langle v_r^i|. \tag{23}$$

<a id="pdf-bbdd8e5c3949-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.93 -->
That $\mathcal{R}$ is a superoperator follows because it is a sum of orthogonal projections followed by unitary operators where the projections span the Hilbert space. To show $\mathcal{R}$ recovers the state, unitary operators $U_i$ are chosen with $U_i|v_r^0\rangle = |v_r^i\rangle$ and $U_i A_a |0_L\rangle = A_a |i_L\rangle$ — existence follows from Eq. (19), by which the inner-product relationships between the $A_a|0_L\rangle$ and the $A_a|i_L\rangle$ are identical. Writing $A_a|\Psi\rangle$ for $\Psi \in \mathcal{C}$ in the basis expansion (Eqs. 24–25) shows $R_r A_a$ is a multiple of the identity on $\mathcal{C}$; since $\mathcal{O}$ is null on all $A_a|j_L\rangle$, $\mathcal{R}$ is a recovery operator for $\mathcal{A}$. QED.

An interesting observation about Eq. (19): it does not require zero scalar products between logical states under two different interactions, merely equal ones. For two-dimensional codes, parts of the subspaces spanned by $A_a|0_L\rangle$ and $A_a|1_L\rangle$ may overlap: identifying each $A_a$ with a distinct error, more than one error can be corrected per two-dimensional subspace — a novel feature of quantum error-correcting codes with no classical counterpart.

<a id="pdf-bbdd8e5c3949-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.92 -->
**Example of nontrivial overlap.** Consider the code $\{|0_L\rangle = |00\rangle, |1_L\rangle = |11\rangle\}$ subject to interaction operators $A_0, A_1, A_2$ (Eqs. 26–27) built from a parameter $0 < q < 1$: $A_0 = \mathrm{diag}(\sqrt{1-2q}, 1, 1, \sqrt{1-2q})$ and $A_1, A_2$ mapping the logical states as $|0_L\rangle \to \sqrt{q/2}(|00\rangle \pm |10\rangle)$, $|1_L\rangle \to \sqrt{q/2}(|01\rangle \pm |11\rangle)$. These operators form a superoperator and are linearly independent, yet one of the three image states is linearly dependent on the other two in each case; only two recovery operators are needed to retrieve the initial state:

$$R_0 = |00\rangle\langle 00| + |11\rangle\langle 11|; \quad R_1 = |00\rangle\langle 10| + |11\rangle\langle 01|. \tag{28}$$

<a id="pdf-bbdd8e5c3949-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.94 -->
**Theorem III.3.** Let $\mathcal{A}$ be a superoperator. $\mathcal{C}$ is an $\mathcal{A}$-correcting code iff the restriction of $\mathcal{A}$ to $\mathcal{C}$ has a left superoperator inverse.

**Proof.** By Theorem III.1, $\mathcal{C}$ is $\mathcal{A}$-correcting iff there exists a superoperator $\mathcal{R}$ such that on $\mathcal{C}$, $R_r A_a = \lambda_{ra} I$ for all $r, a$. This means $\mathcal{R}\mathcal{A}$ is a superoperator equivalent to the identity (by a change of basis on the environment). QED.

**Theorem III.4.** $\mathcal{B}$ has error 0 on $\mathcal{C}$ if and only if $I \otimes \mathcal{B}\,\Sigma_i |i_L\rangle|i_L\rangle = \lambda\,\Sigma_i |i_L\rangle|i_L\rangle$ — checking that an operator has zero error for all pure states is equivalent to checking only one state which is completely entangled with a copy of the system. The equality is interpreted in terms of state ensembles: two state ensembles are equivalent iff they induce the same density matrix.

**Proof.** Let $B_r$ be a member of $\mathcal{B}$; then $I \otimes B_r$ is a member of $I \otimes \mathcal{B}$. If $\mathcal{B}$ has error 0 on $\mathcal{C}$, then $I \otimes B_r \Sigma_i |i_L\rangle|i_L\rangle = \Sigma_i |i_L\rangle B_r |i_L\rangle = \Sigma_i |i_L\rangle \lambda_r |i_L\rangle = \lambda_r \Sigma_i |i_L\rangle|i_L\rangle$.

<a id="pdf-bbdd8e5c3949-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.93 -->
Conversely, if the identity in the theorem holds, then for each $r$, $I \otimes B_r \Sigma_i |i_L\rangle|i_L\rangle = \lambda_r \Sigma_i |i_L\rangle|i_L\rangle$; applying $I \otimes B_r$ to each summand and using independence of the $|i_L\rangle|i_L\rangle$ gives $B_r|i_L\rangle = \lambda_r|i_L\rangle$. The result follows. QED.

<a id="pdf-bbdd8e5c3949-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.94 -->
**Theorem III.5 (error-syndrome representation).** $\mathcal{C}$ is an $\mathcal{A}$-correcting code if and only if there is an isomorphism $\sigma : \mathcal{H} \to \mathcal{C}\otimes\mathcal{E} \oplus \mathcal{D}$ such that for all $A_a \in \mathcal{A}$ and $|\Psi\rangle \in \mathcal{C}$, $A_a|\Psi\rangle = \sigma(|\Psi\rangle \otimes |\mathcal{E}(a)\rangle)$ for some vector $|\mathcal{E}(a)\rangle$ depending on $A_a$ alone.

The idea is that under each interaction operator the effect of the environment is clearly separated from the state to be preserved: $\mathcal{E}$ takes up all the information from the environment, the final state in $\mathcal{E}$ encodes the environment's effect on the code (the error syndrome), and $\mathcal{D}$ is the summand of $\mathcal{H}$ normally never reached by $\mathcal{A}$ (usable for error detection). A perfect quantum code is one for which $\mathcal{D}$ is empty and the $|\mathcal{E}(a)\rangle$ span $\mathcal{E}$.

**Proof.** For an $\mathcal{A}$-correcting code, use the notation from the proof of Theorem III.2: let $\mathcal{D}$ be the orthogonal complement of the subspace spanned by the $|v_r^i\rangle$, let $\mathcal{E}$ be the Hilbert space spanned by $\{|v_r^0\rangle\}_r$, and establish the isomorphism by $\sigma(|i_L\rangle|v_r^0\rangle) = |v_r^i\rangle$ with $\sigma$ the identity on $\mathcal{D}$. Writing $A_a|0_L\rangle = \Sigma_r \beta^0_{ra}|v_r^0\rangle$ and applying the properties from Theorem III.2's proof gives $A_a|\Psi\rangle = \sigma(|\Psi\rangle \otimes \Sigma_r \beta^0_{ra}|v_r^0\rangle)$, so $|\mathcal{E}(a)\rangle = \Sigma_r \beta^0_{ra}|v_r^0\rangle$ proves the "only if" part. For the other direction, a recovery operator restoring the code after action of $\mathcal{A}$ is constructed from the projections onto $\sigma(\mathcal{C}\otimes|v_r^0\rangle)$ followed by unitary operators mapping $\sigma(|i_L\rangle\otimes|v_r^0\rangle)$ to $|i_L\rangle$; the conditions on the $A_a$ imply $R_r A_a$ is a scalar multiple of the identity. QED.

<a id="pdf-bbdd8e5c3949-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.93 -->
**Theorem III.6 (information-theoretic characterization, Nielsen–Schumacher).** Let $|e\rangle = (1/\sqrt{k})\Sigma_i |i_L\rangle|i_L\rangle$ be the perfectly entangled state of the code, and define the density matrices $\bar{\rho} = \frac{1}{k}\sum_{ai} A_a|i_L\rangle\langle i_L|A_a^{\dagger}$ and $\rho = \sum_a I\otimes A_a |e\rangle\langle e| A_a^{\dagger} \otimes I$ (Eq. 29). Let $S(\sigma)$ denote the entropy of a density matrix. Then $\mathcal{C}$ is an $\mathcal{A}$-correcting code if and only if $S(\bar{\rho}) - S(\rho) = \log_2 k$. The quantity $S(\bar{\rho}) - S(\rho)$ is a natural notion of mutual information; the proof is found in [25].

<a id="pdf-bbdd8e5c3949-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.93 -->
## IV. Implementing recovery operators

The recovery operator constructed in Theorem III.2 consists only of projections followed by unitary operators conditional on the result of the projections: first perform a measurement corresponding to the set of projections, then perform an appropriate unitary depending on the outcome. In quantum computation direct measurements are customarily performed in a standard basis, so suitable unitary transformations must be applied first to rotate the measurement subspaces. Using unitary extensions ($W'$ agreeing with $W = \Sigma_i V_i P_i$ on the range of the orthogonal projections $P_i$), the recovery operator described by interaction operators $(U_0 P_0, \ldots, U_{r_m} P_{r_m})$ can be performed with a separate ancillary system $\mathcal{M}$ with standard basis $|r_M\rangle$: apply the unitary $V = \Sigma_r P_r \otimes V_r$ (a generalization of controlled-NOT), measure $\mathcal{M}$ in the standard basis, and apply $U_r$ to the coding space if the outcome is $|r_M\rangle$ — the implementation suggested in [11,12]. Alternatively the measurement can be replaced by application of a unitary operator $\Sigma_r U_r \otimes |r_M\rangle\langle r_M|$, transferring the information about the environment's interaction entirely to $\mathcal{M}$.

<a id="pdf-bbdd8e5c3949-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.92 -->
Decoding into a separate system $\mathcal{C}'$ of the same dimension as $\mathcal{C}$ can be performed by following the recovery operator with a unitary extension of $\Sigma_i |0_L\rangle\langle i_L| \otimes |i\rangle\langle 0|$, swapping the state from $\mathcal{C}$ to $\mathcal{C}'$ after recovery. A method for decoding without ancillas uses projections $Q_i$ onto $\mathcal{V}^i$ and unitary extensions, optionally followed by a measurement of $\mathcal{H}$ in a special basis $|e_{ir}\rangle = \Sigma_j \omega^{ij}|v_r^j\rangle$ with $\omega$ a $k$th root of unity, after which a unitary correction $\Sigma_j \omega^{-ij}|j\rangle\langle j|$ completes the decoding. When $\mathcal{H} = \mathcal{C}'\otimes\mathcal{E}'$, a state can be decoded using the isomorphism of Theorem III.5, and the same circuit can be used for both encoding and decoding. Codes such as those of Steane and Calderbank–Shor have the property that $\mathcal{H}$ can be represented as in Theorem III.5 with the additional property that $A_a\sigma(|\psi\rangle|e_i\rangle) = \sigma(\Sigma_j U_{ij}|\psi\rangle\,\alpha_{aj}|e_j\rangle)$ independent of $\psi$: each subspace $\sigma(\mathcal{C}\otimes|e_i\rangle)$ is an $\mathcal{A}$-correcting code, useful in iterated applications where recovery operators and interactions alternate.

<a id="pdf-bbdd8e5c3949-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.94 -->
## V. Properties of codes correcting independent interactions

### A. Independent interactions

In the classical theory of error correction errors are often assumed independent per symbol. For the quantum theory the set of symbols is replaced by a fixed system such as the qubit, and the coding space is a tensor product of independent systems. The interaction operator acting independently on each component means it is a tensor product of single-system interactions. For $\mathcal{H} = \mathcal{Q}^{\otimes r} = \mathcal{Q}_1 \otimes \cdots \otimes \mathcal{Q}_r$ and a one-qubit superoperator $\mathcal{A}$, the independent action is $\mathcal{A}^{\otimes r} = \{A_{i_1} \otimes A_{i_2} \otimes \cdots\}_{i_1, i_2, \ldots}$. The assumption is reasonable e.g. for spontaneous emission with $S_0 = \begin{pmatrix} 1 & 0 \\ 0 & \sqrt{1-p^2}\end{pmatrix}$, $S_1 = \begin{pmatrix} 0 & p \\ 0 & 0 \end{pmatrix}$, and for phase randomization when the environment's effective wavelength is smaller than the qubit spacing.

<a id="pdf-bbdd8e5c3949-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->
**Definition ($e$-error-correcting code).** As in classical error correction with fixed error rates, it is generally impossible to correct $\mathcal{A}^{\otimes r}$ with error 0; instead one corrects the "important" members — those which strongly affect only a few of the qubits. An operator $A$ acting on $\mathcal{H}$ is said to induce (at most) $e$ errors if it is an $r$-fold tensor product of one-qubit operators where all but $e$ of them are the identity. An $e$-error-correcting code is one which can recover from all interaction operators inducing at most $e$ errors.

<a id="pdf-bbdd8e5c3949-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.94 -->
A linear basis for the one-qubit interactions with each operator unitary is given by

$$A_0 = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix};\; A_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix};\; A_2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix};\; A_3 = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}. \tag{30}$$

These correspond to: (0) leaving the system unchanged, (1) changing the sign if in $|1\rangle$, (2) flipping the bit, (3) flipping the bit and changing sign if it was $|1\rangle$. Another useful basis is $\widetilde{A}_0 = \mathrm{diag}(1,0)$, $\widetilde{A}_1 = \mathrm{diag}(0,1)$, $\widetilde{A}_2 = |0\rangle\langle 1|$, $\widetilde{A}_3 = |1\rangle\langle 0|$ (Eq. 31): $\widetilde{A}_0, \widetilde{A}_1$ implement an ideal measurement on the qubit; $\widetilde{A}_2, \widetilde{A}_3$ an ideal measurement followed by a bit flip. The basis in Eq. (30) is the one used in [15] to find the one-error-correcting five-qubit code.

<a id="pdf-bbdd8e5c3949-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.94 -->
### B. Simple lower bound

One of the simplest lower bounds on the number of classical code words given that $e$ errors are to be corrected is the Hamming bound, obtained by counting the number $b_e$ of words within $e$ errors of each code word: the product of $b_e$ and the number of code words cannot exceed the size of the coding space. For quantum codes one can attempt a similar argument. Writing the superoperator $\mathcal{A}$ in minimal form so each $A_a$ is independent: in the special case where Eq. (19) is solved by setting both sides to 0, all states of the form $A_a|i_L\rangle$ are independent, implying the total dimension of the space is at least $2^k|\mathcal{A}|$. This argument fails in general because no such independence is implied by Eqs. (19) and (20). One can, however, use Theorem III.5 to see that the total dimension has to exceed $2^k e$, where $e$ is the dimension of $\mathcal{E}$; a lower bound on $\dim(A_0|\Psi\rangle, \ldots, A_{a_m}|\Psi\rangle)$ is a lower bound on $e$.

<a id="pdf-bbdd8e5c3949-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.94 -->
As an example, consider whether there are $(2^r, 2)$ codes with $r \le 4$ qubits such that any operator inducing at most one error can be corrected. A natural basis for this family of operators derived from Eq. (30) consists of $1 + 3r$ operators. Solving $2(1+3r) \le 2^r$ suggests $r$ must be at least 5 (see [15] for a code with $r = 5$). As pointed out, this argument is incomplete.

**A complete argument that $r = 5$ is minimal for one-error-correcting codes.** Assume a code with $r = 4$ exists. Use the necessary and sufficient conditions Eqs. (19), (20) and expand the logical zero and one as $|0_L\rangle = \sum_{ijkl}\alpha_{ijkl}|ijkl\rangle$, $|1_L\rangle = \sum_{ijkl}\beta_{ijkl}|ijkl\rangle$ (Eq. 32), using the interaction operators of Eq. (31). Define the reduced density matrices $\rho^0_{i'j'\,ij} = \sum_{kl}\alpha^*_{i'j'kl}\alpha_{ijkl}$ and $\rho^1_{i'j'\,ij} = \sum_{kl}\beta^*_{i'j'kl}\beta_{ijkl}$ (Eq. 33).

<a id="pdf-bbdd8e5c3949-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.93 -->
Using those operators which induce an error on the last two qubits in Eq. (20), one obtains the orthogonality relations $\sum_{ij}\alpha^*_{ij00}\beta_{ij00} = 0$, $\sum_{ij}\alpha^*_{ij10}\beta_{ij00} = 0$, …, $\sum_{ij}\alpha^*_{ij11}\beta_{ij11} = 0$ (Eq. 34), from which the density matrices are orthogonal: $(\rho^0\rho^1)_{ij\,i'j'} = 0$ (Eq. 35). On the other hand, Eq. (19) implies these two density matrices are equal: using those operators which induce an error in the first two qubits gives $\sum_{ij}\alpha^*_{00ij}\alpha_{00ij} = \sum_{ij}\beta^*_{00ij}\beta_{00ij}$ through $\sum_{ij}\alpha^*_{11ij}\alpha_{11ij} = \sum_{ij}\beta^*_{11ij}\beta_{11ij}$ (Eq. 36).

<a id="pdf-bbdd8e5c3949-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.94 -->
From Eq. (36) one deduces $\rho^0_{iji'j'} = \sum_{kl}\alpha^*_{ijkl}\alpha_{i'j'kl} = \sum_{kl}\beta^*_{ijkl}\beta_{i'j'kl} = \rho^1_{iji'j'}$ (Eq. 37). Equation (35) and Eq. (37) are inconsistent (equal density matrices cannot be mutually orthogonal and nonzero), implying no such code exists.

**Theorem V.1.** A $(n,k)$ $e$-error-correcting quantum code must satisfy $n \ge 4e + k$.

**Theorem V.2.** $\mathcal{C}$ is an $e$-error-correcting code if and only if for all $U \subseteq \{1,\ldots,r\}$ with $|U| = 2e$: (i) for all $i, j$, $\rho(|i_L\rangle, U) = \rho(|j_L\rangle, U)$ and (ii) for $i \neq j$, $\rho(|i_L\rangle, \bar{U})\rho(|j_L\rangle, \bar{U}) = 0$. Here the qubits of the coding space are labeled $1, \ldots, r$; for $U \subseteq \{1,\ldots,r\}$, $\rho(|x\rangle, U)$ is the reduced density matrix of $|x\rangle$ on the qubits labeled by elements of $U$, and $\bar{U}$ is the complement of $U$.

The proofs of Theorems V.1 and V.2 are given elsewhere using a straightforward generalization of the techniques in the earlier proof of the bound on one-error correction. The proof of Theorem V.1 is much simplified by characterizing $e$-error correction in terms of the reduced density matrices of the code words.

<a id="pdf-bbdd8e5c3949-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.93 -->
### C. Relationship between the pure state and entangled state fidelity

The states to be protected may involve only a subset of the entangled qubits of the computer or communication channel, so the whole state — not just the component being protected — must be considered. The worst-case fidelity for such states is the entangled state fidelity, distinguished from the pure state fidelity introduced earlier.

**Theorem V.3.** If the pure state fidelity is $F_p = 1 - \epsilon$, then the entangled state fidelity is $F_e \ge 1 - 3\epsilon/2$. There are examples where this bound is achieved.

**Proof.** For a two-dimensional system: $F_p = \min_{|\psi\rangle \in \mathcal{C}} \langle\Psi|\rho|\Psi\rangle = 1 - \epsilon$ (Eq. 38) and the entangled state fidelity is $F_e = \min_{|\Psi_e\rangle \in \mathcal{H}\otimes\mathcal{C}} \langle\Psi_e|\rho_e|\Psi_e\rangle$ (Eq. 39). Writing the entangled state in the Schmidt basis $|\Psi_e\rangle = \Sigma_i \sqrt{p_i}|\psi_i^{\mathcal{C}}\rangle|\psi_i^{\mathcal{H}}\rangle$ and assuming only $\mathcal{C}$ is affected by the interaction and recovery, Eq. (39) becomes $F_e = \sum_{i,j,a} p_i p_j \langle\psi_i^{\mathcal{C}}|A_a|\psi_i^{\mathcal{C}}\rangle\langle\psi_j^{\mathcal{C}}|A_a^{\dagger}|\psi_j^{\mathcal{C}}\rangle$ (Eq. 40). Calculating the pure-state fidelity for superpositions $\sqrt{p_1}\psi_1^{\mathcal{C}} + e^{i\theta}\sqrt{p_2}\psi_2^{\mathcal{C}}$ (Eq. 41) and averaging uniformly over $\theta$ gives $F_p \le F_e + p_1 p_2 (\langle\psi_1^{\mathcal{C}}|A_a|\psi_2^{\mathcal{C}}\rangle\langle\psi_2^{\mathcal{C}}|A_a^{\dagger}|\psi_1^{\mathcal{C}}\rangle + \text{c.c.})$ (Eqs. 42–43). Eq. (5) bounds the last term via $\sum_{i,a}\langle\psi_i^{\mathcal{C}}|A_a|\psi_1^{\mathcal{C}}\rangle\langle\psi_1^{\mathcal{C}}|A_a^{\dagger}|\psi_i^{\mathcal{C}}\rangle \le 1$ (Eq. 44) — a partial trace of a density matrix. Expanding over $i$: the $i=1$ term is at least $1-\epsilon$ by definition of pure-state fidelity, and all terms are positive, so the $i \neq 1$ terms are bounded by $\epsilon$. The largest achievable value of $p_1 p_2$ is $1/4$. This gives

$$F_e \ge 1 - \frac{3\epsilon}{2}. \tag{45}$$

<a id="pdf-bbdd8e5c3949-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.93 -->
**Example showing the bound is best possible.** Consider the interaction of scalar multiples of the Pauli spin matrices $\mathcal{A} = \{\frac{1}{\sqrt{3}}\sigma_x, \frac{1}{\sqrt{3}}\sigma_y, \frac{1}{\sqrt{3}}\sigma_z\}$. For this example $F(\mathcal{A}) = 1/3$ and $F_e(\mathcal{A}) = 0$: for $|u\rangle = \alpha|0\rangle + e^{i\theta}\beta|1\rangle$ with $\alpha^2+\beta^2=1$, maximizing $\frac{1}{3}(|\langle u|\sigma_x|u\rangle|^2 + |\langle u|\sigma_y|u\rangle|^2 + |\langle u|\sigma_z|u\rangle|^2) = \frac{1}{3}[(\alpha^2+\beta^2)^2] = \frac{1}{3}$. For the entangled state $|e\rangle = \frac{1}{\sqrt{2}}(|0\rangle|0\rangle + |1\rangle|1\rangle)$, the states $I\otimes\sigma_x|e\rangle$, $I\otimes\sigma_y|e\rangle$, $I\otimes\sigma_z|e\rangle$ are all orthogonal to $|e\rangle$, whence $F_e(\mathcal{A}) = 0$. Thus the example achieves equality in Eq. (45).

<a id="pdf-bbdd8e5c3949-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.93 -->
### D. Bounds on the fidelity of error-correcting codes for independent interactions

Let $\mathcal{A} = \{A_0, A_1, \ldots\}$ be a one-qubit interaction with $A_0$ close to the identity. When $A_0 = \sqrt{1-p}\,I$, the classical bounds on the probability of error in the corrected code do apply, as discussed by Calderbank and Shor, Steane, and others. Assume $\mathcal{A} = \{\sqrt{1-p}\,I, A_1, \ldots\}$, denote $\mathcal{A}' = \{A_1,\ldots\}$, and note the strength of $\mathcal{A}'$ is $|\mathcal{A}'|^2 = \sup_{|x\rangle}\sum_{i\ge1}\langle x|A_i^{\dagger}A_i|x\rangle = p$. For an $r$-qubit $e$-error-correcting code $\mathcal{C} \subseteq \mathcal{Q}^{\otimes r}$ with recovery operator $\mathcal{R}$, write $\mathcal{A}^{\otimes r} = \{\sqrt{1-p}I, \mathcal{A}'\}^{\otimes r} = \sum_{0\le k\le r}\sum_{U, |U|=k} \sqrt{1-p}^{\,k}(\otimes_{i\notin U} I)\otimes(\otimes_{i\in U}\mathcal{A}')$, where $\mathcal{A}_U$ refers to the ensemble obtained by letting $I$ act on the qubits not in $U$ and $\mathcal{A}'$ on the qubits in $U$. By the properties of the recovery operator, for $|U| \le e$ the error due to $\mathcal{R}\mathcal{A}_U$ is 0; it suffices to bound the error of the remaining terms, assuming the contribution of each summand is bounded by the strength of $\mathcal{A}_U$ given by the maximum value of $|\mathcal{A}_U|x\rangle|^2$.

**Lemma V.4.** Let $\mathcal{B}_1$ and $\mathcal{B}_2$ be operator ensembles. Then $|\mathcal{B}_1\otimes\mathcal{B}_2|^2 = |\mathcal{B}_1|^2|\mathcal{B}_2|^2$. The lemma can be proved by diagonalizing $\mathcal{B}_1^{\dagger}\mathcal{B}_1 = \Sigma_i B_{1i}^{\dagger}B_{1i}$ and $\mathcal{B}_2^{\dagger}\mathcal{B}_2 = \Sigma_i B_{2i}^{\dagger}B_{2i}$.

<a id="pdf-bbdd8e5c3949-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.94 -->
The strength of $\mathcal{A}_U$ is $p^{|U|}$. Evaluating the sums over the $U$'s gives:

**Theorem V.5.** Let $\mathcal{R}$ be the recovery operator of an $e$-error-correcting code $\mathcal{C}$ on $n$ qubits and $\mathcal{A} = \{\sqrt{1-p}\,I, \mathcal{A}'\}$ a superoperator on one qubit. Then

$$F(\mathcal{C}, \mathcal{R}\mathcal{A}^{\otimes r}) \;\ge\; 1 - \sum_{k > e} \binom{r}{k} p^k (1-p)^{r-k}.$$

For applications involving entanglements, the bound needs modification in consideration of the relationship between pure state and entangled state fidelity.

<a id="pdf-bbdd8e5c3949-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.93 -->
## VI. Conclusion and future work

The paper lays the foundations for a theory of quantum error-correcting codes by providing a general definition of quantum codes and characterizing those which can correct known interactions with zero error. Main features: treating a code solely in terms of its subspace in a larger Hilbert space, defining decoding operations in terms of general recovery superoperators (avoiding explicit encoding/decoding when studying fidelity), and characterizations of error-correcting codes via interaction operators. The characterization in terms of how the operators map individual states (Theorem III.2) has proved useful for finding new codes and gives the quantum analog of the classical notion of distance between code words. As an example beyond perfect reconstruction, $e$-error-correcting codes on strings of qubits were defined and the effect of independent interactions considered; for interactions with an identity component the classical bound on the error applies naturally (possibly more pessimistic than necessary).

<a id="pdf-bbdd8e5c3949-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.92 -->
Closing remarks: the entangled-state fidelity is not much less than the pure-state fidelity, but the fact that it can be less is important lest one believe a fidelity of 1/3 might be adequate if not compounded by other errors. The study of imperfect-fidelity codes is far from complete — sources of introduced error and its propagation under repeated recovery require further study. The present work assumes no errors are produced during operations — reasonable if coding, recovery, and decoding are fast compared to the error rate and operation errors are small compared to the error corrected by the code. Acknowledgments and references [1]–[26] follow, including Shor (FOCS 1994), Steane (PRL 77, 793, 1996), Calderbank–Shor (PRA 54, 1098, 1996), Laflamme–Miquel–Paz–Zurek (PRL 76, 198, 1996) [15], MacWilliams–Sloane, Ekert–Macchiavello (PRL 77, 2585, 1996) [23], and Nielsen–Schumacher (PRA 54, 2629, 1996) [25].
