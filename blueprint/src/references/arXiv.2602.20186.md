<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 585ff62e23091238d778fbd3586b3e43754cd0a9aedefbe5ce123d9b0d0fb0ff -->

<a id="pdf-585ff62e2309-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.96 -->
Presents a self-contained symplectic linear-algebraic derivation of the Quantum Singleton Bound for stabiliser codes and, as the primary contribution, a complete Lean4 formalisation of it. Working in finite-dimensional symplectic vector spaces modelling Pauli operators, it combines three standard stabiliser ingredients — distance-based erasure correctability, the Bravyi–Terhal cleaning lemma, and a dimension count — into a purely algebraic proof of $k + 2(d-1) \le n$ for any $[[n,k,d]]$ stabiliser code. The argument uses neither von Neumann entropy nor no-cloning; the Mathlib-based formalisation is claimed to be the first machine-checked proof of the bound.

<a id="pdf-585ff62e2309-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
# Introduction

<a id="pdf-585ff62e2309-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.95 -->
The Quantum Singleton Bound states $k + 2(d-1) \le n$ for an $[[n,k,d]]$ stabiliser code, the quantum analogue of the classical Singleton bound $k + d - 1 \le n$; codes meeting equality are quantum MDS codes. Historically first proved by Knill–Laflamme and independently by Bennett–DiVincenzo–Smolin–Wootters via properties of quantum states/channels; the standard textbook proof uses von Neumann entropy inequalities, and Grassl–Huber–Winter gave a streamlined entropic proof extending to entanglement-assisted and catalytic codes. For stabiliser codes the structure is algebraic: the $n$-qudit Pauli group mod phases is identified with a $2n$-dimensional space over $\mathbb{F}_p$ carrying a symplectic form encoding commutation, a code being an isotropic subspace — motivating an entropy-free symplectic derivation.

<a id="pdf-585ff62e2309-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.96 -->
The proof combines three standard ingredients: (i) **distance implies erasure correctability** — distance $d$ makes any set of at most $d-1$ positions a correctable erasure, expressed as $S^\perp \cap V_E \subseteq S$; (ii) **the cleaning lemma** — for any partition into $M$ and $M^c$, the dimensions of supportable logical operators satisfy $g(M) + g(M^c) = 2k$ (dimension-counting form of Bravyi–Terhal, per Preskill's notes); (iii) **a dimension argument** — for disjoint correctable sets $A,B$ with $|A|=|B|=d-1$, the cleaning lemma forces all $2k$ independent logical operators onto the complement $C=[n]\setminus(A\cup B)$, giving $k \le |C| = n - 2(d-1)$. The resulting proof is elementary and algebraic, avoiding entropy, no-cloning, and decoupling.

<a id="pdf-585ff62e2309-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.95 -->
A secondary contribution is a full Lean4/Mathlib formalisation (~1300 lines) covering the symplectic model, stabiliser codes, the cleaning lemma, and the final bound — claimed as the first machine-checked proof of the Quantum Singleton Bound. Unlike operational verification tools (SQIR, QHLProver, CoqQ, Veri-QEC) that check circuits/procedures, this formalises a structural impossibility result on code parameters; its subspace-dimension character suits Mathlib's linear-algebra API, whereas an entropy proof would require formalising von Neumann entropy and subadditivity.

<a id="pdf-585ff62e2309-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.99 -->
# Related work

<a id="pdf-585ff62e2309-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.94 -->
Prior proofs of the bound: Knill–Laflamme (original); Rains (quantum weight enumerators, linear programming); Nielsen–Chuang (no-cloning plus entropy); Grassl–Huber–Winter (clean entropic proof, extended to EAQECCs and CQECCs, correcting a false conjectured generalisation); Klappenecker–Sarvepalli (no $\mathbb{F}_q$-linear subsystem code over a prime field beats the bound). The symplectic model of the Pauli group is due to Calderbank–Rains–Shor–Sloane and independently Gottesman: an $n$-qudit stabiliser code over $\mathbb{F}_p$ is an isotropic subspace of $\mathbb{F}_p^{2n}$, with distance and correction as subspace intersection/dimension statements; extends to qudits. The cleaning lemma originates with Bravyi–Terhal (self-correcting-memory no-go), used with entropy by Bravyi–Poulin–Terhal; a dimension-counting form appears in Preskill's notes, and Kalachev–Sadov give a lattice-theoretic linear-algebraic abstraction — the version used here follows the dimension-counting formulation in symplectic language. Formal verification of quantum computing (SQIR/Coq, quantum Hoare logic in Isabelle/HOL, CoqQ, Veri-QEC) targets programs/circuits; this work instead formalises a coding-theoretic parameter bound.

<a id="pdf-585ff62e2309-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
# Contributions

<a id="pdf-585ff62e2309-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.96 -->
(i) Primary: the first machine-checked proof of the Quantum Singleton Bound — a complete Lean4/Mathlib formalisation covering the symplectic form, stabiliser codes, erasure correctability, the cleaning dimension identity, and the main theorem. (ii) A self-contained symplectic linear-algebraic derivation of $k + 2(d-1) \le n$ from distance-based erasure correctability and the cleaning lemma via a dimension argument, using neither entropy nor no-cloning; the ingredients are standard, the contribution being a streamlined, formalisation-ready presentation rather than a new bound.

<a id="pdf-585ff62e2309-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.99 -->
# Conventions and symplectic model

<a id="pdf-585ff62e2309-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.97 -->
**Remark (Field convention).** $\mathbb{F}$ denotes a prime field $\mathbb{F}_p$. Work in the symplectic space $V := \mathbb{F}^n \times \mathbb{F}^n \cong \mathbb{F}^{2n}$, with $v = (v_X, v_Z)$. Such $v$ represents the phase-free $n$-qudit Pauli operator $X^{v_X} Z^{v_Z} = \prod_{i=1}^n X_i^{v_X(i)} Z_i^{v_Z(i)}$. Two Pauli operators commute iff the symplectic pairing of their vectors vanishes.

<a id="pdf-585ff62e2309-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.98 -->
**Definition (Standard symplectic form).** For $u=(u_X,u_Z)$, $v=(v_X,v_Z)$ in $V$, $\langle u, v \rangle := \sum_{i=1}^n \bigl( u_X(i) v_Z(i) - u_Z(i) v_X(i) \bigr) \in \mathbb{F}$. This form is bilinear and alternating (hence antisymmetric).

<a id="pdf-585ff62e2309-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.98 -->
**Lemma (Nondegeneracy).** If $u \in V$ satisfies $\langle u, v \rangle = 0$ for all $v \in V$, then $u = 0$.

<a id="pdf-585ff62e2309-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
**Proof.** For each index $i$, pairing $u$ with $(0, e_i)$ gives $u_X(i)=0$ and pairing with $(e_i, 0)$ gives $-u_Z(i)=0$; as $i$ is arbitrary, $u=0$.

<a id="pdf-585ff62e2309-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.96 -->
Nondegeneracy identifies $V$ with its dual, the basis for the dimension identities used throughout.

<a id="pdf-585ff62e2309-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.98 -->
# Support, restriction, and distance

Notation: $[n] := \{1,\dots,n\}$.

<a id="pdf-585ff62e2309-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.98 -->
**Definition (Support and weight).** For $v \in V$, $\operatorname{supp}(v) := \{ i \in [n] : (v_X(i), v_Z(i)) \neq (0,0) \}$ and $\operatorname{wt}(v) := |\operatorname{supp}(v)|$ — the qudit positions where the Pauli operator acts nontrivially, and their count.

<a id="pdf-585ff62e2309-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.98 -->
**Definition (Support subspace).** For $C \subseteq [n]$, $V_C := \{ v \in V : v_X(i) = v_Z(i) = 0 \text{ for all } i \notin C \}$ — vectors with support contained in $C$.

<a id="pdf-585ff62e2309-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=0.98 -->
**Lemma (Dimension of a support subspace).** $\dim(V_C) = 2|C|$.

<a id="pdf-585ff62e2309-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.98 -->
**Proof.** Restriction to the coordinates indexed by $C$ gives an isomorphism $V_C \cong \mathbb{F}^{|C|} \times \mathbb{F}^{|C|}$.

<a id="pdf-585ff62e2309-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.98 -->
**Definition (Restriction map).** For $E \subseteq [n]$, $r_E : V \to V_E$ zeroes all coordinates outside $E$: $(r_E(v))_X(i)=v_X(i)$, $(r_E(v))_Z(i)=v_Z(i)$ for $i\in E$, and $0$ otherwise.

<a id="pdf-585ff62e2309-p003-b010"></a>
<!-- pdf-source: page=3; block=10; confidence=0.98 -->
**Definition (Stabiliser subspace and distance).** A stabiliser code $Q$ is given by an isotropic subspace $S \subseteq V$ (i.e. $S \subseteq S^\perp$) with $\dim(S) = n - k$. The Pauli distance is $d := \min\{ \operatorname{wt}(v) : v \in S^\perp \setminus S,\; v \neq 0 \}$. Elements of $S$ are stabiliser operators; elements of $S^\perp \setminus S$ are nontrivial logical operators; $S^\perp / S$ is the logical operator space.

<a id="pdf-585ff62e2309-p003-b011"></a>
<!-- pdf-source: page=3; block=11; confidence=0.98 -->
**Lemma (Logical space dimension).** If $\dim(S) = n - k$, then $\dim(S^\perp / S) = 2k$.

<a id="pdf-585ff62e2309-p003-b012"></a>
<!-- pdf-source: page=3; block=12; confidence=0.98 -->
**Proof.** Nondegeneracy gives $\dim(S) + \dim(S^\perp) = 2n$, so $\dim(S^\perp) = n + k$; hence $\dim(S^\perp / S) = (n+k) - (n-k) = 2k$.

<a id="pdf-585ff62e2309-p003-b013"></a>
<!-- pdf-source: page=3; block=13; confidence=0.99 -->
# Erasure correctability

<a id="pdf-585ff62e2309-p003-b014"></a>
<!-- pdf-source: page=3; block=14; confidence=0.97 -->
**Definition (Correctable erasure).** $E \subseteq [n]$ is correctable if $S^\perp \cap V_E \subseteq S$. This is equivalent to the Knill–Laflamme conditions for the erasure channel tracing out the qudits in $E$: $E$ is correctable iff no nontrivial logical operator is supported entirely within $E$ (every $S^\perp$ element supported on $E$ lies in $S$).

<a id="pdf-585ff62e2309-p003-b015"></a>
<!-- pdf-source: page=3; block=15; confidence=0.98 -->
**Lemma (Distance implies erasure correctability).** If $|E| \le d - 1$, then $E$ is correctable.

<a id="pdf-585ff62e2309-p003-b016"></a>
<!-- pdf-source: page=3; block=16; confidence=0.98 -->
**Proof.** If $v \in S^\perp \cap V_E$ with $v \notin S$, then $v \in S^\perp \setminus S$ and $\operatorname{wt}(v) \le |E| \le d-1$, contradicting the definition of $d$.

<a id="pdf-585ff62e2309-p003-b017"></a>
<!-- pdf-source: page=3; block=17; confidence=0.97 -->
# Cleaning lemma and the dimension identity

Complementarity: logical operators supportable on $M$ and on $M^c$ together account for all $2k$ logical degrees of freedom.

<a id="pdf-585ff62e2309-p003-b018"></a>
<!-- pdf-source: page=3; block=18; confidence=0.98 -->
**Definition (Supportable logical operators).** For $M \subseteq [n]$, $g(M) := \dim\bigl( (S^\perp \cap V_M) / (S \cap V_M) \bigr)$ — the number of independent logical Pauli operators (mod stabilisers) supportable entirely on $M$.

<a id="pdf-585ff62e2309-p003-b019"></a>
<!-- pdf-source: page=3; block=19; confidence=0.98 -->
**Lemma (Cleaning dimension identity).** For any $M \subseteq [n]$, $g(M) + g(M^c) = 2k$.

<a id="pdf-585ff62e2309-p003-b020"></a>
<!-- pdf-source: page=3; block=20; confidence=0.94 -->
**Proof.** (Reformulation of Preskill's dimension count.) With $P_M := V_M$, $P_{M^c} := V_{M^c}$, set $S_M := S \cap P_M$, $S_{M^c} := S \cap P_{M^c}$, and choose $S_0$ with $S = S_M \oplus S_{M^c} \oplus S_0$. The restriction $r_M$ is injective on $S_M \oplus S_0$: a combination vanishing on $M$ is supported on $M^c$, hence in $S \cap P_{M^c} = S_{M^c}$, forcing triviality by directness; so $\dim(S_M \oplus r_M(S_0)) = \dim(S_M) + \dim(S_0)$. Since $P_M$ is symplectically orthogonal to $S_{M^c}$, commuting with all of $S$ on $P_M$ is orthogonality to $S_M \oplus r_M(S_0)$, giving $\dim(S^\perp \cap P_M) = 2|M| - \dim(S_M) - \dim(S_0)$, and similarly $\dim(S^\perp \cap P_{M^c}) = 2|M^c| - \dim(S_{M^c}) - \dim(S_0)$. Hence $g(M) = 2|M| - 2\dim(S_M) - \dim(S_0)$ and $g(M^c) = 2|M^c| - 2\dim(S_{M^c}) - \dim(S_0)$. Adding, with $|M| + |M^c| = n$ and $\dim(S) = \dim(S_M) + \dim(S_{M^c}) + \dim(S_0) = n-k$: $g(M) + g(M^c) = 2n - 2\dim(S) = 2k$.

<a id="pdf-585ff62e2309-p003-b021"></a>
<!-- pdf-source: page=3; block=21; confidence=0.97 -->
**Remark.** The identity $g(M) + g(M^c) = 2k$ is a statement about dimensions, not individual operators: it does not imply each logical Pauli operator is supportable on exactly one of $M$ or $M^c$.

<a id="pdf-585ff62e2309-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.98 -->
**Corollary (Cleaning lemma — support on the complement).** If $M$ is correctable, then every logical class $[L]\in S^\perp/S$ has a representative supported on $M^c$.

<a id="pdf-585ff62e2309-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.97 -->
**Proof.** Correctability of $M$ gives $S^\perp\cap V_M\subseteq S$, so $g(M)=0$. The dimension identity then yields $g(M^c)=2k=\dim(S^\perp/S)$.

<a id="pdf-585ff62e2309-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.96 -->
**Section — Two disjoint correctable sets.** Key step linking the cleaning lemma to the Singleton bound: two disjoint correctable sets bound the number of logical qubits by the size of the remaining positions.

<a id="pdf-585ff62e2309-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.98 -->
**Lemma (Two disjoint correctable sets bound logical dimension).** Partition the physical qudits into $A,B,C$ with $A\cap B=\varnothing$ and $C=[n]\setminus(A\cup B)$. If erasures of both $A$ and $B$ are correctable, then $k\le|C|$.

<a id="pdf-585ff62e2309-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.97 -->
**Proof.** Set $D:=A^c=B\cup C$. Since $A$ is correctable, $g(A)=0$, so by the cleaning dimension identity $g(D)=g(A^c)=2k$. By definition $g(D)=\dim\big((S^\perp\cap V_D)/(S\cap V_D)\big)$, so $L:=(S^\perp\cap V_D)/(S\cap V_D)$ has $\dim(L)=2k$.

Let $r_C:V_D\to V_C$ be the restriction map (zeroing coordinates outside $C$) and $W:=S\cap V_D$. Then $r_C(W)\le V_C$, and $r_C$ induces $\bar r_C:L\to V_C/r_C(W)$, $[v]\mapsto r_C(v)\bmod r_C(W)$, which is well-defined since $w\in W$ shifts $r_C(v)$ by $r_C(W)$.

$\bar r_C$ is injective: if $\bar r_C([v])=0$ then $r_C(v)=r_C(w)$ for some $w\in W$, so $r_C(v-w)=0$, giving $v-w\in V_B$. Also $v-w\in S^\perp$, hence $v-w\in S^\perp\cap V_B$; correctability of $B$ gives $v-w\in S$, and with $w\in S$ this yields $v\in S$, i.e. $[v]=0$.

Therefore $2k=\dim(L)\le\dim(V_C/r_C(W))\le\dim(V_C)=2|C|$, so $k\le|C|$.

<a id="pdf-585ff62e2309-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.95 -->
**Section — The Quantum Singleton Bound.**

<a id="pdf-585ff62e2309-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.99 -->
**Theorem (Quantum Singleton Bound).** For any $[[n,k,d]]$ stabiliser code, $k+2(d-1)\le n$.

<a id="pdf-585ff62e2309-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.97 -->
**Proof.** Choose disjoint $A,B\subseteq[n]$ with $|A|=|B|=d-1$ and $C=[n]\setminus(A\cup B)$. By the distance-implies-correctable lemma, erasures of $A$ and $B$ are correctable. The two-disjoint-sets lemma gives $k\le|C|=n-2(d-1)$, equivalent to the stated bound.

<a id="pdf-585ff62e2309-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.96 -->
**Remark (Existence of disjoint correctable sets).** Disjoint $A,B$ with $|A|=|B|=d-1$ exist whenever $n\ge2(d-1)$. If $n<2(d-1)$, no such sets exist, but then $k\le n-2(d-1)$ has non-positive RHS and holds automatically since $k\ge0$; so all cases are covered.

<a id="pdf-585ff62e2309-p004-b010"></a>
<!-- pdf-source: page=4; block=10; confidence=0.90 -->
**Discussion.** The Quantum Singleton Bound is derived from three ingredients: (i) the symplectic vector-space model of stabiliser codes, (ii) distance-based erasure correctability, and (iii) a dimension-counting proof of the cleaning lemma (following Preskill), with the final inequality a purely symplectic dimension argument from correctability of two disjoint erasures.

*Comparison with entropic proofs:* the entropy-based proof uses that correcting erasure of $E$ makes encoded information determined by the complement, giving $S(A)\ge S(AB)$ ($S=$ von Neumann entropy); it is more general (arbitrary codes, approximate/noisy correction), but the symplectic proof makes the stabiliser-case algebra transparent.

*Scope and limitations:* the proof applies to stabiliser codes over prime fields $\mathbb{F}_p$; extension to $\mathbb{F}_q=\mathbb{F}_{p^m}$ (Hermitian/trace-symplectic forms) follows the same outline. For general non-additive codes the entropic argument is more natural.

*The formalisation:* the Lean4 development added auxiliary material absent from Mathlib (symplectic bilinear form, support subspaces and restriction maps, interaction of symplectic complements with intersections); the hardest part was the cleaning dimension identity, needing the direct-sum decomposition $S=S_M\oplus S_{M^c}\oplus S_0$. The final theorem was a short consequence once the lemmas were established.

<a id="pdf-585ff62e2309-p004-b011"></a>
<!-- pdf-source: page=4; block=11; confidence=0.92 -->
**Appendix — Lean4 formalisation and code index.** Formalisation is in the `tcslib` repository, file `TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean`, pinned to commit `9c7f65d`, compiling against Mathlib revision `cd0d357` on toolchain `leanprover/lean4:v4.25.0-rc2`. The main file contains no `sorry`, `admit`, or introduced `axiom`s.

<a id="pdf-585ff62e2309-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->
**Index — core definitions (paper object → Lean declaration).** Prime field $\mathbb{F}=\mathbb{F}_p$ → `abbrev F`; ambient space $V\cong\mathbb{F}^{2n}$ → `abbrev V`; standard symplectic form $\langle\cdot,\cdot\rangle$ → `def sym_form`; bilinear-form packaging → `noncomputable def symB`; support/weight $\mathrm{supp}(\cdot),\mathrm{wt}(\cdot)$ → `def supp`, `def wt`; support subspace $V_C$ → `def V_sub`; $\dim(V_C)=2|C|$ → `lemma dim_V_sub`; restriction map $r_E$ → `def r_E`; symplectic orthogonal complement $S^\perp$ → `abbrev sym_orth`; isotropic subspace predicate → `def IsIsotropic`; code distance (infimum over weights) → `noncomputable def code_dist`; correctable erasure (commutant form) → `def correctable`; supportable logical operator count $g(M)$ → `noncomputable def g`; logical dimension $k=n-\dim(S)$ → `def code_k`.

<a id="pdf-585ff62e2309-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.90 -->
**Index — key lemmas and main theorem (paper result → Lean lemma/theorem).** Nondegeneracy of the symplectic form → `lemma sym_form_nondegenerate`; distance implies erasure correctability → `lemma dist_implies_correctable`; cleaning dimension identity ($g(M)+g(M^c)=2k$) → `lemma cleaning_dimension_identity`; two disjoint correctable sets bound logical dimension ($k\le|C|$) → `lemma two_disjoint_correctable_sets_bound_logical_dimension`; existence of disjoint sets of prescribed size → `lemma exists_disjoint_finsets_card`; Quantum Singleton bound → `theorem quantum_singleton_bound`.
