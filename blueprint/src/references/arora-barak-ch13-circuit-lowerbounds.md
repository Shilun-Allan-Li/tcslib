<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 52929dbaa9629cc3e229c78a6cb4860da8d2223064e05f7972c7f03993772747 -->

<a id="pdf-52929dbaa962-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->
# Chapter 13: Circuit lowerbounds

_Subtitle: "Complexity theory's Waterloo."_

<a id="pdf-52929dbaa962-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->
Conjecture: NP has no polynomial-size circuits (would imply NP ≠ P). Motivation from the 1970s–80s: attack P vs NP via circuit lowerbounds. Progress on general circuits is essentially nil — a lowerbound of n is trivial for any function depending on all inputs, and no superlinear lowerbound is known for any NP problem; best known is 4.5n − o(n). Restricted circuit classes admit better results.

<a id="pdf-52929dbaa962-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.92 -->
## 13.1 AC0 and Håstad's Switching Lemma

AC0 = languages computable by circuit families of constant depth, polynomial size, unbounded fanin gates. (Constant-depth fanin-2 circuits compute only functions depending on constantly many inputs.)

<a id="pdf-52929dbaa962-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.90 -->
**Theorem 13.1 ([?, ?]).** Let ⊕ be the parity function. That is, for every x ∈ {0,1}^n, ⊕(x_1,…,x_n) = Σ_{i=1}^n x_i (mod 2). Then ⊕ ∉ AC0.

<a id="pdf-52929dbaa962-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.88 -->
Standard logic-design methods (e.g. Karnaugh maps) apply to depth-2 circuits (CNF/DNF) and show parity needs exponentially many gates at depth 2, but do not generalize to depth 3.

<a id="pdf-52929dbaa962-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->
Main tool for Theorem 13.1: random restrictions. For f computed by a depth-d circuit, randomly fix a large majority (all but ≈ n^ε input variables, ε>0 depending on d) to random 0/1 values; with positive probability the restricted f becomes constant. Since parity cannot be made constant by fixing a proper subset of variables, it is not computable by a constant-depth circuit.

<a id="pdf-52929dbaa962-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.90 -->
### 13.1.1 The switching lemma

**Definition.** A k-DNF (resp. k-CNF) is an OR of ANDs (resp. AND of ORs) in which each AND (resp. OR) involves at most k variables.

<a id="pdf-52929dbaa962-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.97 -->
**Lemma 13.2 (Håstad's switching lemma [Has86]).** Suppose f is expressible as a k-DNF, and let ρ be a random restriction assigning random values to t randomly selected input bits. Then for every s ≥ 2,

(1)  Pr_ρ[ f|ρ is not expressible as an s-CNF ] ≤ ( (n−t)·k^{10} / n )^{s/2},

where f|ρ denotes f restricted by the partial assignment ρ. Typical use: k, s constant and t ≈ n − √n, giving a probability bound n^{−c} for a constant c. Applying the lemma to ¬f gives the same result with DNF and CNF interchanged.

<a id="pdf-52929dbaa962-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
**Proof (Theorem 13.1 from Lemma 13.2).** Simplify a given AC0 circuit (Exercises 1–2): (a) all fanouts 1, so the circuit is a tree; (b) all NOT gates pushed to the input level (2n input wires, last n being negations of first n); (c) ∧ and ∨ levels alternate (at worst doubles depth); (d) bottom level has fanin-1 gates. Iteratively restrict variables so each step whp reduces depth by 1 while keeping bottom-level fanin constant. Let n_i = number of unrestricted variables after step i; at step i+1 restrict n_i − √n_i variables, so with n_0 = n, n_i = n^{1/2^i}. Let n^b bound the number of gates and set k_i = 10·b·2^i. Claim: whp after the i-th restriction we have a depth-(d−i) circuit with bottom-level fanin ≤ k_i. Each bottom ∨ gate computes a k_i-DNF, so by Lemma 13.2, with probability 1 − (k_i^{10} / n^{1/2^{i+1}})^{k_{i+1}/2} it becomes a k_{i+1}-CNF.

<a id="pdf-52929dbaa962-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.72 -->
**Proof (continued).** The per-gate failure probability is at most 1/(10 n^b) for large n, so the ∨ gate's function becomes a k_{i+1}-CNF, which merges with the ∧ gate above it, reducing depth by one (Figures 13.1, 13.2). Symmetrically, if the bottom level is ∧ gates, the lemma turns the k_i-CNF above into a k_{i+1}-DNF. The lemma is applied at most once per each of ≤ n^b gates; by the union bound, with probability ≥ 9/10, continuing for d−2 steps yields a depth-2 circuit with bottom fanin k = k_{d−2} (a k-CNF or k-DNF). Then restricting each remaining variable independently with probability 1/2 collapses this to a constant function with probability ≥ 2^{−k}. Since parity is nonconstant under any restriction fixing fewer than n variables, this contradiction proves Theorem 13.1. ∎

<a id="pdf-52929dbaa962-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->
Figures 13.1 (circuit before the Håstad switching transformation) and 13.2 (after; the new ∧ layer collapses with its single ∧ parent, cutting the number of levels by one) are unavailable in the source PDF.

<a id="pdf-52929dbaa962-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->
### 13.1.2 Proof of the switching lemma (Lemma 13.2)

Proof due to Razborov (simpler than Håstad's original).

<a id="pdf-52929dbaa962-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.88 -->
**Proof (Lemma 13.2).** Let f be a k-DNF on n variables and t as in the lemma (assume t > n/2). Let R_t be the set of restrictions of t variables, |R_t| = C(n,t)·2^t. Let K_{t,s} ⊆ R_t be the restrictions ρ with f|ρ not an s-CNF. To prove the bound it suffices to bound |K_{t,s}|/|R_t| by the RHS of (1). This is done by exhibiting a one-to-one map from K_{t,s} into Z × S, where Z = ∪_{t'≥t+s} R_{t'} is the set of restrictions of at least t+s variables and S is a set of size 3^{2ks}. Since in the relevant range t' ≫ n/2 we have C(n,t') ≈ (n/(n−t'))^{n−t'}, so Z is of size bounded by roughly n·2^s·((n−t)/n)^s·|R_t| (exact bound left as Exercise 3), the claim follows.

<a id="pdf-52929dbaa962-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.55 -->
**Proof (continued — special case).** Map K_{t,s} into Z × S. Given ρ ∈ K_{t,s} fixing t variables with f|ρ not an s-CNF, map ρ one-to-one to a restriction ρ* of at least t+s variables together with an element of a set S of size ≤ 3^{2ks}. Illustrative special case: each term (AND) of the k-DNF is either fixed to 0 by ρ or left with a single unassigned variable, whose value is denoted ?; ρ cannot fix a term to 1 since f|ρ is assumed nonconstant. Denote by x_1,…,x_s the (live variables) … [text continues beyond supplied pages].

<a id="pdf-52929dbaa962-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.78 -->
**Proof (special k-DNF case, cont.).** Take the first $s$ unassigned variables in the canonical ordering of the terms of $f|\rho$ (more than $s$ exist, else $f|\rho$ would be an $s$-CNF). For each such $x_i$ let $\mathrm{term}_i$ be the $?$-valued term containing it, and $R_i$ the operation setting $x_i$ to make $\mathrm{term}_i$ true. Map $\rho\mapsto\tau_1=R_1R_2\cdots R_s\rho$. From $\tau_1$ one recovers $\mathrm{term}_1$ as the first true term of $f|\tau_1$. Because $x_1$ may recur, supply a string $w_i\in\{0,1,?\}^s$ giving the assignment of $\mathrm{term}_1$'s $k$ variables in $\tau_2=R_2\cdots R_s\rho$; this lets one undo $R_1$ and pass from $\tau_1$ to $\tau_2$, and iterating recovers $\rho$. This yields a one-to-one map from $\rho$ to an assignment of $\ge t+s$ variables together with a sequence in $\{0,1,?\}^{ks}$. Note $f|\rho$ cannot contain an OR of $x_i$ and $\neg x_i$ (else it is the constant $1$); and if both assignments to $x_1$ give an $(s-1)$-CNF then $f|\rho$ is an $s$-CNF.

<a id="pdf-52929dbaa962-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.80 -->
**Proof (general case).** Now terms may contain several unassigned variables. Let $\mathrm{term}_1$ be the first $?$-valued term of $f|\rho$ and $x_1$ its first unassigned variable. $R_1$ assigns all $k$ variables of $\mathrm{term}_1$ the unique values making it true; $L_1$ assigns $x_1$ so that if $f|L_1\rho$ is an $(s-1)$-CNF then $f|\rho$ is an $s$-CNF, with $\mathrm{term}_1$ being $?$ or False under $L_1\rho$. Let $\mathrm{term}_2$ be the first $?$-valued term of $f|L_1\rho$ (with $\mathrm{term}_2\ge\mathrm{term}_1$) and $x_2$ its first unassigned variable; $R_2$ makes $\mathrm{term}_2$ the first true term of $f|R_2L_1\rho$, and $L_2$ makes $f|L_2L_1\rho$ not an $(s-2)$-CNF. Iterating gives $L_1,\dots,L_s,R_1,\dots,R_s$. With $\rho_i=L_i\cdots L_1\rho$ ($\rho_0=\rho$), for $1\le i\le s$: (i) $\mathrm{term}_i$ is the first $?$-valued term of $f|\rho_{i-1}$; (ii) $\mathrm{term}_i$ is the first true term of $f|R_i\rho_{i-1}$; (iii) $L_i$ agrees with $\rho_{i-1}$ on all variables assigned by $\rho_{i-1}$; (iv) $R_i$ agrees with $\rho_i$ on all variables assigned by $\rho_i$. Define $\tau_i=R_iR_{i+1}\cdots R_s\rho_s$ for $1\le i\le s$ and $\tau_{s+1}=\rho_s$; then $\mathrm{term}_i$ is the first true term of $f|\tau_i$. Introduce $2s$ strings $z_i,w_i\in\{0,1,?\}^s$: $z_i$ gives the values $\rho_{i-1}$ assigns to $\mathrm{term}_i$'s $k$ variables, and $w_i$ the values $\tau_{i+1}$ assigns them. From $(\mathrm{term}_i,z_i,\rho_i)$ one computes $\rho_{i-1}$.

<a id="pdf-52929dbaa962-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.82 -->
**Proof (cont.).** From $(\mathrm{term}_i,w_i,\tau_i)$ one computes $\tau_{i+1}$. Map $\rho\mapsto(\tau_1;\,z_1,\dots,z_s,\,w_1,\dots,w_s)$. Since $\tau_1$ assigns $\ge s$ variables not assigned by $\rho$, and from $\tau_1$ one recovers $\mathrm{term}_1$ (first true term of $f|\tau_1$) then uses $w_1$ to obtain $\tau_2$, iterating recovers $\rho$. Hence this is a one-to-one map from $T_{t,s}$ into $Z\times\{0,1,?\}^{2ks}$. $\blacksquare$

<a id="pdf-52929dbaa962-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
**13.2 Circuits With "Counters": ACC**

<a id="pdf-52929dbaa962-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.85 -->
Extending AC$^0$ lowerbounds by allowing more general (e.g. parity) gates. An AC$^0$ circuit with parity gates computes parity but still fails on some functions; Razborov gave the first such lowerbound via the Method of Approximations, later extended and clarified by Smolensky. It suffices to consider modular gates with $0/1$ output.

<a id="pdf-52929dbaa962-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.95 -->
**Definition 13.3 (modular gates).** For an integer $m$, the $\mathrm{MOD}_m$ gate outputs $0$ if the sum of its inputs is $\equiv 0 \pmod m$, and $1$ otherwise.

<a id="pdf-52929dbaa962-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.90 -->
**Definition 13.4 (ACC).** For integers $m_1,\dots,m_k>1$, a language $L$ is in $\mathrm{ACC}^0[m_1,\dots,m_k]$ if there is a constant-depth, polynomial-size, unbounded-fan-in circuit family $\{C_n\}$ of $\wedge,\vee,\neg$ and $\mathrm{MOD}_{m_1},\dots,\mathrm{MOD}_{m_k}$ gates accepting $L$. $\mathrm{ACC}^0$ is the union of $\mathrm{ACC}^0(m_1,\dots,m_k)$ over all $k\ge 0$ and $m_1,\dots,m_k>1$. Good lowerbounds are known only when the circuit has a single kind of modular gate.

<a id="pdf-52929dbaa962-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.95 -->
**Theorem 13.5 (Razborov, Smolensky).** For distinct primes $p$ and $q$, the function $\mathrm{MOD}_p$ is not in $\mathrm{ACC}^0(q)$.

<a id="pdf-52929dbaa962-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.92 -->
**Proof (outline, shown for parity $\notin\mathrm{ACC}^0(3)$).** Two steps. **Step 1:** by induction on $h$, any depth-$h$ $\mathrm{MOD}_3$ circuit on $n$ inputs of size $S$ admits a polynomial of degree $(2l)^h$ agreeing with it on a $\ge 1-S\cdot 2^{-l}$ fraction of inputs; setting $2l=n^{1/2d}$ for a depth-$d$ circuit $C$ yields a degree-$\sqrt n$ polynomial agreeing with $C$ on a $\ge 1-S\cdot 2^{-n^{1/2d}/2}$ fraction of inputs. **Step 2:** no degree-$\sqrt n$ polynomial agrees with $\mathrm{MOD}_2$ (parity) on more than a $49/50$ fraction of inputs.

<a id="pdf-52929dbaa962-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.90 -->
**Step 1 (details).** Combining the two steps gives $S>2^{n^{1/2d}/2}/50$ for any depth-$d$ circuit computing $\mathrm{MOD}_2$, proving the theorem. For a node $g$ at depth $h$ computing $g(x_1,\dots,x_n)$, build $\tilde g$ over $GF(3)$ of degree $(2l)^h$ with $g=\tilde g$ on most inputs in $\{0,1\}^n$, and $\tilde g$ taking values in $\{0,1\}$ on all of $\{0,1\}^n$ (square it; in $GF(3)$, $0^2=0$, $1^2=1$, $(-1)^2=1$). Induction: at $h=0$ an input wire $x_i$ is exactly the degree-1 polynomial $x_i$. Given approximators for height $\le h-1$:

1. **NOT** $g=\neg f_1$: set $\tilde g=1-\tilde f_1$; same degree, no new error.
2. **$\mathrm{MOD}_3$** with inputs $f_1,\dots,f_k$: set $\tilde g=\big(\sum_i \tilde f_i\big)^2$; degree $\le 2(2l)^{h-1}<(2l)^h$, no new error.
3. **AND/OR:** naive $\prod_i \tilde f_i$ (AND) or $1-\prod_i(1-\tilde f_i)$ (OR, by De Morgan) multiplies degree by the fan-in $k$, which may exceed $2l$. Correct OR method: $g=\bigvee_i f_i=1$ iff some $f_i=1$; by the random subsum principle, if some $f_i=1$ then the $GF(3)$ sum over a random subset of $\{f_i\}$ is nonzero with probability $\ge 1/2$. Randomly pick $l$ subsets $S_1,\dots,S_l$ of $\{1,\dots,k\}$, form $\big(\sum_{j\in S_i}\tilde f_j\big)^2$ (degree $\le$ twice the largest input polynomial), and OR the $l$ terms naively, giving degree $\le 2l\cdot(2l)^{h-1}=(2l)^h$. For any $x$, the probability over the subset choice that this differs from $\mathrm{OR}(\tilde f_1,\dots,\tilde f_k)$ is $\le 2^{-l}$; by the probabilistic method some fixed choice of subsets makes the error probability over $x$ at most $2^{-l}$, and that choice defines the approximator.

Applying this per gate gives an approximator for the output gate of degree $(2l)^d$; each gate adds error on at most a $2^{-l}$ fraction of inputs, so total error is $\le S\cdot 2^{-l}$ (errors at different gates may interact/cancel).

<a id="pdf-52929dbaa962-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.92 -->
**Step 2.** If a polynomial f of degree ≤ √n agrees with MOD2 on a set G′ ⊆ {0,1}^n, then |G′| < (49/50)·2^n. Apply the change of variables yi = 1 + xi (mod 3), which sends 0 → 1 and 1 → −1; G′ maps to a set G ⊆ {−1,1}^n with |G| = |G′|, and f becomes a degree-√n polynomial g(y1,…,yn). Then (eq 2) MOD2(x) = 1 ⟺ Π_{i=1}^n yi = −1 and MOD2(x) = 0 ⟺ Π_{i=1}^n yi = 1, so g agrees with Π_{i=1}^n yi on G. Let FG be the set of all functions S: G → {0,1,−1}, so |FG| = 3^{|G|}; the goal is to show |FG| ≤ 3^{(49/50)·2^n}, from which Step 2 follows.

<a id="pdf-52929dbaa962-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.90 -->
**Lemma 13.6.** For every S ∈ FG there exists a polynomial gS, expressible as a sum of monomials aI · Π_{i∈I} yi with |I| ≤ n/2 + √n, such that gS(x) = S(x) for all x ∈ G.

<a id="pdf-52929dbaa962-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.85 -->
**Proof.** Let ˆS: GF(3)^n → GF(3) agree with S on G, written as a polynomial in the yi. Since only values on (y1,…,yn) ∈ {−1,1}^n matter and yi² = 1 there, each exponent may be taken ≤ 1, so deg ˆS ≤ n. For any monomial Π_{i∈I} yi with |I| > n/2, rewrite (eq 3) Π_{i∈I} yi = Π_{i=1}^n yi · Π_{i∈Ī} yi, which takes the same values as g(y1,…,yn)·Π_{i∈Ī} yi over {−1,1}^n and has degree ≤ (n − |I|) + √n < n/2 + √n. Hence every monomial of ˆS can be reduced to degree ≤ n/2 + √n. ∎

<a id="pdf-52929dbaa962-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.85 -->
**Conclusion.** Bound the number of polynomials all of whose monomials have degree ≤ n/2 + √n: #polynomials ≤ 3^{#monomials}, where (eqs 4–5) #monomials ≤ |{N ⊆ {1···n} : |N| ≤ n/2 + √n}| ≤ Σ_{i ≤ n/2+√n} C(n, i). Using knowledge of the tails of a binomial distribution (or direct calculation), this gives #monomials ≤ (49/50)·2^n (eq 6), hence |FG| ≤ 3^{(49/50)·2^n} and so |G| ≤ (49/50)·2^n, completing Step 2. ∎

<a id="pdf-52929dbaa962-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->
**13.3 Lowerbounds for monotone circuits.** A Boolean circuit is *monotone* if it contains only AND and OR gates and no NOT gates; such a circuit computes exactly the monotone functions.

<a id="pdf-52929dbaa962-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.93 -->
**Definition 13.7.** For x, y ∈ {0,1}^n, write x ⪯ y if every bit that is 1 in x is also 1 in y. A function f: {0,1}^n → {0,1} is *monotone* if f(x) ≤ f(y) for every x ⪯ y. **Remark 13.8.** Equivalently, f is monotone iff for every input x, flipping any bit of x from 0 to 1 can never change f's value from 1 to 0. Every monotone circuit computes a monotone function and vice versa; CLIQUE is monotone since adding an edge cannot destroy an existing clique.

<a id="pdf-52929dbaa962-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.90 -->
**Theorem 13.9 ([Raz85b, AB87]).** Let CLIQUE_{k,n}: {0,1}^{C(n,2)} → {0,1} be the function that, on the adjacency matrix of an n-vertex graph G, outputs 1 iff G contains a k-vertex clique. There exists a constant ε > 0 such that for every k ≤ n^{1/4}, no monotone circuit of size less than 2^{ε√k} computes CLIQUE_{k,n}.

<a id="pdf-52929dbaa962-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.88 -->
It is conjectured that CLIQUE has no polynomial-size circuits even with NOT gates (NP ⊄ P/poly). The plausible approach of showing monotone circuit complexity is polynomially related to general circuit complexity fails: Razborov ([Raz85a], [Tar88]) refuted this.

<a id="pdf-52929dbaa962-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.87 -->
**Clique indicators.** For S ⊆ [n], let C_S be the function on {0,1}^{C(n,2)} that outputs 1 on a graph G iff S is a clique in G (the *clique indicator* of S). Then CLIQUE_{k,n} = OR_{|S|=k} C_S. Claim: CLIQUE_{k,n} cannot be computed by an OR of fewer than n^{√k/20} clique indicators.

<a id="pdf-52929dbaa962-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.90 -->
Define a positive distribution 𝒴 on n-vertex graphs: pick a random K ⊆ [n] with |K| = k and output the graph consisting of a clique on K with no other edges. Define a negative distribution 𝒩: pick a random c: [n] → [k−1] and place an edge between u and v iff c(u) ≠ c(v). With probability 1, CLIQUE_{n,k}(𝒴) = 1 and CLIQUE_{n,k}(𝒩) = 0. The n^{√k/20} lower bound on the number of clique indicators follows from a lemma stated on the following page.
