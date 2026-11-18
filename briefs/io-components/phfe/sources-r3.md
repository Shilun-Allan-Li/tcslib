# io-phfe: sources, r3 (partial garbling pinned)

Prepared 2026-11-18 at records tip `43eacf952cfc9517f9be8f93e367f658effd9b47`. Static reading
only: the page images of every location below were read, and text extracts were used only to
locate pages. **r3 is a delta over `sources-r2.md`**: §§ 2–4 of r2 stand except where this file
amends them. What r3 adds:
- the two partial-garbling sources Seyoon supplied: [AGW20] and [IW14] (decision-log row
  *Partial-garbling sources received*);
- the pin of [Wee20, Lemma 1] against them;
- the Lemma 1 shape settlement;
- the misprint list, renumbered and extended;
- gap G7 closed, and G3/G4 updated for the rulings.

Page numbers:
- [AGW20] and [IW14]: the printed page equals the PDF page index (checked: AGW20's table of
  contents puts §A on p. 37, which is PDF page 37; IW14 prints its page numbers).
- [GJLS21]: printed = PDF − 4, as r2.

## 1. The files (all five)

| Tag | Item | SHA-256 | Bytes / pages | Revision |
|---|---|---|---|---|
| [JLS26] | as sources-r2 § 1 | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | 771,518 / 30 | journal version |
| [GJLS21] | as sources-r2 § 1 | `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed` | 747,888 / 85 | ePrint 2020/764, 2025-01-03 |
| [Wee20] | as sources-r2 § 1 | `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a` | 203,547 / 14 | ePrint 2020/1420 |
| **[AGW20]** | M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted Sums from k-Lin*, CRYPTO 2020; full version Cryptology ePrint Archive 2020/762 ([Wee20, ref. 2]) | `b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f` | 439,603 / 39 | full version (pdfTeX, PDF created 2020-06-21). The file carries no ePrint stamp; the ePrint number is Seyoon's (decision-log row) |
| **[IW14]** | Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, ICALP 2014, Part I, LNCS 8572, pp. 650–662; full version Cryptology ePrint Archive 2014/995 ([Wee20, ref. 17]; [AGW20, ref. 30]) | `ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77` | 120,947 / 20 | full version (XeTeX, PDF created 2014-07-07). No ePrint stamp; the number is Seyoon's |

All five sit in the maintainer scratchpad (`io-sources/`). They are not committed (pairing Q12(A)).
Seyoon stages them on the exchange at `outbox/io-components/sources/`, with a `SHA256SUMS`
carrying the five hashes above (README step 3).

Still not staged, cited only through the staged papers:
- [EHKRV13] (via [Wee20, §2.1]);
- [BBS04] (via JLS26);
- **[IK02]**: Y. Ishai, E. Kushilevitz, *Perfect constant-round secure computation via perfect
  randomizing polynomials*, ICALP 2002 ([AGW20, ref. 29]; [IW14, ref. 26]). It is the source of
  the determinant lemma [AGW20, Lemma 12] = [IW14, Lemma 1], which the r3 instance does **not**
  use (§ 3).
- [Wee17] ([Wee20, ref. 23]; [AGW20, ref. 43]).

## 2. Where each item is (new: [AGW20], [IW14]; amended: [Wee20])

### [AGW20]
- **§4.1, pp. 11–12: FE for attribute-weighted sums.**
  - Syntax: Setup, Enc of N pairs (x_i, z_i) with x_i public, KeyGen for f ∈ F_{ABP,n,n'}, Dec
    outputs Σ f(x_i)^⊤z_i in ℤ_p.
  - Correctness with probability 1; Remark 1 (bounded-value Dec).
  - **Security definition (p. 11): semi-adaptive simulation**, citing [18] = Chen–Wee, SCN 14:
    1^N ← A(1^λ); Setup; (x*_i, z*_i) ← A(mpk); ct* ← Enc; output A^{KeyGen(msk,·)}(mpk, ct*),
    against Setup*, Enc*(msk*, (x*_i)), KeyGen*(msk*, (x*_i), ·, ·). KeyGen* gets f with
    Σ f(x*_i)^⊤z*_i.
  - "One-slot scheme" (p. 12) is N = 1. This is [Wee20, §2.2]'s notion; Wee20 copies the text.
- **§4.2, p. 12: Partial Garbling Scheme and Lemma 2 (partial garbling [30, 43]).**
  - Wee20's Lemma 1 is this lemma, transposed (AGW20 uses column vectors, f(x)^⊤z; Wee20 rows,
    z f(x)^⊤).
  - Syntax: lgen(f) outputs L₀, L₁; pgb(f, x, z; t) = (z^⊤ − t̲^⊤, t^⊤(L₁(x ⊗ I_m) + L₀));
    pgb*(f, x, µ; t) = (−t̲^⊤, t^⊤(L₁(x ⊗ I_m) + L₀) + µ·e₁^⊤).
  - **t ∈ ℤ_p^{m+n'−1}**, with t̲ its last n' entries; m is linear in the size of f.
  - Reconstruction: rec(f, x) = d_{f,x} ∈ ℤ_p^{n'+m} with p^⊤_{f,x,z} d_{f,x} = f(x)^⊤z.
  - Privacy: pgb(f, x, z; t) ≈_s pgb*(f, x, f(x)^⊤z; t) over t ← ℤ_p^{m+n'−1}.
  - **Lemma 2 states the same swapped shapes as Wee20's Lemma 1** (L₀ with mn columns, L₁ with
    m); § 3 settles them.
  - "Extension" (shifts by δ, p. 12): **not used by Wee20's Π** (Π is AGW20's one-slot Π_one,
    §5), so not formalised.
- **§5, pp. 12–18: Π_one**, of which [Wee20, §4.2] is "a somewhat straight-forward
  modification" ([Wee20, §4, p. 8]).
  - Theorem 2 (p. 15) is the analogue of [Wee20, Theorem 1].
  - Lemma 3 (statistical lemma, p. 15) underlies [Wee20, Lemma 3].
  - Lemmas 4–7 (pp. 16–18) are the four hops.
  - The proof of Lemma 5 (p. 17) is where the semi-adaptive order matters. Wee20 repeats its
    remark on p. 14 (the "random guessing argument").
- **Appendix A, pp. 37–38: Partial Garbling** ("a restatement of the partial garbling schemes in
  [30, 43]"). Contents:
  - **Lemma 12 ([29, 30]), p. 37.** For f ∈ F_{ABP,n,n'} and (x, z), a matrix
    L_{x,z} ∈ ℤ_p^{(m+n')×(m+n')} has det L_{x,z} = f(x)^⊤z, entries affine in (x, z), −1's on
    the second diagonal and 0's below. L_{x,z} is A − I of the ABP with the v₀ column and the v₁
    row removed. L_x is L_{x,z} without its last column, and depends on x and f only.
  - **The family 𝒯** of (m+n')×(m+n') matrices (I_{m+n'−1} t; 0 1), with properties:
    1. det T = 1;
    2. T(t; 1) is distributed as (t; 1) for uniform t;
    3. ∃ T ∈ 𝒯 with L_{x,z}T = (L_x | e₁·f(x)^⊤z).
  - **(28)** p_{f,x,z} = L_{x,z}(t; 1), t ← ℤ_p^{m+n'−1}.
  - **(29)** reconstruction: det(L_x | p_{f,x,z}) = det(L_{x,z}T) = f(x)^⊤z.
  - **(30)** privacy: simulate (L_x | e₁·f(x)^⊤z)(t; 1).
- **Appendix A, p. 38: "Algorithm lgen and pgb, pgb*".**
  - L̄_x ∈ ℤ_p^{m×(m+n'−1)} is L_x without its last n' rows.
  - **(31)** p^⊤_{f,x,z} = (z^⊤ − t̲^⊤, t^⊤L̄_x^⊤).
  - **(32)** L̄_x^⊤ = L₁(x ⊗ I_m) + L₀, "where L₁ is formed from n matrices of size
    (m+n'−1)×m, the i-th of which consists of coefficients of x_i …, and L₀ includes the constant
    term".
  - "Algorithm rec": d_{f,x} is the cofactor vector of det(L_x | ·), and (0, e₁^⊤)d_{f,x} = 1.
- **Appendix B, p. 38: KeyGen of Π_ubd** writes "L₁ ∈ ℤ_p^{(m+n'−1)×mn}, L₀ ∈ ℤ_p^{(m+n'−1)×m}",
  the correct shapes (§ 3).
- References (pp. 35–36): [18] Chen–Wee SCN 14; [29] [IK02]; [30] [IW14]; [43] [Wee17].

### [IW14]
- **§2, p. 6, Lemma 1 ([26, Lemma 1] = [IK02]).** An ABP Γ = (V, E, v₀, v₁, φ) computing f gives
  L(x) ∈ F_q^{(|V|−1)×(|V|−1)} with det L(x) = f(x), entries of degree ≤ 1 in one variable, −1's
  on the second diagonal and 0's below. This is the same lemma as [AGW20, Lemma 12].
- **§3, p. 6: Definition 1 ((affine) partial garbling scheme).** F̂ : F_q^n × F_q^{n'} → F_q^m
  is a PGS of F if two conditions hold:
  - **(correctness)** a deterministic Rec has Pr[Rec(x, F̂(x, z)) = F(x, z)] = 1;
  - **(privacy)** a randomised Sim has Sim(x, F(x, z)) and F̂(x, z) **identically distributed**.
  - "Affine": each output is a_j x_i + b_j or a_j z_i + b_j, with coefficients depending only on
    the randomness.
- **p. 7.** x-affine and z-affine variants, and the efficiency requirement for families
  ("an efficient deterministic garbling algorithm for computing the description of F̂, Rec and
  Sim from that of F"). Examples 1–3: Example 1, the non-zero product x₁x₂x₃z garbled as
  (r₁x₁, r₁ − r₂x₂, r₂ − r₃x₃, r₃ − z), is, up to signs, the layered case of § 3 below for one
  path.
- **§4, p. 8: Partially Garbling ABPs.** The class: private variables only on edges into the last
  t vertices. Fig. 1 gives the matrices for Examples 1–2. **Theorem 3 (partially garbling ABP)**:
  output length t·(|V| − 1), entries of total degree one in x and z, and Rec of degree t.
- **p. 9: Corollary 1 (affine PGS for ABP)**, via the locality lemma.
- **§4.2, pp. 9–11: the construction.**
  - Definition 2: the matrix set ℋ and the groups 𝒢₁, 𝒢₂.
  - Lemma 2: 𝒢₁ℋ𝒢₂ preserves the first ℓ − t columns.
  - Lemma 3: canonical form. G₁HG₂ has −1's on the second diagonal and 0's elsewhere except det H
    in the top-right entry.
  - The PGS outputs the last t columns of R₁L(x, z)R₂ with R₁ ← 𝒢₁, R₂ ← 𝒢₂.
  - Correctness by det; privacy by the canonical form (p. 11).
  - **At IW14's t = 1** (z only on edges into v₁, the case of f(x)^⊤z), 𝒢₁ is trivial. The
    output is then the last column of L·R₂ = L(t; 1): exactly [AGW20, (28)]. [AGW20, App. A]
    is this case, transposed.
- IW14's letters differ: its t is the number of private-input vertices and its ℓ = |V| − 1.
  Wee20's t is the randomness length.

### [Wee20] (amendments to sources-r2 § 2)
- **§4.1, p. 8 (prose and the syntax line of Lemma 1)** and **p. 9 (reconstruction, privacy)**:
  Lemma 1 = [AGW20, Lemma 2], cited as [2, 17, 23] = [AGW20], [IW14], [Wee17].
  - Formulas: pgb(f, x, z; t) = (z − t̲ ‖ t(L₁(x^⊤ ⊗ I_m) + L₀)) and
    pgb*(f, x, µ; t) = (−t̲ ‖ t(L₁(x^⊤ ⊗ I_m) + L₀) + µ·e₁), with t ∈ ℤ_p^t and "m, t linear in
    the size of f".
  - Reconstruction gives d_{f,x} ∈ ℤ_p^{n'+m} with p d^⊤ = z f(x)^⊤.
  - Privacy is stated with ≈_s.
  - **Wee20 does not fix t; AGW20 does (t = m + n' − 1).**
- **§4.2, p. 9.** KeyGen runs "(L₁, L₀) ← lgen(f) where L₁ ∈ ℤ_p^{t×mn}, L₀ ∈ ℤ_p^{t×m}" (the
  correct shapes), samples T ← ℤ_p^{(k+1)×t} and R ← ℤ_p^{k×m}, and outputs
  ([T̲ + WM]₂, [TL₁ + U(I_n ⊗ R)]₂, [TL₀ + VR]₂, [R]₂).
- **App. B, p. 14, proof of Lemma 3: "We clarify that in the semi-adaptive security game,
  (x*, z*) are chosen after seeing A^⊤U, A^⊤W, A^⊤V. Since the two distributions are identically
  distributed, the distinguishing advantage remains 0 even for adaptive choices of x*, z* via a
  random guessing argument."** design-r3 § 4.8 replaces the guessing argument by a bijection
  that fixes the public part.
- **App. B, p. 14, Lemma 5.** Game 4 ≈_s Game 5 by partial-garbling privacy, after the change of
  variables û_j^⊤ ↦ û_j^⊤ − t̲_j^⊤L_{1,j}. With an exact instance (§ 3) it is an identity.
- **App. B, p. 12, "Game sequence".** "for notational simplicity, assume that all key queries f_j
  share the same parameters t and m". With the r3 instance, m and t depend only on the class
  parameters (ℓ, d, n'), not on f's coefficients, so the assumption holds exactly (§ 3).
- **App. B, p. 13, Lemma 4.** MDDH^n_{k,mQ}, where Q is the number of key queries. The
  semi-adaptive game therefore needs a query budget q(κ) (design-r3 § 4.5).

## 3. Partial garbling pinned: what [Wee20, Lemma 1] needs, where it is proved, the instance

**What Lemma 1 must provide to Π** ([Wee20, §4.2] and App. B, read line by line):

| Property | Wee20 | Used in | Source of a proof |
|---|---|---|---|
| syntax: lgen(f) = (L₁ ∈ ℤ_p^{t×mn}, L₀ ∈ ℤ_p^{t×m}), depending on f only; t ≥ n' | Lemma 1, p. 8 (shapes corrected: W1) | KeyGen's [TL₁ + U(I_n ⊗ R)], [TL₀ + VR] (p. 9); Dec's K₂(x^⊤ ⊗ I_m) (7) | [AGW20, App. A, (32)] and [AGW20, App. B] (shapes); t = m + n' − 1 by [AGW20, Lemma 2, p. 12] |
| pgb = (z − t̲ ‖ t(L₁(x^⊤ ⊗ I_m) + L₀)): **affine in x**, linear in t | Lemma 1 | correctness (9)–(11): (p₁‖p₂) = pgb(f, x, zM; sAT) | [AGW20, App. A, (28), (31), (32)] |
| reconstruction: d_{f,x} with pgb(f, x, z; t)·d^⊤ = z f(x)^⊤ **for every t** | Lemma 1, p. 9 | (8), (11) | [AGW20, App. A, (29), "Algorithm rec"]; [IW14, Def 1 (correctness), §4.2 p. 11] |
| pgb* = (−t̲ ‖ t(L₁(x^⊤ ⊗ I_m) + L₀) + µ·e₁): affine in µ, so computable from [µ]₂ in the group | Lemma 1 | the simulator's KeyGen* (12), p. 10 | [AGW20, App. A, (30)] |
| privacy: pgb(f, x, z; ·) and pgb*(f, x, z f(x)^⊤; ·) **identically distributed** over t | Lemma 1 (≈_s) | Lemma 5, p. 14 | **exact**: [AGW20, App. A, properties 1–3 and (30)]; [IW14, Def 1 (privacy: "identically distributed"), §4.2 p. 11] |

**Lemma 1's L₀/L₁ shapes, settled.** The formula t(L₁(x^⊤ ⊗ I_m) + L₀) with x ∈ ℤ_p^n forces
L₁ ∈ ℤ_p^{t×mn} and L₀ ∈ ℤ_p^{t×m}, since x^⊤ ⊗ I_m is mn × m. Three places agree:
- [AGW20, App. A, (32), p. 38]: "L₁ is formed from n matrices of size (m+n'−1)×m … L₀ includes
  the constant term";
- [AGW20, App. B, p. 38];
- [Wee20, §4.2, p. 9].

The swapped shapes are in [Wee20, Lemma 1] (prose and syntax line, p. 8) **and already in
[AGW20, Lemma 2] (p. 12)**, from which Wee20 copies "verbatim" (Wee20 §4, p. 8). So **W1 is
inherited from AGW20**. With AGW20's t = m + n' − 1:
- **L₁ ∈ ℤ_p^{(m+n'−1)×mn};**
- **L₀ ∈ ℤ_p^{(m+n'−1)×m}.**

**The function class.** Wee20 states Lemma 1 for f ∈ F_{ABP,n,n'}. r2 restricts every layer to
vectors of degree-≤ d polynomials, f(x) = C·x̂^{⊗d}, where:
- x̂ = (x, 1) ∈ ℤ_p^{ℓ+1};
- C ∈ ℤ_p^{n' × (ℓ+1)^d}, the coefficient tensor over tuples τ : Fin d → Fin (ℓ+1)
  (design-r2 § 4.6).

r3 keeps that class.

**The instance, chosen for least work: [AGW20, App. A, (28)–(32)] (= [IW14, §4.2] at IW14's
t = 1) applied to the layered ABP of a polynomial vector.**
- **The ABP Γ_C.**
  - Nodes: the source v₀ = the empty tuple; the tuples τ ∈ (ℓ+1)^k for k = 1..d; the n'
    "output" nodes j; the sink v₁.
  - Edges: τ → τ·a labelled x̂_a (affine in x), for k < d; τ → j labelled C_{j,τ} (a constant),
    for |τ| = d; j → v₁ labelled z_j.
  - It computes f(x)^⊤z = Σ_j z_j Σ_τ C_{j,τ} ∏_i x̂_{τ_i}. Its private variables are only on
    edges into v₁ (IW14 §4's class, with IW14's t = 1).
- **Sizes.** m = Σ_{k=0}^{d} (ℓ+1)^k (all nodes but the output nodes and the sink), and
  t = m + n' − 1 (all nodes but v₀ and v₁), as [AGW20, Lemma 2] requires. **m and t depend
  only on (ℓ, d, n')**, so Wee20's "same t and m for all keys" (App. B, p. 12) holds exactly.
- **The scheme, verbatim [AGW20, (28)].** The rows of L_{x,z}(t; 1) are indexed by the nodes
  other than v₁, with t indexed by the nodes other than v₀ and t_{v₁} = 1:
  - for u ∈ {v₀} ∪ tuples: p_u = Σ_{v child of u} label(u→v)·t_v − t_u, with no t_u term at
    u = v₀;
  - for an output node j: p_j = z_j − t̲_j.
  - Then (31) splits p into p₁ = z − t̲ (the output-node rows) and p₂ = t·(L₁(x^⊤ ⊗ I_m) + L₀)
    (the m remaining rows, **v₀'s row first**, so e₁ is v₀'s coordinate). L₀ and L₁ are the
    explicit 0/±1/C matrices of (32).
- **The proofs, by path sums instead of determinants** (disclosed proof-route deviation; the
  statements are [AGW20, Lemma 2]'s, with the shapes corrected):
  - *reconstruction*: d_u = ∏_{i<|u|} x̂_{u_i} (the forward path value from v₀ to u; d_{v₀} = 1,
    matching "(0, e₁^⊤)d_{f,x} = 1", AGW20 p. 38) and d_j = f_j(x). Then p·d^⊤ telescopes to
    z f(x)^⊤, because Σ_{u parent of v} label(u→v)·d_u = d_v for every v ≠ v₀.
  - *privacy, exact*: let s_v be the backward path value from v to v₁ (s_j = z_j;
    s_τ = Σ_j C_{j,τ}z_j for |τ| = d; s_u = Σ_a x̂_a s_{u·a} for |u| < d). Then
    pgb(f, x, z; t) = pgb*(f, x, s_{v₀}; t − s), and s_{v₀} = z f(x)^⊤. So the translation
    t ↦ t − s carries one law to the other (`expect_sample_equiv` with `Equiv.addRight`).
    That is privacy with **δ = 0**, as [IW14, Def 1] requires and as [AGW20, App. A, property 2]
    gives.
  - These are the [AGW20, App. A] facts (29)–(30), specialised to a DAG. They need no [IK02]
    determinant lemma, no 𝒯/𝒢-group calculus, and no ABP datatype.
- **Rejected alternatives.**
  - (b) The general ABP instance [AGW20, App. A] / [IW14, §4.2] with the determinant route needs
    an ABP model, [IK02, Lemma 1] ([AGW20, Lemma 12]), the canonical-form lemma [IW14, Lemma 3],
    cofactor expansion, and a compiler from polynomial vectors to ABPs. That is ≈ 2,500–4,500
    lines against ≈ 500–1,000.
  - (c) IW14's Corollary 1 (fully affine) is not what Lemma 1 asks: Lemma 1 is x-affine and
    bilinear in (t, x).

## 4. Wee20's misprints (replaces the list in sources-r2 § 2)

r2 recorded these readings in four bullets plus a note on the symmetric instantiation. r3
numbers them W1–W5 (W2 and W3 were one r2 bullet). Each is recorded as a reading in the
fidelity table, never copied, never patched silently.

| # | Where | Printed | Read as | Basis |
|---|---|---|---|---|
| W1 | Lemma 1, p. 8 (prose and syntax line) | L₀ ∈ ℤ_p^{t×mn}, L₁ ∈ ℤ_p^{t×m} | L₁ ∈ ℤ_p^{t×mn}, L₀ ∈ ℤ_p^{t×m}, t = m + n' − 1 | § 3; inherited from [AGW20, Lemma 2, p. 12]; correct in [Wee20, §4.2, p. 9], [AGW20, (32) and App. B, p. 38] |
| W2 | §3.2 Enc*, p. 7; Game 4, p. 8 | [y₂]₁ in ct*; "[s₂A₂ + z*₂]₁" replaced by "[y₂]₁" | [y₂]₂, [s₂A₂ + z*₂]₂ | §3.1, p. 6: ct = ([y₁]₁, [y₂]₂, ct₀) |
| W3 | Game 3 and Game 4, p. 8 | y₁ ← ℤ_q^{n'₁}; y₂ ← ℤ_q^{n'₂} | ℤ_p | p is the group order throughout (§2.1). **r3 adds Game 3's occurrence**; r2 noted only Game 4's |
| W4 | §3.2 KeyGen*, p. 7 | [(y₁ ⊗ y₂) f(x*)]_T · [µ]₂^{−1} | [(y₁ ⊗ y₂) f(x*)^⊤]₂ · [µ]₂^{−1} | KeyGen₀* takes a G₂ element (§3, p. 6: "the simulator gets [zMf(x)^⊤]₂"); Game 2, p. 7 |
| W5 | §2.1, p. 4, bilateral MDDH | "[MS]₁, [M]₂, [MS]₁) = 2]" | "[MS]₁, [M]₂, [MS]₂) = 1]" | the random branch: [U]₁, [U]₂ … = 1 |

r2's note stands: in the symmetric instantiation the subscripts 1 and 2 coincide, so only W4's
G vs G_T reading changes a statement.

**Further readings found in r3** (recorded in the fidelity table; none changes a statement):
- R1, §3.2 Setup*, p. 7: "Setup₀*(p, 1^n, 1^{k'n₁+kn₂})". Read n'₁, n'₂ (as §3.1).
- R2, §3.1 Setup, p. 6, passes [M]₂ to Setup₀, while §4.2 passes [M]₂ to KeyGen with each key
  (and §3.1's Dec passes (f, [M]₂) to Dec₀). Read §4's form: per-key [M]₂. The outer scheme
  uses one M for all keys.
- R3, §3.3 Game 1, p. 7: s₀ is sampled and never used. Drop it.
- R4, Lemma 1 privacy is written ≈_s. With the r3 instance it is exact (identical
  distributions, [IW14, Def 1]), so [Wee20, Lemma 5] is an identity.

## 5. The chain (amendments to sources-r2 § 3(c))

| # | r2 | r3 |
|---|---|---|
| G3 adaptivity | the job proves the Def 4.3 form directly | **ruling Q3 (second batch)**: the job proves **[Wee20, §2.2]'s semi-adaptive SIM notion for both layers** (Π and the outer scheme), with keys asked adaptively after ct*. [GJLS21, Definition 4.3] is then **derived** as a special case: a two-stage (A₁, A₂) adversary is the semi-adaptive adversary that ignores mpk, commits, and asks its pre-committed keys. No loss (design-r3 § 4.5) |
| G4 the simulator's input | ruling needed (Q1) | **ruling Q1 (first batch)**: µ_j ∈ ℤ_p, per [GJLS21, Thm 9.2] proof, Hybrid 1, p. 61 (printed). A disclosed deviation from Def 4.3's literal G_T value. Π's simulator receives g^{µ} ([Wee20, §3, p. 6; §4, p. 8]), which the outer simulator computes from µ |
| G7 partial garbling | source not staged (Q2) | **closed**: interface = [Wee20, Lemma 1] = [AGW20, Lemma 2] with W1 corrected; instance § 3 above; **ruling Q2 (first batch)**: interface + proved instance in this job |

## 6. Citations for the Lean docstrings (adds to sources-r2 § 4)

- `[AGW20, §4.2, Lemma 2]` (p. 12) and `[AGW20, Appendix A, (28)–(32)]` (pp. 37–38): the
  interface and the instance's scheme. `[AGW20, §4.1]` (p. 11): the semi-adaptive notion (with
  `[Wee20, §2.2]`).
- `[IW14, Definition 1]` (p. 6): partial garbling, exact privacy. `[IW14, Theorem 3]` (p. 8) and
  `[IW14, §4.2]` (pp. 9–11): the ABP construction of which the instance is the case t = 1.
  `[IW14, Example 1]` (p. 7): the one-path case.
- `[IK02]`, `[Wee17]`: only "as cited in [AGW20, …]" (not staged; not needed).
- Wee20's Lemma 1 is now cited directly against its sources: "[Wee20, Lemma 1] = [AGW20,
  Lemma 2]".
