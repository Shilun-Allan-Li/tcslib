# io-phfe: sources, r2 (the chain pinned)

Prepared 2026-11-18 at records tip `1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae`, from the three PDFs
supplied to the maintainer (static reading: `pdftotext -layout` of every page, with page images
checked for each formula quoted below). This file supersedes `sources.md` (r1) on links (b) and (c);
r1's link (a) is confirmed unchanged.

Page numbers: [JLS26] and [Wee20] page numbers are the printed ones, which equal the PDF page
index. **[GJLS21] printed page = PDF page index − 4** (four front pages); both are given below.

## 1. The files

| Tag | Item | SHA-256 | Bytes / pages | Revision |
|---|---|---|---|---|
| [JLS26] | A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, doi:10.1145/3785007, CC BY 4.0 | `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d` | 771,518 / 30 | journal version (PDF created 2026-02-12); same file as r1 |
| [GJLS21] | R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*, EUROCRYPT 2021, LNCS 12698, pp. 97–126; full version Cryptology ePrint Archive 2020/764 | `481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed` | 747,888 / 85 | ePrint full version, PDF created 2025-01-03: the **latest revision** (r1 § 3(a)). Its Theorems 10.3/10.4 are the ones [JLS26, Thm 5.1] cites (checked: same hypotheses; § 3 below) |
| [Wee20] | H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*, TCC 2020, Part I, LNCS 12550, pp. 210–228, doi:10.1007/978-3-030-64375-1_8; full version Cryptology ePrint Archive 2020/1420 | `d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a` | 203,547 / 14 | ePrint version (PDF created 2020-11-11) |

The PDFs sit in the maintainer scratchpad (`io-sources/`). Under pairing ruling Q12(A) they are not
committed: Seyoon stages them on the exchange at `outbox/io-components/sources/` with a
`SHA256SUMS` carrying the three hashes above (README, step 2). Text extracts are scratch only.

Not staged, cited only through the staged papers (never quoted directly):
- **[EHKRV13]** A. Escala, G. Herold, E. Kiltz, C. Ràfols, J. Villar, *An algebraic framework for
  Diffie–Hellman assumptions*, CRYPTO 2013 ([Wee20, ref. 10]): "k-Lin ⇒ MDDH¹_{k,k+1} ⇒
  MDDH^d_{k,ℓ}, tight", as stated in [Wee20, §2.1, p. 4].
- **[AGW20]** M. Abdalla, J. Gong, H. Wee, *Functional encryption for attribute-weighted sums from
  k-Lin*, CRYPTO 2020 ([Wee20, ref. 2]); **[IW14]** Y. Ishai, H. Wee, *Partial garbling schemes and
  their applications*, ICALP 2014 ([Wee20, ref. 17]). Sources of [Wee20, Lemma 1] (partial
  garbling), which Wee20 states and does not prove: design-r2 Q2.
- **[BBS04]** Boneh–Boyen–Shacham (DLIN's origin, [JLS26, ref. 39]): as in r1.

## 2. Where each item is

### [JLS26] (unchanged from r1; re-read)
- §1.1, p. 3: DLIN on symmetric groups: λ-bit prime p, G, G_T of order p, symmetric e, "a canonical
  generator g"; `(g^x, g^y, g^{xr}, g^{ys}, g^{r+s}) ≈_c (g^x, g^y, g^{xr}, g^{ys}, g^z)`.
- §1.4, pp. 7–8: DLIN "directly gives public key PHFE scheme by the work of [155]" ([155] = Wee20);
  PHFE "for constant degree public computation and degree 2 private computation".
- Definition 2.1, pp. 8–9 (ε-indistinguishability; sub-exponential: ε(λ) = 2^{−λ^c}, some c > 0);
  Remark 2.1, p. 9 (security measured in each assumption's own parameter, here log p = λ).
- Definition 3.3, p. 10: sPRG ∈ (C, deg d) over ℤ_p, p = p(λ) "an efficiently computable function
  in λ"; Eval(I, sd) = Q_I(P̄, S), P̄ = Process_I(P), Q_I degree 1 in P̄ and degree d in S.
- Theorem 5.1, p. 21 = "(Theorem 10.3 and Theorem 10.4 [88])": λ the security parameter, p a λ-bit
  prime; sub-exponential **Bilateral-DLIN on asymmetric bilinear groups of order p (implied by the
  DLIN assumption on symmetric bilinear groups of order p)**, LWE, an sPRG with stretch 1 + τ and
  complexity (deg d, deg 2) over ℤ_p ⇒ iO (and compact FE under polynomial security).
- References [88], [89] (GJLS21 ePrint and EUROCRYPT), [155] (Wee20, TCC 2020).

### [GJLS21] (printed page / PDF page)
- p. 5 / 9: "[Wee20a] builds a public-key FE which support the same class of functions as our scheme
  (namely, NC¹ computation on the public input, and degree-2 on the private input)".
- §3, "Pairing groups", p. 17 / 21: a **sequence** of asymmetric prime-order groups
  G = {(p_λ, G_{λ,1}, G_{λ,2}, G_{λ,T}, P_{λ,1}, P_{λ,2}, P_{λ,T}, e_λ)}, order p_λ = 2^{λ^{Θ(1)}}
  (one group per λ, generators fixed); Remark 3.1 (efficient operations). The DLIN_p distribution:
  A = [[a, 0], [0, b], [1, 1]] ∈ ℤ_p^{3×2}, a, b ← ℤ_p.
- **Definition 3.3 (Bilateral DLIN)**, p. 18 / 22: `{[A]_s, [Ar]_s}_{s∈{1,2}} ≈ {[A]_s, [u]_s}_{s∈{1,2}}`,
  A ← DLIN_p, r ← ℤ_p², u ← ℤ_p³; the adversary also gets the group description.
- §4 opening, p. 18 / 22: the abstract class F_{λ,prmtr}, prmtr = (n, d, ℓ, size); for F^PHFE,
  X = Y = ℤ_p^{n(λ)} with p_λ the group order, **Z = G_{λ,T}**.
- **Definition 4.1 (Syntax of a PHFE scheme)**, p. 19 / 23: PPGen(1^λ, prmtr) → pp (given to all
  algorithms); Setup(pp) → (pk, msk); Enc(pk, (x, y)) → ct "along with the input x"; KeyGen(msk, f)
  → sk_f; Dec(sk_f, (x, ct)) deterministic → z ∈ Z or ⊥. Remarks 4.1 (secret key: pk empty, Enc
  takes msk), 4.2 (FE = PHFE with X = ∅).
- **Definition 4.2 (Correctness)**, p. 19 / 23: for all (x, y), f: Pr[Dec(sk_f, x, ct) ≠ f(x, y)]
  ≤ negl(λ) over PPGen, Setup, Enc, KeyGen.
- **Definition 4.3 (ε-simulation security)**, pp. 19–20 / 23–24: ∃ (possibly stateful) PPT
  simulator S = (Setup~, Enc~, KeyGen~) ∀ stateful PPT A = (A₁, A₂) ∃ negl ∀ λ ∀ prmtr:
  `|Pr[1 ← Real] − Pr[1 ← Ideal]| < negl(λ)`.
  - Real: `(x*, y*), (f_j)_{j∈[Q_sk]} ← A₁(1^λ)`; `pp ← PPGen`; `(pk, msk) ← Setup(pp)`;
    `(x*, ct*) ← Enc(pk, (x*, y*))`; `sk_{f_j} ← KeyGen(msk, f_j)`;
    `α ← A₂(pp, pk, (sk_{f_j})_j, x*, ct*)`.
  - Ideal: same commitment; `pp ← PPGen`; `(pk~, td) ← Setup~(pp)`,
    `ω ← Sample(x*, y*, (f_j)_j)`; `(x*, ct~*) ← Enc~(td, ω)`; `sk~_{f_j} ← KeyGen~(td, f_j, ω)`;
    `α ← A₂(pp, pk~, (sk~_{f_j})_j, x*, ct~*)`.
  - Sample outputs `ω = (x*, (f_j, f_j(x*, y*))_j)` with probability ε, else `(x*, y*, (f_j)_j)`.
  - Remark 4.3, p. 20 / 24: **ε = 1 is standard simulation security** (Sample always gives the
    values). Remark 4.5: ε = 1 with negl = 2^{−λ^{Ω(1)}} is subexponential security.
    **Remark 4.6: many-key = any polynomial Q_sk; one-key = Q_sk = 1; one-key by default.**
- Definition 4.4 (IND), p. 21 / 25; Definition 4.5 (IND-FH), p. 21 / 25: not used for PHFE.
- **Definition 4.6 (Linear efficiency)**, p. 22 / 26: ∃ poly ∀ λ, prmtr, (x, y), pp, (pk, msk):
  the circuit computing Enc(pk, ·) on (x, y) has size ≤ (|x| + |y|)·poly(λ).
- §8, pp. 42–57 / 46–61: GJLS21's own (arith-NC¹, deg 2) PHFE from **SXDH + bilateral DLIN**
  (Theorem 8.1, p. 46 / 50). **Not used** (journal pipeline: Wee20 replaces it, § 3(c)).
- **§9, "PHFE" ingredient**, pp. 57–58 / 61–62 (the requirement the iO chain places on PHFE):
  "a public-key PHFE for the class of functions F^PHFE defined with respect to bilinear groups of
  order p (which is the same as the modulus of ε-1LGFE) and is in fact the order of group G_λ.
  F^PHFE = {F^PHFE_{λ,n'}}_{λ,n'} for every polynomial n' consists of all functions f that takes an
  input of the form (x, y) ∈ ℤ_p^{n'} × ℤ_p^{n'}, and computes
  **f(x, y) = [Σ_{j,k} f_{j,k}(x)·y_j·y_k]_T ∈ G_T where f_{j,k} is a constant degree polynomial
  over x** (i.e. an arithmetic circuit in NC⁰) … The scheme PHFE satisfies the following
  properties: – (Security.) **1-simulation security for unbounded key queries.** – (Efficiency.)
  **Linear run-time as per Definition 4.6.** Such a scheme is constructed in Section 8 (in fact …
  arithmetic NC¹ on the public part)". The sPRG bullet: "sPRG ∈ (arith-NC⁰, deg 2). This sPRG is
  implementable by F^PHFE".
- Theorem 9.1, p. 58 / 62 (sublinearity uses PHFE's linear efficiency); **Theorem 9.2**, p. 60 / 64
  ("PHFE is many-key 1-simulation secure"); its proof, **Hybrid 1, p. 61 / 65**: the PHFE simulator
  is run as `Enc~(td, w)`, `KeyGen~(td, f_j, w)` with **w = (P, {f_i}_i, {v_i}_i), the v_i ∈ ℤ_p
  computed in the clear** by the hybrid.
- **Theorems 10.3 and 10.4**, pp. 63–64 / 67–68. Text before them (p. 63): "subsequent to the initial
  publication of our work, Wee [Wee20b] showed how to construct a PHFE scheme from only the
  Bilateral DLIN assumption. By using Wee's theorem in place of Theorem 8.1, we obtain:". Thm 10.3:
  Bilateral DLIN "(immediately implied by the DLIN assumption over symmetric bilinear groups)", LWE,
  an sPRG ⇒ (levelled) sublinearly efficient public-key FE for all circuits, subexponentially secure
  under subexponential assumptions. Thm 10.4: the subexponential versions ⇒ iO. [Wee20b] = TCC
  2020, LNCS 12550, pp. 210–228 (reference list, p. 72 / 76).

### [Wee20]
- Abstract and §1.1, p. 1: public-key PHFE, "NC¹ computation on public attributes and quadratic
  computation on the private message, with ciphertext size independent of the length of the public
  attribute"; selective, simulation-based security against unbounded collusions; footnote 1: "We
  actually achieve semi-adaptive security [9], a slight strengthening of selective security".
- §1.2, p. 2: "bilateral 1-Lin is false, for the same reason DDH is false in symmetric bilinear
  groups".
- §2, p. 4: arithmetic branching programs, F_{ABP,n,n'}; **§2.1, p. 4**: the generator G(1^λ) →
  (p, G₁, G₂, G_T, e), "G₁, G₂ and G_T are cyclic groups of order p, and e : G₁ × G₂ → G_T is a
  non-degenerate bilinear map" (G₁ ≠ G₂ is not required here, though the §1.2 overview, p. 2, says
  "We rely on an asymmetric bilinear group"); implicit notation [M]_s; **Assumption 1
  (MDDH^d_{k,ℓ})** with M ← ℤ_p^{ℓ×k} uniform, S ← ℤ_p^{k×d}; "Escala et al. [10] showed that
  k-Lin ⇒ MDDH¹_{k,k+1} ⇒ MDDH^d_{k,ℓ} ∀ k, d ≥ 1, ℓ > k with a tight security reduction. (In the
  setting where ℓ ≤ k, the MDDH^d_{k,ℓ} assumption holds unconditionally.)"; bilateral MDDH.
- **§2.2, p. 5 (PHFE)**: class (x, z) ↦ h(z)·f(x)^⊤, h fixed (h(z₁, z₂) = z₁ ⊗ z₂ for quadratic);
  syntax Setup/Enc/KeyGen/Dec, Dec outputs a value in ℤ_p; perfect correctness (probability 1);
  **Remark 1**: Dec recovers h(z)f(x)^⊤ in ℤ_p only for values bounded by B ("brute-force discrete
  log … from the exponent"); **security: semi-adaptive simulation** (mpk first, then (x*, z*), then
  adaptive KeyGen queries), "whenever A makes a query f to KeyGen, the simulator KeyGen* gets f
  along with h(z*)f(x*)^⊤".
- **§3, pp. 5–6**: the main scheme for `(x, (z₁, z₂)) ∈ ℤ_p^n × ℤ_p^{n'₁+n'₂} ↦ (z₁ ⊗ z₂) f(x)^⊤`,
  f ∈ F_{ABP,n,n'₁n'₂}. **Security claim (p. 6, unnumbered): "The scheme is SA-SIM-secure under the
  bilateral k-Lin assumption and the k'-Lin assumption in G₁, G₂ (for the most efficient concrete
  instantiation, we set k = 2, k' = 1). In our scheme, decryption actually computes
  [(z₁ ⊗ z₂) f(x)^⊤]_T, whereas the simulator only needs to get [(z₁ ⊗ z₂) f(x)^⊤]₂."** Building
  block: an SA-SIM PHFE (Setup₀, Enc₀, KeyGen₀, Dec₀) for (x, z) ↦ [zMf(x)^⊤]_T "parameterized by a
  matrix [M]₂ … where encryption gets [z]₁ and the simulator gets [zMf(x)^⊤]₂".
- **§3.1, p. 6**: Setup(p, 1^n, 1^{n'₁}, 1^{n'₂}) runs G ← G(p) (**the prime p is an input**),
  A₁ ← ℤ_p^{k×n'₁}, A₂ ← ℤ_p^{k'×n'₂}, M = (A₁ ⊗ I_{n'₂} ; I_{n'₁} ⊗ A₂), mpk = (G, [A₁]₁, [A₁]₂,
  [A₂]₂, mpk₀), msk = msk₀; Enc: y₁ = s₁A₁ + z₁, y₂ = s₂A₂ + z₂, ct₀ = Enc₀(mpk₀, x,
  [s₁ ⊗ z₂ ‖ y₁ ⊗ s₂]₁), ct = ([y₁]₁, [y₂]₂, ct₀); KeyGen = KeyGen₀; Dec =
  [(y₁ ⊗ y₂) f(x)^⊤]_T · Dec₀(sk_f, (f, [M]₂), ct₀, x)^{−1}. Correctness: identities (4), (5).
- **§3.2, p. 7**: simulator (Setup*, Enc*, KeyGen*(msk*, x*, f, [µ]₂)); Enc* draws y₁, y₂ (the
  simulator is stateful from Enc* to KeyGen*).
- **§3.3, pp. 7–8**: Games 0–4: Game 1 by security of the building block (the reduction picks the
  building block's semi-adaptive challenge `x*, s₁ ⊗ z*₂ ‖ (s₁A₁ + z*₁) ⊗ s₂`); Game 2 ≡ Game 1 by
  (5); Game 3 by bilateral k-Lin on A₁ ("holds even if z*₁ is adaptively chosen after seeing
  [A₁]₁, [A₁]₂"); Game 4 by k'-Lin in G₂ on A₂; Game 4 is the simulator.
- **§4, p. 8**: the building block Π, "simulation-based semi-adaptive security under k-Lin";
  "Most of the text in this section is copied verbatim from [2]". **§4.1, pp. 8–9: Lemma 1
  (partial garbling [2, 17, 23])**: (lgen, pgb, rec, pgb*); pgb(f, x, z; t) =
  (z − t̄ ‖ t(L₁(x^⊤ ⊗ I_m) + L₀)); reconstruction p·d^⊤ = z f(x)^⊤; privacy
  pgb(f, x, z; t) ≈_s pgb*(f, x, z f(x)^⊤; t). Stated, **not proved** in Wee20.
- **§4.2, pp. 9–10**: Π: Setup, Enc ([sA]₁, [z + sAW]₁, [sAU(x^⊤ ⊗ I_k) + sAV]₁), KeyGen(msk,
  (f, [M]₂)), Dec (6)–(8); correctness (9)–(11); simulator (Setup*, Enc*, KeyGen*), full rank of
  (A | c) with probability 1 − 1/p.
- **Appendix A, p. 12**: the concrete quadratic FE (f constant). Not needed.
- **Appendix B, pp. 12–14: Theorem 1** (security of Π): "For all A, there exist B₁ and B₂ with
  Time(B₁), Time(B₂) ≈ Time(A) such that Adv^Π_A(λ) ≤ Adv^{MDDH¹_{k,k+1}}_{B₁}(λ) +
  Adv^{MDDH^n_{k,mQ}}_{B₂}(λ) + 1/p", n the public-input length, m from the size of f, Q the number
  of keys. Games 0–5 (pp. 12–13); Lemma 2 (Game 0 ≈_c 1, MDDH¹_{k,k+1}, p. 13), Lemma 3 (Game 2 ≡ 3,
  p. 13, proof p. 14), Lemma 4 (Game 3 ≈_c 4, MDDH^n_{k,mQ}, p. 14), Lemma 5 (Game 4 ≈_s 5, partial
  garbling privacy, p. 14).

**Wee20 has no numbered theorem for its main PHFE.** Its security is the unnumbered claim of §3
(p. 6), proved in §3.3 (pp. 7–8), with the building block's security as Theorem 1 (Appendix B,
p. 12) and Lemma 1 (§4.1) as a cited black box. Cite them exactly so.

**Misprints in Wee20 to read through, not copy** (each recorded as a reading in the fidelity table):
- Lemma 1 (p. 8) swaps the shapes: L₀ ∈ ℤ_p^{t×mn}, L₁ ∈ ℤ_p^{t×m}. The formula needs
  L₁ ∈ ℤ_p^{t×mn}, L₀ ∈ ℤ_p^{t×m}, as §4.2's KeyGen states.
- §3.2 Enc* (p. 7) outputs [y₂]₁; Game 4 (p. 8) writes [s₂A₂ + z*₂]₁ and "y₂ ← ℤ_q". The group is
  G₂ (and ℤ_p), as in §3.1.
- §3.2 KeyGen* (p. 7) writes [(y₁ ⊗ y₂) f(x*)]_T · [µ]₂^{−1}. KeyGen₀* takes a G₂ element, so read
  [(y₁ ⊗ y₂) f(x*)^⊤]₂ · [µ]₂^{−1} (as Game 2, p. 7).
- §2.1 (p. 4), bilateral MDDH: "[MS]₁ … = 2" in the real branch. Read [MS]₂ and "= 1".
- In the symmetric instantiation the subscripts 1, 2 coincide, so only the G vs G_T reading of the
  KeyGen* item matters.

## 3. The chain, pinned

**(a) JLS26 → GJLS21. Verified (r1, re-read).** [JLS26, Thm 5.1, p. 21] = [GJLS21, Thms 10.3, 10.4,
pp. 63–64 (PDF 67–68)] at the 2025-01-03 revision: same three hypotheses (bilateral DLIN "implied
by" symmetric DLIN, LWE, an sPRG), same conclusions (FE; iO under subexponential security). JLS26's
footnote 3 (p. 5) about the update of [88] is consistent: this revision defines sPRGs (GJLS21
Defs 6.1–6.3, p. 28 ff.).

**(b) GJLS21 Thms 10.3/10.4 → the PHFE notion. Verified.** Thms 10.3/10.4 are Thms 10.1/10.2
with [Wee20b] in place of Thm 8.1 (p. 63). What they consume is the PHFE ingredient of §9
(pp. 57–58), used in Theorem 9.1 (efficiency) and Theorem 9.2 (security). That ingredient is:

| Item | GJLS21's requirement | Where |
|---|---|---|
| key setting | **public-key** | §9, p. 57; Def 4.1 (Remark 4.1 for the secret-key variant, not used) |
| syntax | PPGen(1^λ, prmtr) → pp; Setup(pp); Enc(pk, (x, y)) with x public; KeyGen(msk, f); deterministic Dec | **Def 4.1**, p. 19 |
| function class | F^PHFE_{λ,n'}: (x, y) ∈ ℤ_p^{n'} × ℤ_p^{n'} ↦ [Σ_{j,k} f_{j,k}(x)·y_j·y_k]_T ∈ G_T, each f_{j,k} a constant-degree polynomial in x (arithmetic NC⁰); p the order of G_λ | §9, pp. 57–58; §4 opening, p. 18 |
| match with JLS26 Def 3.3 "(deg d, deg 2)" | each sPRG output Q_I(Process_I(P), S) has degree ≤ d in P and degree ≤ 2 in S, so it is Σ_{j,k} f_{j,k}(P)·ŷ_j·ŷ_k on ŷ = (S, 1) with deg f_{j,k} ≤ d. One output is one key. GJLS21 itself pads y with secret values whose terms are linear (Fig. 8, p. 59: ⟨msk', pp_{C_i}⟩ is degree 1 in y) | JLS26 Def 3.3, p. 10; GJLS21 §9 sPRG bullet, p. 58 |
| correctness | Pr[Dec ≠ f(x, y)] ≤ negl, with f's value in **G_T** ("in the exponent") | **Def 4.2**, p. 19; §9 |
| security | **1-simulation security (Def 4.3 with ε = 1, Remark 4.3) for unbounded key queries (many-key, Remark 4.6)**: one challenge ciphertext; the adversary commits to (x*, y*) **and all Q_sk functions** before pp is generated (very selective, non-adaptive keys); universal stateful simulator; the simulator gets x* and (f_j, f_j(x*, y*))_j | **Def 4.3**, pp. 19–20; §9, p. 58 |
| compactness | **linear efficiency, Def 4.6**: Enc(pk, ·) has circuit size ≤ (\|x\| + \|y\|)·poly(λ) | **Def 4.6**, p. 22; §9, p. 58; used by Thm 9.1 |
| group setting | a sequence of asymmetric prime-order groups, one per λ, order p_λ = 2^{λ^{Θ(1)}}, the same p as the 1LGFE and sPRG modulus; bilateral DLIN (Def 3.3). JLS26/GJLS21 adapt this to DLIN on symmetric groups (Thm 10.3's parenthetical; JLS26 Thm 5.1, §1.4) | §3, p. 17; Def 3.3, p. 18; §9, p. 57 |
| subexponential form | negl = 2^{−λ^{Ω(1)}} | Remark 4.5, p. 20 |

**The PHFE definition is therefore [GJLS21, Definition 4.3]** (at ε = 1, many-key), for the class
F^PHFE of [GJLS21, §9], with syntax Def 4.1, correctness Def 4.2 and efficiency Def 4.6.

**(c) Wee20 → that notion. Verified, with four gaps (all bridged; one needs a ruling).** Wee20's
result (§3, p. 6; §3.3; Theorem 1): public-key PHFE for (x, (z₁, z₂)) ↦ (z₁ ⊗ z₂) f(x)^⊤ with f an
ABP, **semi-adaptive simulation security** with unbounded keys, from bilateral k-Lin and k'-Lin.
With k = k' = 2 on a symmetric group:

| # | Item | Wee20 | GJLS21 needs | Bridge | Where proved |
|---|---|---|---|---|---|
| G1 | group setting and assumption | asymmetric G₁, G₂ (§2.1 allows G₁ = G₂); bilateral k-Lin and k'-Lin; MDDH (uniform matrices) in Thm 1 | symmetric DLIN (JLS26) | (i) a symmetric group is an instance of Wee20's formal §2.1 generator (G₁ = G₂ = G, g₁ = g₂ = g; only the §1.2 overview says "asymmetric"), and every hop of §3.3 and App. B is a reduction using elements of one group plus exponents it samples, so the scheme and proofs apply verbatim (maintainer's static check; the job re-checks); bilateral 2-Lin is then 2-Lin in G. (ii) k' = 1 (SXDH) is unavailable, so k = k' = 2 (Wee20 p. 2). (iii) GJLS21 Def 3.3's DLIN_p matrix in G₁ = G₂ is JLS26 §1.1's tuple. (iv) Wee20's k-Lin is uniform-matrix MDDH; DLIN ⇒ MDDH^d_{2,ℓ} (random self-reducibility) | (i)–(iii): GJLS21 Thm 10.3 parenthetical (p. 63) and JLS26 Thm 5.1 (p. 21), §1.4 (pp. 7–8); (iv): [EHKRV13] via [Wee20, §2.1, p. 4]. **Proved in the job** (DLIN ⇒ MDDH reduction) |
| G2 | function class | f ∈ F_ABP (NC¹ ⊇ constant degree), two private vectors z₁, z₂ | Σ_{j,k} f_{j,k}(x) y_j y_k with constant-degree f_{j,k}, one private vector y | encrypt (x, (y, y)) and give the key for the vector f(x) = (f_{j,k}(x))_{(j,k)}: (y ⊗ y) f(x)^⊤ = Σ_{j,k} f_{j,k}(x) y_j y_k. The job restricts Wee20's class to vectors of degree-≤ d polynomials (no ABP model), which still contains the image | GJLS21 §9, p. 58 ("in fact … larger class") and p. 5. **Proved in the job** (an identity plus a wrapper scheme) |
| G3 | adaptivity | semi-adaptive: challenge after mpk, keys adaptive after ct* | very selective: challenge and all keys committed before pp | the GJLS21 game is a special case: an (A₁, A₂) adversary is a semi-adaptive one that ignores mpk, commits, then asks its pre-chosen keys; the GJLS21 simulator is Wee20's (Setup~ = Setup*, Enc~ = Enc*(·, x*), KeyGen~(td, f_j, ω) = KeyGen*(·, x*, f_j, value)). No loss | immediate; the job proves the GJLS21 form directly (design-r2 § 5) |
| G4 | **the simulator's input** | KeyGen* needs **[µ]₂ = g^µ** (§3, p. 6; §3.2); Wee20's own definition gives µ ∈ ℤ_p (§2.2, p. 5) | literally f_j(x*, y*) ∈ **G_T** (Def 4.3 with Z = G_T, §4 p. 18, §9 p. 57), which is computationally **less** than g^µ | from µ ∈ ℤ_p the simulator computes g^µ, so Wee20 gives Def 4.3 **when the simulator is handed the values in ℤ_p**. That is exactly how GJLS21 uses it: Thm 9.2, Hybrid 1 (p. 61) runs the PHFE simulator on w = (P, {f_i}, {v_i}) with the v_i ∈ ℤ_p in the clear. **The literal G_T reading is not proved by Wee20 nor anywhere in the staged sources** (passing from [µ]_T to [µ]₂ is pairing inversion) | **ruling needed: design-r2 Q1** (recommended: values in ℤ_p) |
| G5 | correctness | perfect, Dec = [µ]_T (§3, p. 6; (9)–(11)); ℤ_p only for bounded values (Remark 1) | Def 4.2 (error ≤ negl), value in G_T | perfect ⇒ Def 4.2 with negl = 0; in the exponent matches F^PHFE's G_T output | immediate |
| G6 | efficiency | ct grows with z only (p. 1, §3); \|ct\| = (n'₁ + n'₂) + (k+1) + (k'n'₁ + kn'₂) + k group elements, plus x | Def 4.6 linear efficiency | Enc's work is linear in \|x\| + \|y\| (the only x-dependent term is [sAU(x^⊤ ⊗ I_k)]₁) | Phase A: written as a statement; proved in Phase B |
| G7 | partial garbling | Lemma 1 cited from [AGW20, IW14, Wee17], not proved | (used inside Π) | must be built for the degree-≤ d class | **source not staged: design-r2 Q2** |
| G8 | the prime | Setup(p, …) runs G(p) (§3.1): p is an input; §4.2 runs G(1^λ) | one p per λ, the group order, shared with the sPRG and 1LGFE (§9; JLS26 Thm 5.1) | fixed prime schedule p(κ) (ruling Q-S2); Π shares the outer scheme's group (as GJLS21 Def 4.1: pp is given to all algorithms) | ruling Q-S2; docstring deviation |

## 4. Citations for the Lean docstrings

Every location below is checked in the staged PDFs; the job re-checks before citing.
- `[JLS26, §1.1]` (DLIN, p. 3); `[JLS26, §1.4]` (PHFE from DLIN, pp. 7–8); `[JLS26, Definition 2.1]`
  and `[JLS26, Remark 2.1]` (subexponential, pp. 8–9); `[JLS26, Definition 3.3]` (p. 10);
  `[JLS26, Theorem 5.1]` (p. 21).
- `[GJLS21, §3]` (groups, DLIN_p; p. 17); `[GJLS21, Definition 3.3]` (bilateral DLIN, p. 18);
  `[GJLS21, Definitions 4.1, 4.2, 4.3]` (pp. 19–20) and `Remarks 4.3, 4.5, 4.6` (p. 20);
  `[GJLS21, Definition 4.6]` (p. 22); `[GJLS21, §9]` (the PHFE ingredient and F^PHFE, pp. 57–58);
  `[GJLS21, Theorem 9.2]` and its Hybrid 1 (pp. 60–61); `[GJLS21, Theorems 10.3, 10.4]`
  (pp. 63–64). Page numbers are the printed ones.
- `[Wee20, §2.1]` (groups, MDDH, the Escala et al. implication; p. 4); `[Wee20, §2.2]` (PHFE,
  Remark 1, SA-SIM; p. 5); `[Wee20, §3]` (the scheme's security claim, p. 6), `[Wee20, §3.1]`,
  `[Wee20, §3.2]`, `[Wee20, §3.3]` (pp. 6–8); `[Wee20, Lemma 1]` (§4.1, p. 8); `[Wee20, §4.2]`
  (pp. 9–10); `[Wee20, Theorem 1]` and `[Wee20, Lemmas 2–5]` (Appendix B, pp. 12–14).
- `[EHKRV13]`, `[AGW20]`, `[IW14]`: only as "cited in [Wee20, …]" until staged.
- Library precedents: `[BB04]` and `[PS10]` as in `Pairing/*` and `IdentityBased/*`.

Policy §2 ingest: as pairing Q12(A), the PDFs stay uncommitted, staged on the exchange only. The
job adds nothing under `blueprint/`.
