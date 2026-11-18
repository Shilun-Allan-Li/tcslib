# io-phfe design r2: degree-2 PHFE from DLIN [Wee20], the notion of [GJLS21, Definition 4.3], Phase A

The design note behind `dispatch-prompt-r2.md`. Prepared 2026-11-18 at records tip
`1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae`, from static reading of the three staged PDFs
(`sources-r2.md`) and the code (no Lean run). It replaces `design-r1.md`, which is kept for the
record. Every Lean shape below is **proposed: Codex may refine it, with disclosure in `REPORT.md`**.
Seyoon's rulings on § 7 override this note. The maintainer records them in `rulings.md` beside it.

## 0. Binding rulings applied (decision log, 2026-11-18)

| Ruling | Effect on the design (r1 → r2) |
|---|---|
| **Journal pipeline** | Symmetric prime-order groups with DLIN; public-key PHFE from DLIN via [Wee20]; the notion [JLS26, Thm 5.1] consumes via [GJLS21, Thms 10.3, 10.4]. **Now pinned** (sources-r2 § 3): [GJLS21, Definition 4.3] at ε = 1, many-key, for the class F^PHFE of [GJLS21, §9], with Defs 4.1, 4.2, 4.6. |
| **Generic FE as a goal** | Generic syntax over a function class; correctness and security as separate predicates; PHFE an instance. Where generality and fidelity to Def 4.3 conflict, fidelity wins (§ 4.5). |
| **Fixed prime schedule p(κ) (Q-S2)** | Overrides r1 Q9. The headlines assume `hp : ∀ κ r, (G.inst κ r).order = p κ`. |
| **p as an input** | Honest algorithms and the simulator read the modulus from the public parameters (the drawn group's order; at string level `G.Ops.orderStr`). They never compute p, and the scheme's definition never mentions `p`. Statements hold for every prime schedule. |
| **Subexponential security** (`Foundations/Subexponential`, PR #374, `cbce64d1`) | Core theorems are explicit advantage inequalities with explicit slack. Negligible and subexponential corollaries are derived (`SubexpSmall`, `SubexpHard`, `.negligible`, `.add`, `.const_mul`, `.mul_pow`, `.comp_of_rpow_le`). |
| **Two phases** | This dispatch is **Phase A**. Honest algorithms, simulator and reductions are explicit Lean functions; a reduction is a function of (input, advice, coins). Correctness is proved. Security is proved as explicit inequalities **for any NUPPT that realises each reduction function**. Efficiency statements are written (as named `Prop`s), not proved. **r1's machines (milestone M4, `PolyHandler` constructions) are dropped.** No RAM interface appears. |
| **Uniformity (binding)** | Written efficiency statements use `PolyTimeComputable` or `∃ A, A.Uniform ∧ A.Computes f` (or a uniform time-bounded `FinTM` form for Def 4.6), never a bare `∃ A : NUPPT, A.Computes f`. There is one program for all κ, ℓ, n, with no per-κ constants. Advice appears only in reductions and adversaries. |
| **Sampling** | Honest algorithms, the simulator and games draw exact laws (`ProbComp.sample`). **Reduction functions never sample**: their own randomness is averaged out and fixed as typed advice ω* (the non-uniform hardwiring route of the sPRG pack, design-r2 § 4.8 there), so no coin decoder and no draw slack appear. **The job builds no sampler bridge.** |
| **Lean processes** | At most one Lean process for this job on Seyoon's machine. |

Unchanged conventions (pairing precedent):
- g uniform in G* (pairing Q2; r1 Q8);
- typed honest algorithms and a typed universal simulator (pairing Q5; r1 Q12);
- the adversary: **departed from** pairing Q7's one-machine-with-oracles shape, because the source
  and the shared realiser force it (§ 4.5): Def 4.3's adversary is a two-stage pair (A₁, A₂);
- the two-experiment advantage (pairing Q9);
- encodings injective on reachable objects (G40-01);
- PDFs not committed (pairing Q12).

## 1. The chain and the target

### 1.1 Pinned (details and pages: `sources-r2.md` § 3)
- [JLS26, Thm 5.1, p. 21] = [GJLS21, Thms 10.3, 10.4, pp. 63–64], which put [Wee20b] in place of
  GJLS21's Theorem 8.1. Their PHFE requirement is the §9 ingredient (pp. 57–58).
- **Target notion T.**
  - Syntax: [GJLS21, Definition 4.1], public-key.
  - Correctness: [GJLS21, Definition 4.2]; the value is in G_T.
  - Security: **[GJLS21, Definition 4.3] with ε = 1 (Remark 4.3), many-key (Remark 4.6)**. The
    adversary commits to (x*, y*) and Q_sk functions before pp; it gets pp, pk, the Q_sk keys and the
    challenge ciphertext; the simulator is universal and stateful.
  - Efficiency: [GJLS21, Definition 4.6], linear efficiency.
  - Class: **F^PHFE of [GJLS21, §9]**: (x, y) ∈ ℤ_p^{n'} × ℤ_p^{n'} ↦ [Σ_{j,k} f_{j,k}(x)·y_j·y_k]_T,
    each f_{j,k} a constant-degree polynomial, p the group order.
  - Setting: one prime p per κ, symmetric groups, DLIN.
- **Wee20's result:**
  - an unnumbered claim in [Wee20, §3, p. 6], proved in §3.3, with [Wee20, Theorem 1] (App. B) for
    the building block and [Wee20, Lemma 1] for partial garbling;
  - semi-adaptive simulation security with unbounded keys, for (x, (z₁, z₂)) ↦ (z₁ ⊗ z₂)·f(x)^⊤,
    f an ABP, from bilateral k-Lin and k'-Lin.

### 1.2 Gaps and bridges (sources-r2 § 3(c), rows G1–G8)
- **G1. Symmetric DLIN, k = k' = 2.** Wee20 runs verbatim on a symmetric group (its §2.1 does not ask
  G₁ ≠ G₂). Cite [GJLS21, Thm 10.3] ("immediately implied by the DLIN assumption over symmetric
  bilinear groups") and [JLS26, Thm 5.1, §1.4]. The job proves DLIN ⇒ uniform-matrix MDDH^d_{2,ℓ}
  ([EHKRV13] via [Wee20, §2.1]). Every assumption Wee20 uses (Thm 1's MDDH¹_{2,3} and
  MDDH^ℓ_{2,mQ}; §3.3's bilateral 2-Lin on A₁ and 2-Lin on A₂) is an instance.
  - **Check done statically:** no step of Wee20's proofs uses asymmetry. Each reduction uses only
    group elements it receives in the one group, plus exponents it chooses (hardwired as advice).
  - Codex re-checks each step and escalates E-SRC if one fails.
- **G2. Class.** F^PHFE embeds in Wee20's class by z₁ = z₂ = y and f(x) = (f_{j,k}(x))_{(j,k)}. The
  job restricts Wee20's f to vectors of degree-≤ d polynomials, so no ABP model is needed.
- **G3. Adaptivity.** Def 4.3 is a special case of semi-adaptive security with no loss. The job
  proves the Def 4.3 form directly (§ 5).
- **G4. The simulator's input.** Wee20's simulator needs g^µ; Def 4.3 read literally gives
  e(g, g)^µ. Bridged by handing the simulator µ ∈ ℤ_p, as GJLS21's own Thm 9.2 (Hybrid 1, p. 61)
  does. **This needs a ruling: Q1.**
- **G5. Correctness.** Perfect correctness ⇒ Def 4.2.
- **G6. Efficiency.** Linear efficiency is written in Phase A and proved in Phase B.
- **G7. Partial garbling.** [Wee20, Lemma 1] is cited, not proved, and its sources are not staged.
  **This needs a ruling: Q2.**
- **G8. The prime.** Fixed schedule; Π shares the outer group (GJLS21 Def 4.1's pp).

## 2. The deliverable (Phase A)

1. **DLIN** [JLS26, §1.1] = [GJLS21, Def 3.3] in G₁ = G₂ (asymptotic, NUPPT distinguishers), with its
   matrix form; **uniform-matrix MDDH^d_{2,ℓ}**; and the reduction DLIN ⇒ MDDH^d_{2,ℓ} as a function
   with an explicit inequality.
2. **Generic FE** (syntax, `Correct`, `CorrectExcept` = Def 4.2, simulator, the Def 4.3 game,
   `SimSecure`) and **reduction functions with realisers** (§ 4.4).
3. **Classes:**
   - `phfeClass`, the GJLS21 §9 class;
   - `quadClass`, Wee20's §3 class restricted to polynomial vectors;
   - the embedding between them.
4. **Partial garbling** (Wee20 Lemma 1) as an interface, plus an instance for degree-≤ d polynomial
   vectors (Q2).
5. **Π** [Wee20, §4.2] and the **quadratic scheme** [Wee20, §3.1] at k = k' = 2 on a symmetric
   group; the **PHFE** `wee20PHFE` for `phfeClass` (§ 4.9).
6. **Headlines:**
   - perfect correctness and Def 4.2;
   - the security inequality (Def 4.3 shape, explicit slack, one realiser per reduction);
   - the negligible and subexponential corollaries, conditional on realisers existing;
   - the ciphertext width;
   - efficiency statements as named `Prop`s.

Phase B (not this job): word-RAM programs for the algorithms and reduction functions; the RAM ⇒
`PolyTimeComputable`/NUPPT bridge (`ram-bridge-assessment.md`); proofs of the efficiency `Prop`s;
realisers for every reduction function; and the unconditional corollaries.

## 3. Module layout (proposed)

New files only. Every file is at most 1000 lines; target 150–600 (policy §1).
**`Pairing/Assumptions.lean` is not touched**: cleanup S2-A step A05 edits it.

| File (new) | Contents | Est. lines |
|---|---|---|
| `TCSlib/Cryptography/Pairing/Exponents.lean` | `[v]`, `[M]` (vectors and matrices of group elements), algebra, pairing of vectors to `e(g,g)^{a·b}`, Kronecker forms | 300–500 |
| `TCSlib/Cryptography/Pairing/Linear.lean` | `dlinStr`, `dlinGame`, `dlinAdv`, `DLINAssumption`, `SubexpDLIN`, readers; the matrix form | 300–500 |
| `TCSlib/Cryptography/Pairing/MatrixDH.lean` (+ `MatrixDH/SelfReduction.lean`) | uniform-matrix `mddhGame d ℓ`, `mddhAdv`; the reduction function `dlinToMddh` and `mddhAdv_le` (DLIN ⇒ MDDH, explicit slack) | 800–1,500 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption.lean` | facade | 40 |
| `…/FunctionalEncryption/Defs.lean` | `FnClass`, `FEScheme`, `honestRun`, `Correct`, `CorrectExcept`, `Simulator`, `simGame`, `simAdv`, `SimSecure`, `SubexpSimSecure` | 500–900 |
| `…/FunctionalEncryption/Realization.lean` (only if Q5 is not (A) at `<BASE>`) | `NUPPT.RealizesOn` and readers, the same declarations as the shared file, for a mechanical move later | 0–150 |
| `…/FunctionalEncryption/Classes.lean` | `phfeClass` (GJLS21 §9), `quadClass` (Wee20 §3, polynomial vectors), `embed` lemma, `pad_one` reader (JLS26 Def 3.3 outputs) | 300–600 |
| `…/FunctionalEncryption/PartialGarbling.lean` (+ `PartialGarbling/Poly.lean`) | interface (Wee20 Lemma 1) + instance (Q2) | 150–250 + 1,200–2,500 |
| `…/FunctionalEncryption/Wee20/Linear.lean`, `LinearCorrect.lean`, `LinearSecurity/*.lean` | Π (§4.2), correctness (9)–(11), simulator, Games 0–5 typed, reduction functions, Theorem 1 inequality | 2,000–3,700 |
| `…/FunctionalEncryption/Wee20/Quadratic.lean`, `QuadraticCorrect.lean`, `QuadraticSecurity/*.lean` | §3.1 scheme, (4)–(5), §3.2 simulator, §3.3 Games 0–4 typed, reduction functions | 1,300–2,300 |
| `…/FunctionalEncryption/Wee20.lean` | `wee20PHFE` (the GJLS21 class), headlines, corollaries, ct width, efficiency `Prop`s | 400–800 |

**Existing files touched** (r1 Q7(A), pairing precedent): `TCSlib/Cryptography/Pairing.lean` and
`TCSlib/Cryptography/AdvancedEncryption.lean`. In each, only import lines, `## Contents` bullets and
`## References` tags change. `TCSlib.lean` already imports both facades.

**Namespaces:**
- `TCSlib.Cryptography.Pairing` (`BilinearGen.DLINAssumption`, `BilinearGen.mddhAdv`, exponent
  helpers under `BilinearGroup`);
- `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption`;
- `…FunctionalEncryption.Wee20`, with inner `Linear` and `Quadratic`.

## 4. Statement shapes (proposed; Codex may refine with disclosure)

### 4.1 DLIN [JLS26, §1.1] = [GJLS21, Def 3.3] on G₁ = G₂
As r1 § 4.1: `dlinStr`, `dlinGame D real κ`, `dlinAdv D κ := advantage …`,
`DLINAssumption := ∀ D : NUPPT, Negligible (G.dlinAdv D)`. New:
`SubexpDLIN := SubexpHard G.dlinAdv` (`Foundations/Subexponential`, `α := NUPPT`).

Docstrings record:
- the JLS26 tuple order;
- that GJLS21 Def 3.3's `{[A]_s, [Ar]_s}_{s=1,2}` with A ← DLIN_p becomes one copy of this tuple in
  G₁ = G₂ ([GJLS21, Thm 10.3]'s parenthetical);
- g uniform in G* (no stronger than the canonical-g form, by re-randomisation; prose only);
- the generator is given to D through the description, as `dbdhGame`.

### 4.2 MDDH and the self-reduction (`Pairing/MatrixDH*.lean`) [Wee20, §2.1, Assumption 1]
- `mddhGame (d ℓ : PolyExpr) D real κ`: g ← G*; M ← ℤ_p^{ℓ×2} uniform; real gives
  `[M], [M S]` with S ← ℤ_p^{2×d}; random gives `[M], [U]` with U ← ℤ_p^{ℓ×d}.
  - `mddhAdv`, readers.
  - Wee20's orientation (row vectors, sA) is a transpose; the docstring maps it.
- **The reduction** `dlinToMddh G d ℓ D ω` (§ 4.4: pre-processing then D) and
  ```lean
  theorem mddhAdv_le (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
      (D : NUPPT) :
      ∃ ω : ∀ κ, MddhAdvice p d ℓ κ, ∀ B : NUPPT,
        B.RealizesOn G.dlinEnc D.coins (dlinToMddh G hp d ℓ D ω) →
        ∀ κ, G.mddhAdv d ℓ D κ ≤ G.dlinAdv B κ + mddhSlack G d ℓ κ
  ```
  - Route: [EHKRV13] random self-reducibility, cited via [Wee20, §2.1]. Re-randomise the 3×2 DLIN
    matrix into a uniform ℓ×2 one; spread one challenge column into d columns.
  - `mddhSlack` is explicit: (rank-deficiency terms)/p, with p the drawn order. There is no draw
    term, because the re-randomisation matrices are hardwired in ω (averaging:
    `exists_expect_sample_le`, `abs_expect_sub_le_expect`).
  - With `hp` and 2^κ ≤ p κ it is `SubexpSmall c` for every c < 1.
  - The case ℓ ≤ 2 (unconditional, Wee20 §2.1) is a statistical lemma, with no D.
  - If the tight route proves too long, a column-hybrid with a non-uniform index is the fallback.
    It is then a sum of DLIN advantages over d realisers; disclose it.

### 4.3 Exponent vectors (`Pairing/Exponents.lean`)
As r1 § 4.2: `expVec`, `expMat`, `expVec_add`, `expVec_smul`, `expMat_mulVec`, `pair_expVec`, plus
Kronecker forms for `[y₁ ⊗ y₂]` from `[y₁]` and y₂ (Wee20 §3.3 Games 3, 4). Built on `pow_val_add`,
`pow_val_mul`, `bilinear_pow`, Mathlib `dotProduct`/`mulVec`/`kroneckerMap`.

### 4.4 Reduction functions and realisers (Phase A; the interface Phase B must meet)
The same shape as the sPRG pack r2 (§ 4.8 there), so that both jobs share one predicate:
```lean
/-- `B` realises the reduction function `R` on the encoded challenges `enc`, with coin
polynomial `c` (shared file `Asymptotic/Realization.lean`, sPRG Q-S9 = this pack's Q5). -/
def Complexity.NUPPT.RealizesOn (B : NUPPT) {X : ℕ → Type} (enc : ∀ m, X m → List Bool)
    (c : PolyExpr) (R : ∀ m, X m → List Bool → List Bool) : Prop :=
  B.coins = c ∧ ∀ m (x : X m) (r : List Bool), B.runAtL m (enc m x) r = R m x r
```
Every PHFE reduction function has this form:
```lean
def XRed (A : TwoStage) (ω : ∀ κ, XAdvice κ) (κ : ℕ) (x : XChal κ) (r : List Bool) :
    List Bool :=
  A.A₂.runAtL κ (XPre κ (ω κ) x) (r.take (A.A₂.coinLen κ))
```
This is exactly the sPRG shape with φ = id and post := id, i.e. the conclusion shape of
`NUPPT.exists_reparam_pre_post`. **PHFE needs nothing different**, for two reasons:
- Def 4.3's A₁ runs on 1^κ alone, so its output (commitment and state) does not depend on the
  challenge. It is fixed in ω* by averaging over A₁'s coins, with the reduction's own choices.
- What is left is **one** activation of A₂ on a pre-processed view.
- **Challenge.** `XChal κ` is the assumption's typed challenge (the DLIN tuple, or the MDDH
  matrices) and `enc` is exactly the string the assumption's game hands its distinguisher.
- **Advice.** `XAdvice κ` is a finite type, inhabited at every κ, with an explicit encoding and
  `PolyExpr` length. It holds the reduction's own choices: the matrices and exponents Wee20's
  reductions sample (A₁, A₂, W, U, V, s's, T_j, R_j, the partial-garbling coins…) and A₁'s output
  (commitment and state). ω* is chosen by averaging (`exists_expect_sample_le`,
  `abs_expect_sub_le_expect`), so **reductions never sample**.
- **Advice types need the fixed schedule.** The advice holds exponents in `ZMod (p κ)`. They are
  fixed before the challenge's group is drawn, so the reduction lemmas take `hp`, and `XPre` casts
  them into the drawn group's `ZMod` through `hp`. This is one more reason for Q-S2.
- **Pre-processing.** `XPre` is the deterministic pre-processing into A₂'s input, i.e. A₁'s state
  with the view of § 4.5. It is typed in `ZMod` and the group, then encoded.
- **Statement form** (as sPRG `prop41`): **∃ advice ω* such that EVERY NUPPT realising the
  reductions at ω* satisfies, at every κ, the explicit inequality.**
- **Transfer.** One lemma per assumption: for B realising R, `dlinAdv B κ` equals the typed
  advantage of `R κ` on the challenge law (`NUPPT.distinguisherL_eq`, `runAt_eq`). Hops are proved
  on the typed side.
- **Home: Q5**, recommended in house, shared with the sPRG job.
- **Not proposed for PHFE in Phase A:** the sPRG pack's Q-S11 (prove "targets ⇒ realisers" now via
  `NUPPT.exists_reparam_pre_post`). PHFE's pre-processing needs group words on encodings, which is
  Phase B work.

### 4.5 Generic FE (`FunctionalEncryption/Defs.lean`)
**`FnClass` and `FEScheme`** are as r1 § 4.3, with these changes:
- **No leakage map.** `FnClass` has `pubLen`, `privLen`, `fnLen` (messages are pairs (x, y); x is
  public, as GJLS21 Def 4.1; FE is `pubLen = 0`, Remark 4.2), plus `Prm`, `Out` and `eval`.
- **The modulus.** `cprm pp` is the drawn group's order: the algorithms read p from pp.
- **`DecOut`/`embed`** stay (G_T, `e(g,g)^{v.val}`), for correctness in the exponent.

**Correctness:**
- `Correct`: perfect, `AllOutputs` as r1.
- `CorrectExcept (ε : ℕ → ℝ)`: [GJLS21, Def 4.2] with explicit error.
- `Correct.correctExcept_zero`.

**Simulator** ([GJLS21, Def 4.3], stateful):
```lean
structure Simulator where
  St : ℕ → Type
  setup : (κ : ℕ) → (pp : S.Pub κ) → ProbComp (S.MPK κ × St κ)     -- Setup~(pp) → (pk~, td)
  enc   : (κ : ℕ) → (pp : S.Pub κ) → St κ → Ω κ pp → ProbComp (S.CT κ × St κ)
  key   : (κ : ℕ) → (pp : S.Pub κ) → St κ → Ω κ pp → (j : ℕ) → ProbComp (S.SK κ × St κ)
```
- `Ω κ pp` is ω = (x*, (f_j, µ_j)_{j<q}). The form of µ_j is Q1; recommended:
  `µ_j : C.Out κ (S.cprm κ pp)`, i.e. ℤ_p.
- `key` takes the index j, which is a reindexing of KeyGen~(td, f_j, ω). The deviation is recorded.
- The simulator is typed and universal (∃ Sim before ∀ A). Its efficiency is a named `Prop`, as for
  honest algorithms.

**The adversary** is `TwoStage := (A₁ A₂ : NUPPT)`, GJLS21's stateful A = (A₁, A₂), with
independent coins.

**The game `simGame Sim A q ideal κ`** ([GJLS21, Def 4.3]):
- `c ← A₁.runAt κ []`.
- **Commitment.** c is decoded (fixed width, total decoding mod the drawn p) as
  (x*, y*, f_1, …, f_{q(κ)}) and a state string st.
- pp ← pubGen (generator coins; g ← G*).
- real: (pk, msk) ← setup; ct ← enc pk (x*, y*); sk_j ← keyGen msk f_j.
- ideal: Sim.setup, Sim.enc and Sim.key on ω, with µ_j = eval f_j (x*, y*).
- `α ← A₂.runAt κ ⟨st, ⟨encPub pp, encMPK pk, encSK sk_1, …, encSK sk_q, x*, encCT ct⟩⟩`.
- **Why this shape.**
  - It is Def 4.3 line by line. A₁ sees nothing of pp. A₁ needs no `Pub` oracle: by Q-S2 the
    modulus is p κ for every coin string, so A₁ can encode messages without seeing the group (r1's
    `Pub` oracle is dropped).
  - The experiment is non-interactive, so no oracle is needed.
  - It yields single-activation reductions (§ 4.4).
  - Pairing Q7's oracle shape was for adaptive key queries, which Def 4.3 does not have.
- **Decoding.** Residues are decoded mod the drawn order. Under `hp` this equals decoding mod
  p(κ), and a reader says so.

**The predicates:**
```lean
noncomputable def simAdv (Sim) (A : TwoStage) (q : PolyExpr) (κ : ℕ) : ℝ :=
  advantage (S.simGame Sim A q false κ) (S.simGame Sim A q true κ)
/-- [GJLS21, Definition 4.3] with ε = 1 (Remark 4.3), many-key (Remark 4.6). -/
def SimSecure : Prop := ∃ Sim, ∀ (A : TwoStage) (q : PolyExpr), Negligible (S.simAdv Sim A q)
/-- [GJLS21, Remark 4.5]: subexponential simulation security. -/
def SubexpSimSecure : Prop :=
  ∃ Sim, SubexpHard fun (Aq : TwoStage × PolyExpr) => S.simAdv Sim Aq.1 Aq.2
```
- One-key is `q = 1`.
- IND (Def 4.4), ε < 1 (Def 4.3's Sample coin), adaptive, many ciphertexts, secret key: documented
  extensions (§ 9).

### 4.6 Classes (`FunctionalEncryption/Classes.lean`)
**`phfeClass ℓ n d`** ([GJLS21, §9, pp. 57–58]):
- x ∈ ℤ_p^ℓ, y ∈ ℤ_p^n (residues as `G.wG`-bit numerals);
- a function is a tensor c_{j,k,t}, j, k < n, over monomial tuples t : Fin d → Fin (ℓ+1) on
  x̂ = (x, 1);
- eval: Σ_{j,k} (Σ_t c_{j,k,t} ∏_i x̂_{t i})·y_j·y_k.

Deviations:
- separate lengths ℓ, n (GJLS21's n' for both is the instance ℓ = n);
- tuples, not monomials;
- d is a parameter for "constant degree".

**`pad_one` reader** (JLS26 Def 3.3 → F^PHFE): every polynomial of degree ≤ d in x and ≤ 2 in y
equals a `phfeClass` function at (x, (y, 1)). This is GJLS21 §9's "implementable by F^PHFE".

**`quadClass ℓ n₁ n₂ d`** ([Wee20, §3], restricted):
- (x, (z₁, z₂)) ↦ (z₁ ⊗ z₂)·f(x)^⊤;
- f a vector of n₁n₂ polynomials of degree ≤ d, as tensors;
- deviation: polynomial vectors instead of ABPs, a subclass of F_ABP (constant d).

**`phfeClass_eval_eq_quad`**: eval c (x, y) = quad-eval (vec c) (x, (y, y)). The identity uses
Mathlib `kroneckerMap` ordering.

### 4.7 Partial garbling (`PartialGarbling.lean`) [Wee20, Lemma 1, §4.1]
```lean
structure PartialGarbling (ℓ n' d : …) where   -- for z·f(x)^⊤, f ∈ quad-type polynomial vectors
  m t : Fn → ℕ
  L₁ : (f : Fn) → Matrix (Fin (t f)) (Fin (m f * ℓ)) (ZMod q)   -- read with the corrected shapes
  L₀ : (f : Fn) → Matrix (Fin (t f)) (Fin (m f)) (ZMod q)
  rec : (f : Fn) → (x : Fin ℓ → ZMod q) → Fin (n' + m f) → ZMod q
  rec_spec : ∀ f x z τ, pgb f x z τ ⬝ᵥ rec f x = z ⬝ᵥ eval f x       -- reconstruction
  privacy : ∀ f x z, law (pgb f x z ·) ≈[δ] law (pgb* f x (z ⬝ᵥ eval f x) ·)   -- explicit δ
```
- `pgb` and `pgb*` are defined from L₀, L₁ exactly as in Lemma 1 (definitions with `_eq` readers,
  not fields).
- Privacy is an exact-law closeness with explicit slack δ (Wee20 writes ≈_s). An instance with
  δ = 0 is recommended.
- **Lemma 1's swapped shapes** (sources-r2 § 2) are read as §4.2 uses them, and the reading is
  recorded.
- The instance for degree-≤ d polynomial vectors is Q2.

### 4.8 Π and the quadratic scheme (`Wee20/Linear*`, `Wee20/Quadratic*`)
These are typed algorithms over the drawn group `B = G.inst κ r` with g ∈ G*. Exponents are
`ZMod B.order`. All matrix shapes are Wee20's with k = k' = 2.

**Π** [Wee20, §4.2]:
- Setup samples A, W, U, V; Enc takes z in the clear (honest Enc always knows it);
- KeyGen(msk, (f, [M])) runs `L₁, L₀` and samples T, R; Dec is (6)–(8).
- **Correctness (9)–(11):** `pi_dec_eq : Dec = e(g,g)^{zM f(x)^⊤}` for every coin.
- **Security** (Theorem 1's bound, in the group-first form the outer reduction needs; Q3):
  - the adversary sees pp and mpk₀, then commits to (x*, z*) and to q pairs (f_j, [M_j]); it gets
    ct* and the q keys;
  - the simulator receives [z* M_j f_j(x*)^⊤] = g^{µ_j};
  - the inequality is Games 0–5:
    - Lemma 2: MDDH¹_{2,3};
    - Lemma 3: an identity for full-rank (A | c), plus a 1/p failure term;
    - Lemma 4: MDDH^{ℓ}_{2,mQ} (n = ℓ the public length);
    - Lemma 5: partial-garbling privacy, δ per key.

**Quadratic** [Wee20, §3.1–§3.3], with n₁ = n₂ = n at the use site:
- mpk = (pp, [A₁], [A₂], mpk₀); [M] is computed from them.
- Correctness by (4)–(5).
- Security Games 0–4:
  - Game 1: Π's inequality;
  - Game 2: identity (5);
  - Game 3: MDDH^1_{2,n} on A₁, with z*₁ added in the exponent;
  - Game 4: MDDH^1_{2,n} on A₂.

The simulator is §3.2 (Enc* draws y₁, y₂ and keeps them in its state; KeyGen* uses
`g^{(y₁ ⊗ y₂) f(x*)^⊤} · (g^µ)^{-1}`). Misprints are read as in sources-r2 § 2.

### 4.9 The PHFE (`FunctionalEncryption/Wee20.lean`)
```lean
/-- [GJLS21, Definitions 4.1–4.3] for the class of [GJLS21, §9], instantiated by the scheme of
[Wee20, §3] on symmetric groups with k = k' = 2 ([JLS26, §1.4]; [GJLS21, Theorem 10.3]). -/
noncomputable def wee20PHFE (G : BilinearGen) (PG : …) (ℓ n : PolyExpr) (d : ℕ) :
    FEScheme (phfeClass ℓ n G.wG d)
```
- Enc(x, y) = quadratic Enc(x, (y, y)); KeyGen(c) = quadratic KeyGen(vec c).
- `cprm` is the drawn order; `DecOut` is G_T; `embed v = e(g,g)^{v.val}`.
- The definition takes no `p` and no `hp`.

### 4.10 Headlines
```lean
theorem wee20PHFE_correct : (wee20PHFE G PG ℓ n d).Correct
theorem wee20PHFE_correctExcept : (wee20PHFE G PG ℓ n d).CorrectExcept 0      -- Def 4.2
theorem wee20PHFE_ctLen_eq : (wee20PHFE G PG ℓ n d).ctLen = …   -- (6n + 5)·wG + ℓ·wG: no ℓ
                                                                  -- dependence beyond x itself
/-- The core inequality, [GJLS21, Def 4.3] shape, explicit slack. -/
theorem wee20PHFE_simAdv_le (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (A : TwoStage) (q : PolyExpr) :
    ∃ ω : (i : Fin 4) → ∀ κ, Wee20Advice G PG p ℓ n d q i κ, ∀ B : Fin 4 → NUPPT,
      (∀ i, (B i).RealizesOn G.dlinEnc A.A₂.coins (wee20Red G PG hp ℓ n d A q i (ω i))) →
      ∀ κ, (wee20PHFE G PG ℓ n d).simAdv (wee20Sim G PG ℓ n d) A q κ ≤
        ∑ i, G.dlinAdv (B i) κ + wee20Slack G PG ℓ n d q p κ
/-- Realisability of the reductions (Phase B constructs the realisers). -/
def Wee20Realizable (G PG p hp ℓ n d) : Prop :=
  ∀ A q i ω, ∃ B : NUPPT, B.RealizesOn G.dlinEnc A.A₂.coins (wee20Red G PG hp ℓ n d A q i ω)
theorem wee20PHFE_simSecure (p) (hp) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hreal : Wee20Realizable G PG p hp ℓ n d)
    (h : G.DLINAssumption) : (wee20PHFE G PG ℓ n d).SimSecure
theorem wee20PHFE_subexpSimSecure (p) (hp) (hpb) (hreal) (h : G.SubexpDLIN) :
    (wee20PHFE G PG ℓ n d).SubexpSimSecure
```
- **The reductions.** There are four reduction functions:
  - MDDH¹_{2,3} for Π's Game 1;
  - MDDH^ℓ_{2,mQ} for Π's Game 4;
  - A₁ in the quadratic Game 3;
  - A₂ in the quadratic Game 4.

  Each is composed with `dlinToMddh`. Codex fixes the exact count at M0.
- **`wee20Slack`** is explicit: (constant)/p (the rank events of Π's Setup* and of the MDDH
  re-randomisation) and q·δ from partial garbling. It is `SubexpSmall c` for c < 1 under `hpb` (via `.mul_pow`, `.add`,
  `subexpSmall_two_pow_neg`, `.comp_of_rpow_le`).
- **`hreal`** (`Wee20Realizable`) is what Phase B discharges. The corollaries need it now, and their
  docstrings say so. Its coin polynomial is A₂'s: the realiser hands its coins to A₂.
- **Subexponential corollary.** One exponent works for every (A, q) because the number of hops is
  constant: `SubexpSmall.add`, then `.mono_exponent` to min(c, 1)⁻.
- If Q1 is (C), the predicate and statements change as § 7 says.

### 4.11 Efficiency statements (written, not proved)
Each is a named `Prop` with an `_iff` reader, never a `theorem … := sorry`:
- `Wee20.KeyGenEfficient`, `Wee20.DecEfficient`, `Wee20.SetupCoreEfficient`, `Wee20.SimEfficient`
  (a string form of each deterministic core, with group operations through `G.Ops` and p read by
  `orderStr`): `PolyTimeComputable` of the string form, or `∃ A, A.Uniform ∧ A.Computes f`.
- **`Wee20.LinearEfficient`** ([GJLS21, Def 4.6]): ∃ one `FinTM` M and one `PolyExpr` q such
  that, for all ℓ, n, κ and inputs, M computes Enc's deterministic core (pk, x, y, exponents) within
  (ℓ(κ) + n(κ))·q(κ) steps (`FinTM.ComputesInTime`). It is uniform in κ, ℓ and n.
- **Exclusions.** No RAM interface appears. No efficiency `Prop` is a hypothesis of a security or
  correctness theorem.

## 5. Proof plan (sources for every hop)

| Step | Statement | Source | Kind |
|---|---|---|---|
| P1 | DLIN ⇒ MDDH^d_{2,ℓ} (explicit slack) | [Wee20, §2.1] citing [EHKRV13] | reduction function + statistics |
| P2 | partial-garbling instance: reconstruction, privacy | [Wee20, Lemma 1]; Q2 | algebra + exact law |
| P3 | Π correctness | [Wee20, §4.2, (9)–(11)] | algebra |
| P4 | Π security inequality | [Wee20, Thm 1, Lemmas 2–5] | typed hops + 2 reductions |
| P5 | quadratic correctness | [Wee20, §3.1, (4)–(5)] | algebra (mixed product) |
| P6 | quadratic security inequality | [Wee20, §3.3] | typed hops + Π + 2 reductions |
| P7 | class embedding, `wee20PHFE` correctness | [GJLS21, §9]; G2 | identity |
| P8 | Def 4.3 form for the PHFE (from P6 with z₁ = z₂ = y; the Def 4.3 game is the special case G3) | [GJLS21, Def 4.3]; G3 | game equality |
| P9 | corollaries | [GJLS21, Remark 4.5]; #374 | asymptotics |

- **Shape of the hops.** Every computational hop is "typed game difference = typed advantage of the
  reduction's coin function", then the transfer lemma (§ 4.4).
- **Statistical hops.** These carry explicit terms: the 1/p rank events (Π's Setup*, the MDDH
  re-randomisation) and partial-garbling privacy. Reductions are deterministic given ω*, so there
  is no draw term.
- **Typed identities.** These use `expect_sample_equiv`, `expect_simulate_rel` and
  `expect_sample_rel`.

## 6. Milestones and size (Phase A; one end-to-end job, Q4)

| M | Content | Push | Est. lines |
|---|---|---|---|
| **M0** | **Statements commit**: every new file with definitions and readers (readers proved), every theorem stated with `sorry` under its sketch, docstrings, **the fidelity table against [GJLS21, Defs 4.1–4.3, 4.6, §9] first**, facade lines, size re-estimate | checkpoint 0 | 2,000–3,000 |
| M1 | Exponents; DLIN; MDDH; P1 | checkpoint 1 | 1,400–2,500 |
| M2 | Generic FE and reduction plumbing; classes; P7's identity; partial-garbling interface and instance (P2) | checkpoint 2 | 2,300–4,500 |
| M3 | Π: P3, P4 | checkpoint 3 | 2,000–3,700 |
| M4 | Quadratic: P5, P6 | checkpoint 4 | 1,300–2,300 |
| M5 | `wee20PHFE`, P8, headlines, P9, ct width, efficiency `Prop`s; final checks | final | 400–800 |
| | **Total (M0 counted inside M1–M5)** | | **~7,400–13,800** |

- **Instance outside the job.** With the partial-garbling instance out of the job (Q2(B)), the
  total is ~6,200–11,300.
- **Against r1.** r1 estimated 8,300–15,100. Phase A drops the machine milestone (−2,000–4,000) and
  adds partial garbling (+1,350–2,750) and the MDDH self-reduction (+800–1,500).
- **Calibration.** BB1 is ~6k with its machine; the sPRG is 4–7k.
- **Overrun.** If the budget runs out, a PARTIAL final: all statements, every proved declaration
  standard-axiom-only, the remaining sorries listed, and a continuation note.

## 7. Questions for Seyoon (r2 numbering; multiple choice, recommended first)

**Q1. What the simulator is given for each key** (gap G4; affects the generic predicate).
- **(A)** The value µ_j ∈ ℤ_p (`C.Out = ZMod p`): [Wee20, §2.2]'s definition, and what
  [GJLS21, Thm 9.2]'s proof supplies (Hybrid 1, p. 61: w = (P, {f_i}, {v_i}) in the clear). Wee20's
  simulator is built to use only g^{µ_j}, recorded as a remark. Deviation from the literal Def 4.3
  (Z = G_T) is recorded. *Recommended.*
- (B) The literal reading: e(g, g)^{µ_j} ∈ G_T. Wee20 does not prove it (its simulator needs g^µ,
  §3 p. 6), and no staged source does. The job would stop at an open step (E-STMT).
- (C) g^{µ_j} ∈ G: exactly Wee20's simulator interface, and stronger than (A). The generic `Out`
  then becomes group-dependent, which is less reusable.

**Q2. Partial garbling** ([Wee20, Lemma 1], cited from [AGW20], [IW14], [Wee17]; none staged).
- **(A)** The interface (§ 4.7) plus an instance for vectors of degree-≤ d polynomials in this job,
  after Seyoon stages [AGW20] (CRYPTO 2020) and [IW14] (ICALP 2014) on the exchange, so that the
  instance has a source to cite. *Recommended.* Size +1,200–2,500.
- (B) Only the interface in this job. All Wee20 results are stated for any partial-garbling scheme
  satisfying Lemma 1, and the instance is a follow-up job. The headline is then conditional on an
  instance (smaller job, ~6.2–11.3k).
- (C) No partial garbling: encrypt z ⊗ mon(x) with a plain linear FE. Simpler, but the ciphertext
  grows like n·(ℓ+1)^d, which breaks [GJLS21, Def 4.6] (linear efficiency), so it is a fidelity
  deviation.

**Q3. Which notion each layer proves** (r1 Q6, now with the sources).
- **(A)** The weakest notions that suffice:
  - the outer scheme proves [GJLS21, Def 4.3] directly;
  - Π proves the group-first form its caller needs: commitments after pp and mpk₀, all keys at
    once.

  Wee20's semi-adaptive notion is a documented extension. *Recommended:* smallest, and fidelity to
  Def 4.3 is exact.
- (B) Wee20's semi-adaptive SIM for both layers, as written, and then Def 4.3 as a corollary. This
  needs adaptive key oracles and the "random guessing" step (Wee20 p. 14), about +1,000–2,000 lines.
- (C) One monolithic hybrid for the concrete scheme, with no Π layer.

**Q4. One job or two** (r1 Q13; ~7.4–13.8k lines).
- **(A)** One end-to-end job, as the campaign ruled, with checkpoints at M0–M5 and a PARTIAL final
  allowed. *Recommended.*
- (B) Two jobs, each with its own gates: (1) DLIN/MDDH, generic FE, classes, partial garbling
  (~3.7–7.0k); (2) Π, the quadratic scheme and the headlines (~3.7–6.8k).

**Q5. Where `NUPPT.RealizesOn` lives.** This is the same question as the sPRG pack's **Q-S9**;
rule them together.
- **(A)** One shared owner file, `TCSlib/Cryptography/Asymptotic/Realization.lean` (`RealizesOn`,
  readers, the verdict lemma; ~80–150 lines), written in house and stacked on #374 before
  dispatch. `<BASE>` is that head and both jobs reuse it. If it is not at `<BASE>`, the job writes
  the same declarations in `FunctionalEncryption/Realization.lean` for a mechanical move later.
  *Recommended.*
- (B) Each job defines its own, unified after both land (a disclosed duplication).
- (C) No predicate: each theorem carries the agreement hypothesis inline.

### Settled since r1 (not asked)
| r1 | Now | Basis |
|---|---|---|
| Q1 notion | [GJLS21, Def 4.3], ε = 1, many-key; the residue is Q1 above | sources-r2 § 3(b) |
| Q2 class | GJLS21 §9 class (constant degree d in x, homogeneous quadratic in y), plus the `pad_one` reader; no NC¹/ABP; the residue is Q2 | GJLS21 §9 pp. 57–58 |
| Q3 correctness | in the exponent (G_T), perfect, plus the Def 4.2 form | GJLS21 §4, §9; Wee20 §3 p. 6 |
| Q4 compactness | Def 4.6 as a written `Prop` (Phase A) plus a proved ct-width equation | GJLS21 §9 p. 58 |
| Q5 generality | generic FE; fidelity first; IND, ε < 1 and adaptive security documented | ruling "Generic FE" |
| Q7 DLIN home | (A): new `Pairing/{Exponents,Linear,MatrixDH}` files, two facades | pairing precedent |
| Q8 g | (A): uniform in G* | pairing Q2 |
| Q9 modulus | superseded: fixed schedule `hp`; algorithms read p from pp | Q-S2; "p as input" |
| Q10 sPRG link | (A): independent representations; `pad_one` makes the later bridge a lemma | jobs run in parallel |
| Q11 game | a two-stage adversary (A₁, A₂) of NUPPTs, Def 4.3 literally; no oracle, no `Pub` oracle. This departs from pairing Q7 because the source's experiment is non-interactive, and because single-activation reductions fit the shared `RealizesOn` (sPRG Q-S9) | Def 4.3; Q-S2; § 4.4 |
| Q12 simulator | typed, universal; efficiency a written `Prop` | pairing Q5; Phase A |
| Q14 k | k = k' = 2 (k' = 1 is impossible on symmetric groups, Wee20 p. 2); matrix lemmas generic in k where free | sources |

## 8. Risks

- **Symmetric adaptation.** Checked statically: no hop uses asymmetry (§ 1.2). Codex re-checks each
  hop at M3/M4 and escalates E-SRC if one fails.
- **Partial garbling** (Q2): the largest unknown in size; its source must be staged for (A).
- **The MDDH self-reduction**: the tight route needs rank and uniformity arguments; the fallback is
  a column hybrid.
- **Dependent types**: `Pub` and the group depend on coins (`G.inst κ r`), as in BB1. Follow BB1's
  `_onSpec` readers; avoid Σ-typed instances.
- **Realisers** (Q5 = sPRG Q-S9): if the definition moves after M0, the statements change. Fix Q5 before
  dispatch.
- **Parallel jobs**: the sPRG job shares the host; this job holds at most one Lean process.
- **Stage 2 drift**: S2-A edits `Pairing/Assumptions.lean` (A05), `Games/Probability.lean` (A04) and
  `IdentityBased/Defs.lean` (A06). The job imports and never edits them, and rebases if S2-A merges.

## 9. Documented extensions (not built)
- Wee20's semi-adaptive notion (Q3(B)); IND ([GJLS21, Def 4.4]); ε-simulation for ε < 1 (Def 4.3's
  Sample); adaptive security; many challenge ciphertexts.
- Secret-key PHFE (GJLS21 Remark 4.1; the SXDH route of JLS26 §1.4).
- The ABP/NC¹ class of Wee20 and GJLS21 §8; general k-Lin.
- IBE as an FE instance (no refactor of `IdentityBased/Defs.lean`).
- Phase B: RAM programs, efficiency proofs, realisers, and unconditional corollaries.
