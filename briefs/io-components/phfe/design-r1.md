# io-phfe design r1: degree-2 partially hiding FE from DLIN [Wee20], JLS26 pipeline

The design note that the Codex dispatch (`dispatch-prompt.md`) points to. Prepared 2026-11-18 at
records tip `0fec25892d5aea3acde4908d94451f24b3c23b79`, from static reading only (no Lean run).

Every Lean shape below is **proposed. Codex may refine it, with disclosure in `REPORT.md`.** Seyoon's
rulings on § 7 override this note. The maintainer records them in `rulings.md` beside it before
dispatch.

## 0. Settled conventions (rulings of 2026-11-18; not open)

1. **The JLS26 journal pipeline.** Where JLS26 differs from its conference version or from GJLS21,
   JLS26 wins:
   - symmetric bilinear groups of prime order with **DLIN**, not SXDH on asymmetric groups;
   - **public-key** PHFE from DLIN, as [JLS26, §1.4] attributes it to [Wee20] ([JLS26, ref. 155]),
     not the secret-key SXDH PHFE of [JLS26, refs. 114, 131];
   - the PHFE **notion that [JLS26, Theorem 5.1] consumes** through [GJLS21, Theorems 10.3, 10.4].

   GJLS21's definition is used where JLS26 relies on it. Where GJLS21's text is written for another
   setting (asymmetric groups, bilateral DLIN, SXDH or secret key), the docstring records the
   adaptation and cites JLS26 for it: [JLS26, Theorem 5.1] ("implied by the DLIN assumption on
   symmetric bilinear groups") and [JLS26, §1.4].
2. **Non-uniform PPT throughout** ([PS10, Definition 26.8]; `Complexity.NUPPT`). Assumptions read
   "every `NUPPT` has negligible advantage". **Every reduction is a machine**: an `NUPPT` built
   with its efficiency proved, in the pattern of `BonehBoyenMachine/` (§ 5).
3. **Sampling** (IOComponentsPlan.md, "Deferred library work"). Laws are exact finite
   distributions, and the pairing code's existing convention is reused:
   - **games and typed algorithms** draw with `Games.ProbComp.sample` (exact uniform on a finite
     type): `ZMod p`, `{x : G // x ≠ 1}`, `G_T`, generator coins. Dependent draws are sequential
     binds, as in `BilinearGen.dbdhGame` (a uniform draw over a dependent sum would change the
     generator's law: `Pairing/Assumptions.lean`, module docstring);
   - **reduction machines** draw exponents from coin blocks with `BB1Machine.draw` (the bounded
     rejection sampler `Candidates.sampleBelowL`), and pay its statistical distance through
     `BB1Machine.statClose_draw` / `BB1Machine.abs_expect_draws_sub_le` (`q · 2^{-n}`, n = κ + wG + 1),
     exactly as `exists_bb1_distinguisher` does.

   The generic "sampler bridge with perfect correctness" is deferred library work. **The job does
   not build it.**
4. **Generic FE, with PHFE as an instance** (Seyoon's design goal; a goal, not a hard rule): § 4.3.
   Where generality would cost fidelity to the JLS26 notion, or make the job much larger, fidelity
   wins and the trade-off is a question (Q5).
5. Library conventions inherited without change: g uniform in G* (pairing ruling Q2); typed honest
   algorithms with efficiency deferred (pairing Q5); one adversary machine against oracles, with
   an `Init` oracle (pairing Q7); the two-experiment advantage (pairing Q9); encodings injective on
   reachable objects (ruling G40-01); PDFs not committed (pairing Q12).

## 1. What is being formalized: the citation chain

Details and the verification status of each link: `sources.md` § 3.

### 1.1 Verified (JLS26 PDF)
- **Consumer:** [JLS26, Theorem 5.1] = [GJLS21, Theorems 10.3, 10.4]. Its pairing hypothesis is
  bilateral DLIN on asymmetric groups of order p, "implied by the DLIN assumption on symmetric
  bilinear groups of order p". Its sPRG hypothesis has complexity (deg d, deg 2) over ℤ_p.
- **PHFE as JLS26 describes it** [JLS26, §1.4]: "Partially Hiding Functional Encryption (PHFE),
  for constant degree public computation and degree 2 private computation". "DLIN directly gives
  public key PHFE scheme by the work of [155]".
- **DLIN** [JLS26, §1.1, p. 3]: `(g^x, g^y, g^{xr}, g^{ys}, g^{r+s}) ≈_c (g^x, g^y, g^{xr}, g^{ys},
  g^z)`.
- **The class JLS26 feeds to it** [JLS26, Definition 3.3]: Process_I of degree d in the public
  seed P, and Q_I of degree 1 in P̄ = Process_I(P) and degree 2 in the private seed S. The
  composite has degree ≤ d in P and ≤ 2 in S. Each of the m outputs is one such polynomial.

### 1.2 Not verified (PDFs refused; staged later by Seyoon)
- **GJLS21's PHFE definition:** its number, syntax, correctness form, security notion and
  compactness are unknown (Q1–Q4). The abstract says public-key, degree 2 on the secret part and
  arithmetic NC¹ on the public part.
- **Wee20's theorem:** its number is unknown. The abstract says public-key PHFE for NC¹ public ×
  quadratic private, **selective simulation security against unbounded collusions**, from
  bilateral k-Lin in prime-order groups, and ciphertexts independent of the public-input length.
  The core is "a reduction from FE for quadratic functions to FE for linear functions".

### 1.3 The target, and the bridge rule
- **Target notion:** the one [GJLS21, Definition `<GJLS21-PHFE-DEF>`] defines and Theorems
  10.3/10.4 use, adapted to symmetric DLIN and public key as in § 0.1.
- **If Wee20 proves exactly that notion** (or a stronger one that implies it with no argument), the
  headline is Wee20's theorem stated through the generic predicate, instantiated at G₁ = G₂ = G,
  k = 2.
- **If Wee20 proves something different** (another class, notion or setting), the job states
  GJLS21's notion. It proves Wee20's theorem plus a **bridge** lemma, and the docstring cites
  where the literature proves the bridge (Seyoon names the place: Q1). The **statements gate
  checks this fidelity first**.
- **Group-setting adaptation:** [Wee20] is written for asymmetric groups and bilateral k-Lin. The
  job instantiates G₁ = G₂ = G (the library's symmetric `BilinearGroup`) and k = 2. Elements that
  Wee20 places in both source groups become one element of G, and bilateral 2-Lin becomes DLIN in
  G. Cite [JLS26, Theorem 5.1 and §1.4] for the adaptation. If the PDF shows a step that needs
  asymmetry, the job reports it (E-SRC) and does not patch the proof silently.

## 2. Mathematical shape of the deliverable

- **DLIN** in the library's asymptotic form (`BilinearGen`, NUPPT distinguishers, the description
  given to the adversary), with its 2-Lin matrix form `A = [[x,0],[0,y],[1,1]]`, `[A], [A s]` and,
  if Wee20's proof needs it, a **many-sample** form `[A], [A S]` vs `[A], [U]`. The many-sample
  form has a tight random self-reduction ([A | z] is invertible unless z ∈ span A, probability
  1/p): one machine, statistical loss 1/p ≤ 2^{-κ} + δ(κ) under `OrderAtLeastExcept`. A hybrid
  over the columns is the fallback (one machine with a non-uniform hybrid index).
- **Generic FE** (§ 4.3), with **PHFE = FE for the class of polynomials of bidegree (d, 2)**
  (§ 4.4). The message is a pair (x public, z private), the ciphertext may reveal x, and
  decryption yields `f(x, z)` in the form ruled in Q3.
- **The scheme** `wee20PHFE` (§ 4.6): the [Wee20] partially hiding construction, layered as Wee20
  layers it (FE for linear functions, then quadratic, then partial hiding; Q6).
- **Headlines:** perfect correctness, and selective simulation security under DLIN (or GJLS21's
  notion, Q1), with every reduction a machine.

## 3. Module layout (proposed; Q7 rules the DLIN home)

New files only. Every file stays at most 1000 lines and targets 150–600 (policy §1).

| File (new) | Contents | Est. lines |
|---|---|---|
| `TCSlib/Cryptography/Pairing/Exponents.lean` | `[v]`, `[M]` (vectors and matrices of group elements `g^{v_i}`) with their algebra: sums, scaling, `[M v]` from `[M]` and `v`, pairings of vectors to `e(g,g)^{a·b}` | 250–450 |
| `TCSlib/Cryptography/Pairing/Linear.lean` | `dlinStr`, `dlinGame`, `dlinAdv`, `DLINAssumption` and readers; the 2-Lin matrix form | 300–500 |
| `TCSlib/Cryptography/Pairing/LinearMany.lean` (if needed) | the many-sample game and `mdlin_of_dlin` (statement and typed part) | 300–600 |
| `TCSlib/Cryptography/Pairing/LinearMachine/*.lean` (if needed) | the self-reduction machine (words, handler, run, bound) | 800–1,500 |
| `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption.lean` | facade (`## Contents`, `## References`) | 40 |
| `…/FunctionalEncryption/Defs.lean` | `FnClass`, `FEScheme`, `honestRun`, `Correct`, `Simulator`, the selective game and `SelSimSecure` (+ `SelIndSecure` if Q5/Q1 say so) | 500–900 |
| `…/FunctionalEncryption/DegreeTwo.lean` | the bidegree-(d, 2) class `degTwoPH` (coefficients, evaluation, encoding readers) | 250–450 |
| `…/FunctionalEncryption/Wee20/Linear.lean`, `Quadratic.lean`, `Scheme.lean` | the layers and the scheme `wee20PHFE`, with readers | 900–1,800 |
| `…/FunctionalEncryption/Wee20/Correct.lean` | correctness of the layers and of `wee20PHFE` | 400–900 |
| `…/FunctionalEncryption/Wee20/Security/*.lean` | the typed hybrids and statistical steps | 2,000–3,500 |
| `…/FunctionalEncryption/Wee20/Machine/*.lean` | reduction machines: words, handlers, draws, runs, bounds | 2,000–4,000 |
| `…/FunctionalEncryption/Wee20.lean` | the headline security theorem through the generic predicate | 150–300 |

**Why here:**
- *FE beside IBE.* `AdvancedEncryption/` already holds "encryption primitives beyond PKE"
  (IBE, GSW), and the FE interface is consistent in style with `IdentityBased/Defs.lean`
  without duplicating it.
- *DLIN beside BDH.* DLIN is an assumption on the pairing bundle, so it lives in `Pairing/`. The
  existing `Pairing/Assumptions.lean` is not used: cleanup S2-A step A05 edits it now, and the job
  creates new files only.
- *Exponent helpers in `Pairing/`*, because they serve the whole area (policy §1, "Helpers").

**Existing files touched (Q7(A)):** one import line, plus its `## Contents` bullet and the new
reference tags, in each of two existing facades:
- `TCSlib/Cryptography/AdvancedEncryption.lean` (`import …FunctionalEncryption`);
- `TCSlib/Cryptography/Pairing.lean` (`import …Pairing.Exponents`, `…Pairing.Linear`; one line
  each if two files).

`TCSlib.lean` already imports both facades, so it is not touched. This exceeds the default "one
facade line in one existing facade", and **needs Q7's ruling**.

**Namespaces:**
- `TCSlib.Cryptography.Pairing` (DLIN as `BilinearGen.DLINAssumption`; exponent helpers under
  `BilinearGroup`);
- `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption` (generic FE and the class);
- `…FunctionalEncryption.Wee20` for the scheme's internals. Machine helpers go in an inner
  `Wee20Machine` namespace, as `BB1Machine`.

## 4. Proposed statement shapes (Lean-like; proposed, Codex may refine with disclosure)

### 4.1 DLIN [JLS26, §1.1]
```lean
namespace TCSlib.Cryptography.Pairing
/-- The DLIN string ⟨d, ⟨g, ⟨X, ⟨Y, ⟨U, ⟨V, W⟩⟩⟩⟩⟩⟩⟩, elements by their encodings. -/
def dlinStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g X Y U V W : B.G) :
    List Bool
theorem dlinStr_eq … := rfl
namespace BilinearGen
/-- coins r; g ← G*; (x, y, r', s', z) ← ℤ_p⁵; D's coins; D on
`dlinStr B d g g^x g^y g^{x r'} g^{y s'} (if real then g^{r'+s'} else g^z)`. -/
noncomputable def dlinGame (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool
theorem dlinGame_eq … := rfl
noncomputable def dlinAdv (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (G.dlinGame D false κ) (G.dlinGame D true κ)
def DLINAssumption : Prop := ∀ D : NUPPT, Negligible fun κ => G.dlinAdv D κ
theorem dlinAssumption_iff : G.DLINAssumption ↔ … := Iff.rfl
```
Deviations to note in the docstrings:
- asymptotic, relative to a generator, as `DBDHAssumption`;
- **g uniform in G\*** (Q8(A)). JLS26 p. 3 says a canonical generator. The canonical form implies
  this one by re-randomization (raise the whole tuple to t ← ℤ_p*), so the assumption used is no
  stronger than JLS26's. The remark is given in prose, not formalized.
- The tuple order is JLS26's.

Many-sample form, if the proof needs it (shape):
```lean
noncomputable def mdlinGame (Q : PolyExpr) (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool
theorem mdlin_of_dlin (H : Candidates.ArithmeticFP) (O : G.Ops) (Q : PolyExpr)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DLINAssumption) :
    ∀ D : NUPPT, Negligible fun κ => advantage (G.mdlinGame Q D false κ) (G.mdlinGame Q D true κ)
```

### 4.2 Group-element vectors (`Pairing/Exponents.lean`)
`BilinearGroup.expVec B g v := fun i => g ^ (v i).val` and `expMat`. Readers include:
- `expVec_add` (pointwise product);
- `expVec_smul`;
- `expMat_mulVec` (`[M v]_i = ∏_j [M]_{ij}^{v_j}`);
- `pair_expVec` (`∏_i e([a]_i, [b]_i) = e(g, g)^{(a ⬝ᵥ b).val}`).

All are built on `pow_val_add`, `pow_val_mul`, `bilinear_pow` and Mathlib's `dotProduct`/`mulVec`
(see `duplication-sweep.md`). Add `pow_val_add_GT` only if no derivation from `pow_mod_card`
exists, and disclose it either way.

### 4.3 Generic FE (`FunctionalEncryption/Defs.lean`)
A function class carries its own parameter (for example the modulus p), a function-description
length, a message length, an output type, an evaluation map and a **leakage** map (what a
ciphertext may reveal). Partial hiding is the leakage: for ordinary FE it is empty, and for PHFE
it is the public part x.
```lean
structure FnClass where
  Prm : ℕ → Type                      -- class parameter (e.g. the modulus)
  fnLen msgLen leakLen : PolyExpr
  Out : (κ : ℕ) → Prm κ → Type
  eval : (κ : ℕ) → (c : Prm κ) → (Fin (fnLen.eval κ) → Bool) →
    (Fin (msgLen.eval κ) → Bool) → Out κ c
  leak : (κ : ℕ) → (Fin (msgLen.eval κ) → Bool) → Fin (leakLen.eval κ) → Bool

/-- A public-key FE scheme for the class `C` [GJLS21, Definition <GJLS21-PHFE-DEF>] in
generic form. -/
structure FEScheme (C : FnClass) where
  pubLen mpkLen skLen ctLen : PolyExpr
  Pub MPK MSK SK CT : ℕ → Type        -- Pub: public parameters (the group), drawn first
  cprm : (κ : ℕ) → Pub κ → C.Prm κ    -- the class parameter they fix (e.g. the order p)
  DecOut : (κ : ℕ) → Pub κ → Type
  embed : (κ : ℕ) → (pp : Pub κ) → C.Out κ (cprm κ pp) → DecOut κ pp   -- Q3
  pubGen : (κ : ℕ) → ProbComp (Pub κ)
  setup : (κ : ℕ) → Pub κ → ProbComp (MPK κ × MSK κ)
  keyGen : (κ : ℕ) → Pub κ → MSK κ → (Fin (C.fnLen.eval κ) → Bool) → ProbComp (SK κ)
  enc : (κ : ℕ) → Pub κ → MPK κ → (Fin (C.msgLen.eval κ) → Bool) → ProbComp (CT κ)
  dec : (κ : ℕ) → (pp : Pub κ) → MPK κ → SK κ → CT κ → DecOut κ pp
  encPub encMPK encSK encCT …          -- fixed-width encodings for the adversary
  encPub_inj encMPK_inj encSK_inj encCT_inj …   -- injective on reachable objects (G40-01)

namespace FEScheme
noncomputable def honestRun (κ) (f) (m) : ProbComp (S.Pub κ × S.MPK κ × S.SK κ × S.CT κ)
/-- Perfect correctness: every honest outcome decrypts to `embed (eval f m)`. -/
def Correct : Prop := ∀ κ f m, (S.honestRun κ f m).AllOutputs fun o =>
  S.dec κ o.1 o.2.1 o.2.2.1 o.2.2.2 = S.embed κ o.1 (C.eval κ (S.cprm κ o.1) f m)

/-- A simulator: from the public parameters and the leakage, encoded `mpk` and challenge
ciphertext; then each key from the function and its value on the challenge. -/
structure Simulator where
  St : ℕ → Type
  init : (κ : ℕ) → (pp : S.Pub κ) → (Fin (C.leakLen.eval κ) → Bool) →
    ProbComp ((Fin (S.mpkLen.eval κ) → Bool) × (Fin (S.ctLen.eval κ) → Bool) × St κ)
  key : (κ : ℕ) → (pp : S.Pub κ) → St κ → (Fin (C.fnLen.eval κ) → Bool) →
    C.Out κ (S.cprm κ pp) → ProbComp ((Fin (S.skLen.eval κ) → Bool) × St κ)
```
**The selective simulation game** (Q11(A)): one `NUPPT` against three bit-string oracles
(`Games.bitCodec`), with a polynomial budget q, as `IBEScheme.sidGame`:
- `Pub` (oracle 0): answers `encPub pp`;
- `Init` (oracle 1, on `m*`): the first query fixes `m*` and answers `⟨mpk, ct*⟩` (real:
  `setup` and `enc`; ideal: `Sim.init pp (leak m*)`); later queries repeat the answer;
- `KeyGen` (oracle 2, on `f`): `⊥` before `Init`. Otherwise real answers `⟨1, encSK sk_f⟩` and ideal
  answers `Sim.key pp st f (eval f m*)`.
```lean
noncomputable def selSimGame (Sim : S.Simulator) (A : NUPPT) (q : ℕ) (ideal : Bool) (κ : ℕ) :
    ProbComp Bool
/-- Selective SIM security, one challenge ciphertext, polynomially many keys. -/
def SelSimSecure : Prop := ∃ Sim : S.Simulator, ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ,
  Negligible ε ∧ ∀ κ, advantage (S.selSimGame Sim A (q.eval κ) false κ)
    (S.selSimGame Sim A (q.eval κ) true κ) ≤ ε κ
```
The simulator is **universal** (∃ Sim before ∀ A) and **typed**. Its efficiency is deferred with
the honest algorithms' (Q12(A); pairing Q5). Wee20's simulator is efficient, so the docstring
records this as a deviation. Readers: `selSimGame_eq`, the oracle case lemmas and
`selSimSecure_iff`, as for `sidImpl`.

**Where the literature varies** (parameters, defined only if cheap; Q5):
- **IND vs. SIM.** `SelIndSecure` uses the same oracles, with `Init(m₀, m₁)` refused unless
  `leak m₀ = leak m₁`, and `KeyGen(f)` refused (`⊥`) unless `eval f m₀ = eval f m₁` (refusal, as
  IBE's pairing Q8). Defining it costs ~150 lines. SIM ⇒ IND needs a machine that evaluates the
  class (larger), so the implication is not proposed unless Q1 needs IND.
- **Key bound.** An optional cap `t(κ)` on answered keys (1-key notions). It costs one argument
  and is added only if Q1's notion is bounded.
- **Selective vs. adaptive, many challenges, secret key:** documented extensions (§ 9), not built.

### 4.4 The bidegree-(d, 2) class (`FunctionalEncryption/DegreeTwo.lean`) [JLS26, §1.4, Def. 3.3]
Messages are x ∈ ℤ_p^ℓ (public) and z ∈ ℤ_p^n (private), each residue a w-bit numeral read
mod p. Extend both with a constant 1: x̂ = (x, 1) and ẑ = (z, 1). A function is a coefficient
tensor `c : Fin (n+1) → Fin (n+1) → (Fin d → Fin (ℓ+1)) → ℤ_p`, and
`f(x, z) = Σ_{j,k,t} c_{j,k,t} · ∏_{i<d} x̂_{t(i)} · ẑ_j · ẑ_k`.
- This is **every polynomial of degree ≤ d in x and ≤ 2 in z**. The monomials are tuples, so
  there are (ℓ+1)^d of them, polynomial for constant d, and `fnLen` is a `PolyExpr`
  (`PolyExpr.pow`).
- `leak (x, z) = x`.
```lean
noncomputable def degTwoPH (ℓ n w : PolyExpr) (d : ℕ) : FnClass   -- Prm κ := ℕ (the modulus)
theorem degTwoPH_eval_eq …   -- the sum formula, read through the decoded residues
theorem degTwoPH_leak_eq …
```
- One key gives one output, so the m outputs of an sPRG are m keys (unbounded collusion covers
  this).
- **Deviation notes:** the extension by 1 (Wee20's `f(x)ᵀ(z ⊗ z)` is homogeneous); tuples rather
  than monomials; constant degree rather than NC¹ (Q2).
- Residues are decoded with `Encoding.Modular` (must-reuse), with a total reading mod p.

### 4.5 PHFE
```lean
abbrev PHFEScheme (ℓ n w : PolyExpr) (d : ℕ) := FEScheme (degTwoPH ℓ n w d)
```
The docstring is the PHFE definition: "[GJLS21, Definition `<GJLS21-PHFE-DEF>`] in the public-key
DLIN form of [JLS26, §1.4]", with every deviation listed.

### 4.6 The scheme (`FunctionalEncryption/Wee20/…`)
```lean
noncomputable def wee20PHFE (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) :
    PHFEScheme ℓ n G.wG d
```
- **`Pub`:** the generator's coins and g ∈ G*, drawn in sequence. Use a structure, not a `Σ`:
  Σ-typed instances do not elaborate under the seals (T4's report, cited in the bb1-sim fill
  brief).
- **`cprm`:** the group order.
- **`DecOut`:** `G_T`, with `embed v = e(g, g)^{v.val}` (Q3(A)).
- **Residue width:** `G.wG`, sufficient because `p ≤ 2^{wG}` (`BB1Machine.order_le_two_pow`).
- **Algorithms:** [Wee20]'s partially hiding scheme with G₁ = G₂ = G, k = 2, **transcribed from
  the staged PDF at M0**. This note does not reproduce them, because the source could not be read
  (sources.md § 2).
- **Layers** (Q6(A)), following the abstract's "reduction from FE for quadratic functions to FE
  for linear functions". The internal FE for linear functions may need group-encoded inputs,
  which the generic syntax does not model. If so, it keeps a scheme-internal interface. Making it
  an `FEScheme` instance is a stretch goal, taken only if cheap.

### 4.7 Headlines
```lean
theorem wee20PHFE_correct (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) :
    (wee20PHFE G ℓ n d).Correct
theorem wee20PHFE_selSimSecure (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ κ) δ)
    (h : G.DLINAssumption) : (wee20PHFE G ℓ n d).SelSimSecure
```
- If Q1 rules a different GJLS21 notion: add that predicate, and
  `wee20PHFE_<notion> : … → (wee20PHFE G ℓ n d).<Notion>` via the bridge (§ 1.3).
- If Q4(A): add `wee20PHFE_ctLen` (the ciphertext width is O((n + 1) · wG), independent of ℓ),
  matching the compactness GJLS21 requires.
- `H` and `O` are needed only by the machines, as for `bb1_sidSecure`. `hN` makes the statistical
  terms (1/p, the draws) negligible.

## 5. Machines and efficiency (how reductions are built)

Each computational step is a reduction to DLIN, or to its many-sample form, built as BB1's step 3
is (`exists_bb1_distinguisher`):
1. a `Games.PolyHandler` whose `run`, `advIn` and `out` are polynomial-time string functions, with
   - group operations through `BilinearGen.Ops` (`mulG`, `powG`, `pairStr`, `mulT`, `memT`, and
     `orderStr` for p),
   - arithmetic mod p through `Candidates.ArithmeticFP` (`divModStr`, `addStr`, `mulStr`,
     `xgcdStr`),
   - exponents drawn from seed blocks by `BB1Machine.draw`;
2. `Games.exists_handlerMachine` (or `exists_interactiveHandlerMachine`) gives the `NUPPT`, and
   `Games.exists_toCompOn_of_toComp` adapts the adversary;
3. the drawn-versus-ideal gap is `BB1Machine.abs_expect_draws_sub_le`, and the averaging is
   `ProbComp.abs_expect_sub_le`.

Shared string words (pairing of encoded vectors, `[M v]` from `[M]`) go in one helper module and
serve every handler. **Do not copy `BB1Machine.Words`:** its arithmetic words read BB1's input
layout (`zD`). Where a layout-generic version is needed, request its promotion in `REPORT.md`, and
write a disclosed private local version until then. No step may be stated as an existential over
non-machine functions.

## 6. Milestones (one end-to-end job; size estimates in Lean lines)

| M | Content | Push | Est. lines |
|---|---|---|---|
| **M0** | **Statements commit.** Every new file with its definitions and readers (readers proved, by `rfl` where they hold), every theorem stated with `sorry` under its proof sketch, the module docstrings, the fidelity table (each definition and theorem → its exact source location, every deviation), the facade lines. Pushed first, as checkpoint 0; the **statements gate** runs on it while the job continues | checkpoint 0 | 2,000–3,000 |
| M1 | Exponent helpers; DLIN readers; the 2-Lin matrix form; the many-sample lemma with its machine (if needed) | checkpoint 1 | 1,500–2,800 |
| M2 | Correctness of the layers and of `wee20PHFE` | checkpoint 2 | 500–1,000 |
| M3 | Security: the typed hybrids and statistical steps for each layer, each computational step reduced to a typed DLIN/MDDH-with-post-processing statement | checkpoint 3 | 2,000–3,500 |
| M4 | The reduction machines (handlers, words, draws, runs, bounds) | checkpoint 4 | 2,000–4,000 |
| M5 | The headline theorem(s) through the generic predicate; the bridge (Q1) and compactness (Q4) if ruled; final checks | final | 300–800 |
| | **Total** | | **~8,300–15,100** |

For calibration: BB1 (one scheme, one reduction) is about 6,000 lines with the pairing bundle,
and its machine alone is ~2,750. The estimate is about twice the sPRG's (4–7k). The proof's
size depends on Wee20's hybrid count, which is unknown until the PDF is read. Codex re-estimates
at M0. If the job runs out of budget, it delivers a **PARTIAL final**: all statements, proved
targets with the standard axioms, and a continuation note (Q13).

## 7. Open questions for Seyoon (multiple choice, recommended option first)

**Where Seyoon's input matters most: Q1–Q3 and Q6** (the notion and the proof route, which he
knows well). Q1–Q4 also fill gaps the refused PDFs left. Each answer may come with the GJLS21
or Wee20 location it rests on.

**Q1. The PHFE security notion that GJLS21 Theorems 10.3/10.4 consume** (chain link (b); please
give the definition number for `<GJLS21-PHFE-DEF>`).
- **(A)** Selective simulation security: one challenge ciphertext and polynomially many keys
  after it, as Wee20 proves it per its abstract. *Recommended* as the generic predicate: it is
  Wee20's theorem, and it implies (C), (D) and (likely) (B).
- (B) A semi-functional notion (GJLS21-style keys or ciphertexts with a hard-wired value), stated
  as its own predicate, with a bridge from (A) whose literature place you name.
- (C) Selective indistinguishability security, polynomially many keys.
- (D) One-key, one-ciphertext simulation security.
- (E) Adaptive simulation security. This is not Wee20's notion, so the job would be much larger.

**Q2. Function class.**
- **(A)** Bidegree (d, 2) polynomials over ℤ_p, d constant (§ 4.4). This is JLS26 §1.4's
  "constant degree public, degree 2 private" and Def. 3.3's composite, and a subclass of Wee20's.
  *Recommended.*
- (B) Wee20's and GJLS21's class: arithmetic NC¹ (arithmetic branching programs) in x, quadratic
  in z. Most faithful to the cited theorems, but it needs an ABP model (none in TCSlib; Boolean
  BPs only) and a larger garbling layer.
- (C) Bidegree (1, 2) on a preprocessed public input P̄. Smallest, but the ciphertext carries P̄
  and loses the compactness JLS needs: a deviation.

**Q3. Correctness form.**
- **(A)** In the exponent: `Dec = e(g, g)^{f(x, z)}` (`embed`). Standard for pairing FE, and the
  generic `embed` covers it. *Recommended.*
- (B) The value `f(x, z) ∈ ℤ_p` for outputs in a polynomial range, by a brute-force discrete log
  (needs a range bound and `Ops`).
- (C) Both.

**Q4. Compactness.**
- **(A)** State a ciphertext-length lemma (`ctLen` = O((n + 1) · wG), independent of ℓ), matching
  whatever GJLS21 requires. *Recommended*, pending the GJLS21 text.
- (B) None beyond the encoding widths.

**Q5. Generality (your design goal).**
- **(A)** Generic `FnClass`/`FEScheme` with leakage, generic `Correct` and `SelSimSecure`, and
  PHFE as the instance. `SelIndSecure` and a key cap are defined only if Q1 needs them; the rest
  is documented (§ 9). About +300–600 lines over a PHFE-only syntax. *Recommended.*
- (B) PHFE-specific syntax only (smaller, less reusable).
- (C) The full family (SIM/IND × selective/adaptive × key and ciphertext bounds): larger, and
  beyond what JLS26 consumes.

**Q6. Proof architecture.**
- **(A)** Wee20's layers as written (FE for linear functions → quadratic → partially hiding),
  each layer with its own file and theorem. *Recommended:* the abstract names this reduction as
  the core.
- (B) One monolithic hybrid proof for the concrete scheme.

Your sketch of the hybrid sequence, if you have one in mind, would help most here.

**Q7. Where DLIN lives (facade lines).**
- **(A)** New `Pairing/Exponents.lean` and `Pairing/Linear.lean`, with import lines in
  `Pairing.lean`, plus the FE facade line in `AdvancedEncryption.lean`: two existing facades
  touched, import and `## Contents` lines only. *Recommended:* no conflict with S2-A.
- (B) DLIN in `Pairing/Assumptions.lean`. S2-A step A05 edits that file, so the job would rebase
  after S2-A merges.
- (C) DLIN inside the new FE directory: one facade line, and a later move to `Pairing/`.

**Q8. The DLIN generator g.**
- **(A)** Uniform in G* (pairing Q2). This is no stronger than JLS26's canonical-g DLIN (§ 4.1).
  *Recommended.*
- (B) The bundle's fixed `gen`, as JLS26 p. 3.

**Q9. The modulus.** JLS26 Theorem 5.1 uses one λ-bit prime p for the groups and the sPRG; the
library's generator draws a group of random order.
- **(A)** Use the drawn order p (`cprm`), and couple it with the sPRG's p in the later
  bootstrapping design. *Recommended.*
- (B) Add a fixed-order hypothesis `∀ κ r, (G.inst κ r).order = p κ` to the headline now.

**Q10. Sharing "(deg d, deg 2)" with the parallel sPRG job.**
- **(A)** Independent representations now, with a bridge later (the jobs run in parallel and
  cannot import each other). *Recommended.*
- (B) PHFE waits for the sPRG's M0 statements and adopts its representation (serializes the
  jobs).

**Q11. Game shape.**
- **(A)** One machine with `Pub`/`Init`/`KeyGen` oracles, so the group is public before the
  commitment (pairing Q7 plus a `Pub` oracle). *Recommended.*
- (B) The literal IBE shape: nothing before `Init`, and inputs are strings read mod an unseen p.
- (C) A two-stage adversary.

**Q12. The simulator.**
- **(A)** Typed and universal, with efficiency deferred with the honest algorithms' (pairing Q5).
  *Recommended.*
- (B) `NUPPT` simulators with efficiency proved (a string-level simulator; much larger).

**Q13. Size and partial delivery.**
- **(A)** One end-to-end job, as ruled, with checkpoints per milestone and a PARTIAL final
  allowed (all statements, proved parts standard-axiom-only, a continuation note). *Recommended.*
- (B) Split into two end-to-end jobs (the DLIN layer and exponents; then FE and PHFE), each with
  its own gates.

**Q14. Generality in k.**
- **(A)** k = 2 (DLIN) only, the case JLS26 needs, with matrix lemmas generic where it costs
  nothing. *Recommended.*
- (B) The general k-Lin family.

Sampling is not a question: § 0.3 is settled, and the pairing code fixes the convention.

## 8. Risks

- **Source access** (highest). The job cannot start without both PDFs staged and Q1 answered.
  Without them, the PHFE notion cannot be fidelity-checked.
- **Symmetric adaptation.** A proof step of Wee20 may use something the symmetric instantiation
  breaks. JLS26 asserts the implication, but the job checks it step by step, and escalates
  (E-SRC) if a step fails.
- **Size and machines.** Several reductions, each needing group words. A shared words module is
  mandatory, to avoid four private copies.
- **Rule 10 on dependent types.** `Pub` and the group types depend on coins (`G.inst κ r`), as in
  BB1. Follow BB1's readers and casts (the `_onSpec` pattern), and avoid Σ-typed instances.
- **Parallel jobs.** The sPRG job runs alongside under the same 3-process host cap. This job holds
  at most one Lean process.
- **Stage 2 drift.** S2-A may merge during the job. It touches `Games/Probability.lean` (A04, an
  addition), `IdentityBased/Defs.lean` (A06, DL-57's move) and `Pairing/Assumptions.lean` (A05).
  The job imports these files and edits none of them, so it rebases if S2-A merges.

## 9. Documented extensions (not built)

- Adaptive simulation and IND; many challenge ciphertexts; bounded collusion as a general
  parameter.
- A secret-key variant (`enc` with `msk`). [JLS26, §1.4] mentions it for SXDH; it is not needed
  for the DLIN route.
- The NC¹/ABP class (Q2(B)), and the general k-Lin (Q14(B)).
- **IBE as an FE instance:** message (ID, M), leakage ID, f_{ID'}(ID, M) = M if ID = ID' and ⊥
  otherwise. This is a possible later bridge; `IdentityBased/Defs.lean` is **not** refactored.
- The generic sampler bridge (IOComponentsPlan.md, "Deferred library work").
- PHFE efficiency (an `FEScheme.Efficient` predicate), as pairing Q5(B).
