# io-phfe design r3: degree-2 PHFE from DLIN [Wee20], semi-adaptive for both layers, Def 4.3 derived, Phase A

The design note behind `dispatch-prompt-r3.md`. It was prepared 2026-11-18 at records tip
`43eacf952cfc9517f9be8f93e367f658effd9b47`, from static reading of the five staged PDFs
(`sources-r3.md`) and the code (no Lean run).

**r3 is a delta over `design-r2.md`.**
- Sections listed as *unchanged* below are binding as written in design-r2.
- Every other section is replaced here.
- Every Lean shape is **proposed**: Codex may refine it **with disclosure in `REPORT.md`**.
- Precedence: `rulings.md` > design-r3 > design-r2.

| Pin | Value |
|---|---|
| Rulings | every decision-log row dated 2026-11-18, read at `32a40963de5ed5f7abb472cd9d432c6561c2e833`; in particular **standing rule 15** (*Efficiency is mandatory*, *Efficiency baked into definitions*; `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2), *Phase A rulings, first batch* (Q1 A, Q2 A, Q4 A, Q5 A), *second batch* (Q3 = Wee20's semi-adaptive SIM for both layers), *Partial-garbling sources received*, *Sampler bridge implemented*, *Shared `Asymptotic/Realization.lean` written* |
| Shared realisation file | `foundations/realization` head `cdc0934f36365533d410607d0664a0570ae92679` (on #374's `cbce64d1`), `TCSlib/Cryptography/Asymptotic/Realization.lean`; report `briefs/io-components/realization/REPORT.md` |
| Lean base | `<BASE>`: a branch stacking #374 + `foundations/realization` + #378 (`foundations/coin-sampling` `51dc7672`), shared with the sPRG job |

## What changed from r2

0. **Rule 15: efficiency is mandatory and baked into the definitions** (§ 1E, binding).
   - The generic `FEScheme`, the Def 4.3 `Simulator`, the `SASimulator` and the
     `PartialGarbling` interface carry their algorithms' efficiency as structure fields, in
     uniform form:
     - `PolyTimeComputable` of the deterministic cores, with pp (the group description) on the
       input;
     - samplers as an exact-law core plus #378's `UniformSampler`.
   - The constructions are **raw bundles** (`wee20PHFE_raw`, `wee20Sim_raw`, `wee20SASim_raw`,
     `layeredPG_raw`), with correctness and security proved for them.
   - The primitives (`wee20PHFE … hT`, …) are assembled from the raw bundles and the efficiency
     targets.
   - Reductions stay in `RealizesOn` form. The L1 link "pre-processing target ⇒ realiser" is
     proved in Phase A.
   - The statements gate checks "definitions carry efficiency" right after source fidelity.
1. **Q3 ruled (B).** Both layers prove **[Wee20, §2.2]'s semi-adaptive simulation security**:
   - the outer scheme, and the building block Π of [Wee20, §4];
   - mpk first; then the challenge (x*, z*); then **adaptive** key queries, after ct*.

   **[GJLS21, Definition 4.3] is derived** from the outer layer's semi-adaptive inequality by a
   generic game identity (§ 4.5). Consequences:
   - an adaptive adversary model, the library's oracle-machine form (§ 4.5);
   - reductions that run an adaptive adversary against deterministic answers (§ 4.4);
   - Π's Lemma 3 adaptive step done by an exact change of variables, replacing Wee20's
     "random guessing" (§ 4.8).
2. **Q2 ruled (A).** Partial garbling is an **interface** ([Wee20, Lemma 1] = [AGW20, Lemma 2],
   shapes corrected) **plus a proved instance**: [AGW20, App. A, (28)–(32)] on the layered ABP of
   a polynomial vector, proved by path sums, with **exact** privacy (§ 4.7; `sources-r3.md`
   § 3). Smaller than r2's instance.
3. **Q1 ruled (A):** µ_j ∈ ℤ_p, a disclosed deviation (r2's recommended text stands).
   **Q4 ruled (A):** one job, a PARTIAL final allowed.
4. **Q5 ruled (A); the shared file exists.**
   - `Complexity.NUPPT.RealizesOn` and its API are **must-reuse** at `<BASE>`.
   - `FunctionalEncryption/Realization.lean` is dropped.
   - The predicate's body constrains only coin strings of length `c.eval m` (weaker than r2's
     draft; statements unchanged; § 4.4).
5. **Two-level realisers.** Wee20's hops reduce to **MDDH** distinguishers. Those are then
   composed with r2's DLIN ⇒ MDDH reduction. Each level has its own `RealizesOn` hypothesis
   and its own Phase B route (§ 4.4).
6. **Base.** `<BASE>` carries #378 (`CoinSampling`, `Games.Closeness`).
   - Rule 15's efficiency fields need the type `UniformSampler`, so `CoinSampling.Efficiency`
     is imported **only** for that, in the definition files (§ 1E).
   - No other `CoinSampling` module and not `Games.Closeness`.
   - No sampler is built or proved efficient.
7. **Size** ≈ 8,800–16,100 lines (r2: 7,400–13,800) (§ 6).
8. **One open question, Q-E1** (§ 7.2): where `SamplesEfficiently` lives, the same question as
   the sPRG pack's; rule them together.

## 0. Binding rulings applied (adds to design-r2 § 0)

| Ruling | Effect |
|---|---|
| **Q1 (A)** | The Def 4.3 simulator's ω carries x* and (f_j, µ_j) with µ_j ∈ ℤ_p (the drawn order) [GJLS21, Thm 9.2, proof, Hybrid 1, p. 61]. The outer semi-adaptive simulator gets µ ∈ ℤ_p per key, which is [Wee20, §2.2]'s own form. Π's simulator gets g^{µ} ([Wee20, §3 p. 6, §4 p. 8]). Deviation from Def 4.3's literal G_T value: disclosed, with this justification |
| **Q2 (A)** | § 4.7: interface plus proved instance; [GJLS21, Def 4.6] is then unconditional at the scheme level (ct independent of the garbling size) |
| **Q3 = Wee20's semi-adaptive SIM for both layers** | § 4.5 (generic notion, the derivation of Def 4.3), § 4.8 (Π and the outer scheme), § 4.10 (headlines for both notions) |
| **Q4 (A)** | One job, checkpoints M0–M5, PARTIAL final allowed |
| **Q5 (A)** | § 4.4: the shared predicate, must-reuse |
| **Base stacking** | #374 + realization + #378 (+ the Q-E1 file if (A)). Only `CoinSampling.Efficiency` is imported, for the type `UniformSampler` in rule 15's fields (§ 1E). No other `CoinSampling` module and not `Games.Closeness` |
| **Rule 15** | § 1E: efficiency fields in every interface; raw bundles; assembly from targets; gate order (§ 6) |

Unchanged from design-r2 § 0 and binding:
- the journal pipeline;
- generic FE as a goal, with fidelity first;
- the fixed prime schedule `hp`;
- p as an input;
- subexponential via #374;
- two phases;
- uniformity;
- sampling (exact laws; reductions never sample);
- one Lean process.

r2's settled row **Q11 (game shape) is amended**:
- the Def 4.3 game keeps the two-stage (A₁, A₂) adversary, as Def 4.3 has it;
- the semi-adaptive games use the library's **oracle-machine** adversary
  (`NUPPT.toCompOn` with a `bitCodec`, as `IBEScheme.sidGame` does, pairing Q7). Wee20's
  adversary is stateful and adaptive.

## 1. The chain and the target (amends design-r2 § 1)

§ 1.1 is unchanged. In § 1.2:
- **G3.** The job proves Wee20's semi-adaptive notion for both layers. Def 4.3 is the special
  case (§ 4.5, `simAdv_eq_saSimAdv`). There is no loss.
- **G4.** Ruled (Q1 A).
- **G7.** Closed: `sources-r3.md` § 3, design § 4.7.
- G1, G2, G5, G6 and G8 are unchanged.

## 1E. Rule 15 in this job (new; binding)

### 1E.1 Raw bundles and primitives

| Interface | Raw bundle (correctness and security are defined here) | Primitive (adds the efficiency fields; no instance without them) |
|---|---|---|
| FE scheme ([GJLS21, Defs 4.1–4.2]; [Wee20, §2.2]) | `FEScheme.Raw`: design-r2 § 4.5's `FEScheme` fields. Setup, Enc and KeyGen are in **core-plus-draw** form (`SetupDraw κ pp`, `setupCore`; `EncDraw κ pp`, `encCore`; `KeyDraw κ pp`, `keyCore`), with `setup`/`enc`/`keyGen` derived definitions with readers. Dec is deterministic. PPGen is the group generator's description (`BilinearGen.gen`, already a uniform NUPPT, `gen_uniform`) | `structure FEScheme extends FEScheme.Raw` with `setup_eff`, `enc_eff`, `keyGen_eff` (`SamplesEfficiently`, § 1E.2) and `dec_eff` (`PolyTimeComputable` of Dec's string form, pp on the input) |
| Def 4.3 simulator ([GJLS21, Def 4.3]: "∃ a (possibly stateful) PPT simulator") | `Simulator.Raw` (design-r2 § 4.5's `Simulator`, core-plus-draw) | `Simulator extends Simulator.Raw` with the three samplers' efficiency |
| semi-adaptive simulator ([Wee20, §2.2]: "a randomized simulator", efficient by the notion's reading) | `SASimulator.Raw` (§ 4.5) | `SASimulator extends SASimulator.Raw` with efficiency fields |
| partial garbling ([Wee20, Lemma 1]: "four efficient algorithms") | `PartialGarbling.Raw` (§ 4.7's structure) | `PartialGarbling extends PartialGarbling.Raw` with `lgen_eff` and `rec_eff`: `PolyTimeComputable` of the string forms of (L₁, L₀) and of `rec`, with p and the class parameters on the input. pgb and pgb* are matrix arithmetic on them and need no field |

- **The predicates `Correct`, `CorrectExcept`, `simAdv`, `saSimAdv` are defined on the raw
  bundles.**
  - `SimSecure S := ∃ Sim : S.Simulator, …` and `SASimSecure S := ∃ Sim : S.SASimulator, …`
    quantify over **efficient** simulators, as Def 4.3 and Wee20 demand.
  - Their raw-simulator forms `SimSecureWith (Sim : Simulator.Raw)` and `SASimSecureWith` are
    named, with readers.
- **Π** ([Wee20, §4]) is an internal building block, not a library interface: its keys carry
  group elements (§ 4.8). It is a raw bundle only (`Linear.scheme_raw`). Its efficiency enters
  through the outer scheme's targets (the outer KeyGen and Dec cores run Π's). This is
  disclosed.
- **Existing interfaces** this job only reuses (`BilinearGen` has `gen_uniform` and
  `BilinearGen.Ops` has `_poly` fields, so they already comply) need no change.

### 1E.2 Field forms (uniform only)

- **Deterministic cores.** `∃ f, PolyTimeComputable f ∧ ∀ κ r inputs, f (NUPPT.advInput κ
  ⟨G.desc κ r, inputs⟩) = output`.
  - The map is quantified before κ and the group; pp is the description string on the input.
  - Group operations appear only inside `f`'s specification, through `BilinearGen.Ops`
    (`orderStr`, `mulG`, `powG`, `pairStr`, …).
  - Never a bare `∃ A : NUPPT, A.Computes f`.
- **Samplers.** `SamplesEfficiently y encDraw encOut core` with parameter word `y κ π` = the
  encoded pp and the sampler's other inputs (design-r3 of the sPRG pack, § 1.2, gives the
  declaration). In words: a #378 `UniformSampler`, an explicit equivalence to the draw type,
  failure ≤ 2^{-κ}, and a `PolyTimeComputable` core. Home: **Q-E1** (§ 7.2).
- The **R-DLOG** rule (§ 4.4) applies to every core: no discrete logarithms.

### 1E.3 Targets and assembly

Design-r2 § 4.11's written `Prop`s become **the targets that inhabit the primitives**:

| Target | Content |
|---|---|
| `Wee20.SchemeTargets G ℓ n d` | `SamplesEfficiently` for Setup, Enc and KeyGen of `wee20PHFE_raw` (their cores run Π's and the quadratic layer's); Dec's `PolyTimeComputable` form |
| `Wee20.SimTargets …` | the same for `wee20Sim_raw` (Def 4.3) and `wee20SASim_raw` (semi-adaptive) |
| `Wee20.PGTargets ℓ n' d` | `lgen_eff`, `rec_eff` for `layeredPG_raw` |
| `Wee20.LinearEfficient` | [GJLS21, Def 4.6] for Enc's core: one `FinTM` with a (ℓ + n)·q(κ) step bound (design-r2 § 4.11). Not an interface field; it is a property of this scheme that GJLS21 §9 requires |
| `Wee20.MddhPreTargets` | L1: the `PolyTimeComputable` pre-processing of `dlinToMddh` on encodings (one map for every D, advice and κ) |
| `Wee20.Targets` | the conjunction |

**Assembly** (Phase A, pure, sorry-free; target witnesses chosen):
```lean
noncomputable def layeredPG (hT : Wee20.PGTargets ℓ n' d) : PartialGarbling …   -- toRaw = layeredPG_raw
noncomputable def wee20PHFE (G) (ℓ n d) (hT : Wee20.Targets G ℓ n d) : FEScheme (phfeClass ℓ n G.wG d)
noncomputable def wee20Sim (hT) : (wee20PHFE G ℓ n d hT).Simulator
noncomputable def wee20SASim (hT) : (wee20PHFE G ℓ n d hT).SASimulator Λ
theorem wee20PHFE_toRaw (hT) : (wee20PHFE G ℓ n d hT).toRaw = wee20PHFE_raw G layeredPG_raw ℓ n d
```
- The raw bundle `wee20PHFE_raw G PG ℓ n d` takes a **raw** garbling scheme `PG`, so it can be
  proved correct and secure for any `PartialGarbling.Raw`.
- The primitive uses the layered instance.

**The L1 link (proved in Phase A; pure, as the sPRG's Q-S11 link):**
```lean
theorem mddhRealizable_of_preTarget (hT : Wee20.MddhPreTargets …) : MDDHRealizable G p hp d ℓ
```
It applies `Complexity.NUPPT.exists_realizesOn_of_preTarget_id D G.dlinEnc encΩ pre hf hT ω b hb`
per MDDH distinguisher `D` (the φ = id shape). The L2 link (handler machines, T1) stays Phase B
(§ 8).

## 2. The deliverable (replaces design-r2 § 2)

*Rule 15 applies throughout (§ 1E).*
- Items 2, 4 and 5 below are the **raw bundles**, plus the efficient primitive structures and
  their assembly from targets.
- Item 6's headlines are proved on the raw bundles and restated on the assembled primitives.

1. **DLIN**, uniform-matrix **MDDH^d_{2,ℓ}**, and DLIN ⇒ MDDH as a reduction function with an
   explicit inequality (design-r2 § 4.1–§ 4.2, unchanged).
2. **Generic FE:**
   - syntax, correctness, the Def 4.3 game and predicates (design-r2 § 4.5);
   - **the semi-adaptive game and predicates**;
   - **the Def 4.3 ⇐ semi-adaptive identity**;
   - **a deterministic oracle run** for reductions (§ 4.4–§ 4.5).
3. **Classes:** `phfeClass`, `quadClass`, and the embedding (design-r2 § 4.6, unchanged).
4. **Partial garbling:** the interface (Lemma 1, corrected) and the layered instance, proved
   (§ 4.7).
5. **Π** and the **quadratic scheme** at k = k' = 2 on a symmetric group, each with its
   **semi-adaptive** inequality (§ 4.8). `wee20PHFE` for `phfeClass` (design-r2 § 4.9).
6. **Headlines:**
   - perfect correctness and Def 4.2;
   - the semi-adaptive core inequality (typed adversaries) and its corollaries for NUPPT oracle
     adversaries;
   - **the Def 4.3 inequality and corollaries** (the GJLS21 target), derived;
   - the ciphertext width;
   - the efficiency targets, the assembled primitives (§ 1E.3) and the primitive-level
     headlines;
   - the L1 link `mddhRealizable_of_preTarget`.

Phase B (not this job):
- word-RAM programs and the RAM bridge;
- proofs of the targets, which make `wee20PHFE … hT` unconditional;
- realisers for the MDDH-level reductions (`Games.exists_handlerMachine`, T1);
- the unconditional corollaries.

## 3. Module layout (replaces design-r2 § 3's table; the other text of § 3 stands)

| File (new) | Contents | Est. lines |
|---|---|---|
| `Pairing/Exponents.lean` | unchanged (design-r2) | 300–500 |
| `Pairing/Linear.lean` | unchanged | 300–500 |
| `Pairing/MatrixDH.lean` (+ `MatrixDH/SelfReduction.lean`) | unchanged: `mddhGame d ℓ`, `mddhEnc d ℓ` (the challenge encoding, for the MDDH-level realisers), `mddhAdv`, `dlinToMddh`, `mddhAdv_le` | 800–1,500 |
| `AdvancedEncryption/FunctionalEncryption.lean` | facade | 40 |
| `…/FunctionalEncryption/Defs.lean` (split at ~600 lines into `Defs.lean` + `Defs/Efficient.lean`) | `FnClass`; `FEScheme.Raw` (core-plus-draw) and `FEScheme` (efficiency fields, § 1E); `honestRun`, `Correct`, `CorrectExcept`; `Simulator.Raw`/`Simulator`; `TwoStage`, `simGame`, `simAdv`, `SimSecureWith`, `SimSecure`, `SubexpSimSecure` | 700–1,150 |
| `…/FunctionalEncryption/SamplerEfficiency.lean` | only if Q-E1 (A) is not at `<BASE>`: `SamplesEfficiently` + readers, for a mechanical move later | 0–120 |
| `…/FunctionalEncryption/Run.lean` | the deterministic oracle run `runDet` and its reader to `simulate` (§ 4.4) | 120–250 |
| `…/FunctionalEncryption/SemiAdaptive.lean` | `saSpec`, `saCodec`, `saImpl` (+ case lemmas), `SAAdv`, `NUPPT.toSAAdv`, `SASimulator.Raw`/`SASimulator`, `saGame`, `saSimAdv`, `SASimSecureWith`, `SASimSecure`, `SubexpSASimSecure`; `TwoStage.toSA`, `SASimulator.Raw.toSim` (+ the efficient form), **`simAdv_eq_saSimAdv`** | 500–900 |
| `…/FunctionalEncryption/Classes.lean` | unchanged | 300–600 |
| `…/FunctionalEncryption/PartialGarbling.lean` | interface: `PartialGarbling.Raw` (§ 4.7) and `PartialGarbling` (efficiency fields, § 1E) | 200–330 |
| `…/FunctionalEncryption/PartialGarbling/Layered.lean` | `layeredPG_raw` and its three properties (§ 4.7); `Wee20.PGTargets`'s statement | 500–1,000 |
| `…/FunctionalEncryption/Wee20/Linear.lean`, `LinearCorrect.lean`, `LinearSecurity/*.lean` | Π (§4.2); correctness (9)–(11); Π's semi-adaptive game and simulator; Games 0–5 typed; two MDDH reduction functions; Theorem 1 inequality | 2,400–4,500 |
| `…/FunctionalEncryption/Wee20/Quadratic.lean`, `QuadraticCorrect.lean`, `QuadraticSecurity/*.lean` | §3.1 scheme; (4)–(5); §3.2 simulator; §3.3 Games 0–4 typed; two MDDH reduction functions; the derived Π adversary | 1,600–2,900 |
| `…/FunctionalEncryption/Wee20.lean` | `wee20PHFE_raw`, `wee20Sim_raw`, `wee20SASim_raw`; headlines on the raw bundles for both notions; corollaries; ct width | 600–1,200 |
| `…/FunctionalEncryption/Wee20/Targets.lean` | the targets of § 1E.3; the assembly (`layeredPG`, `wee20PHFE`, `wee20Sim`, `wee20SASim`, `_toRaw`); `mddhRealizable_of_preTarget`; the primitive-level headlines | 400–700 |
| **Total** | 18–22 new modules + 1 facade, + facade lines in `Pairing.lean` and `AdvancedEncryption.lean` | **≈ 8,800–16,100** |

- **Removed:** `FunctionalEncryption/Realization.lean` (the shared file is at `<BASE>`).
- **Imports.** Add `TCSlib.Cryptography.Asymptotic.Realization` where realisers appear.
- **Import `TCSlib.Cryptography.CoinSampling.Efficiency` only** in the files that state
  sampler-efficiency fields or targets (`Defs`, `SemiAdaptive`, `PartialGarbling`, `Wee20/Targets`,
  `SamplerEfficiency` if local). Use it only for the types `UniformSampler` and
  `CoinSampler.fail` (§ 1E.2), with `Contract` if Q-E1 (A) is at `<BASE>`.
- **Do not import:** any other `CoinSampling` module, `Games.Closeness`,
  `Pairing/Assumptions.lean` (unchanged rule), `TCSlib/Programs/*`,
  `TCSlib/Complexity/RAMSimulation/*`.

## 4. Statement shapes

§ 4.1 (DLIN), § 4.2 (MDDH and the self-reduction), § 4.3 (exponent vectors), § 4.6 (classes),
§ 4.9 (`wee20PHFE`, now named `wee20PHFE_raw`: the raw bundle, § 1E) are **unchanged from
design-r2**, except that § 4.2's `mddhAdv_le` reads its realisers through the shared predicate
(as written there). § 4.11 is replaced below.

### 4.4 Reduction functions and realisers (replaces design-r2 § 4.4)

**The shared predicate (must-reuse; at `<BASE>`).** Names are `Complexity.NUPPT.*`; lines are at
`cdc0934f`. Body: `B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`.

| Item | Line |
|---|---|
| `RealizesOn` | 96 |
| `realizesOn_iff` | 103 |
| `RealizesOn.coins_eq`, `.runAtL_eq` | 113, 118 |
| `.runAt_eq`, `.distinguisherL_eq` (verdict) | 124, 132 |
| `.runAt_coinsEquivPoly_symm` | 141 |
| `realizesOn_of_forall`, `RealizesOn.congr` | 149, 157 |
| `realizesOn_self`, `realizesOn_self_take` | 167, 179 |
| `exists_realizesOn_of_preTarget(_id)` | 220, 239 (Phase B; not used in Phase A) |

- **The body constrains only encoded challenges and coin strings of the layout's length.** It is
  weaker than r2's draft (every coin string). The statements are unchanged, every "∀ realiser"
  theorem is at least as strong, and realisability is easier.
- The docstrings of the core theorems and of the realisability `Prop`s say so in one sentence
  (deviation D-R).
- Read realisers only through the readers (Rule 10).

**Two levels of reductions.**

| Level | Assumption | Reduction function | Realiser hypothesis | Phase B route |
|---|---|---|---|---|
| L1 | DLIN | `dlinToMddh G hp d ℓ D ω` (design-r2 § 4.2): one activation of the NUPPT MDDH distinguisher `D` on a pre-processed DLIN challenge, `fun κ x r => D.runAtL κ (pre κ (ω κ) x) (r.take (D.coinLen κ))` | `B.RealizesOn G.dlinEnc D.coins (dlinToMddh … D ω)` | `exists_realizesOn_of_preTarget_id` (single activation, φ = id) |
| L2 | MDDH^{d}_{2,ℓ} (four instances, § 4.8) | `XRed 𝒜 ω κ x r`: **run the adaptive adversary 𝒜 on coins r against deterministic answers** computed from the MDDH challenge x and the advice ω κ, and return its bit (below) | `D.RealizesOn (G.mddhEnc d ℓ) 𝒜.coins (XRed 𝒜 ω)` | `Games.exists_handlerMachine` (T1, `Games/Efficiency.lean:332`), with handler seed length 0 and ω κ in the handler's initial state |

The headlines compose the two levels (§ 4.10).

**The L2 shape.** Wee20's hops run an adversary that asks keys adaptively, so a reduction is no
longer one activation of the adversary. Its typed form:
```lean
/-- Run the oracle computation `c` against the deterministic stateful handler `h` from state `s`,
for at most `q` moves; the same move semantics as `Games.buildComp` (defined by recursion on `q`,
mirroring `buildComp`'s next-move function). -/
def runDet {ι σ α} {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (timeout : α)
    (h : σ → (i : ι) → spec.dom i → spec.rng i × σ) : ℕ → QueryLog spec → σ → α × σ
/-- Reader: a deterministic handler's simulation is a point mass at `runDet`. This is exactly
the hypothesis shape of `Games.exists_handlerMachine` (`simulate (H.impl …) (A.toCompOn …) s₀ =
.pure (a, s)`). -/
theorem simulate_buildComp_detImpl_eq_pure … :
    simulate (detImpl h) (buildComp next timeout q hist) s =
      .pure (runDet next timeout h q hist s)
```
- `XRed 𝒜 ω κ x r := (runDet (𝒜.next κ (𝒜.input …) r) … (XHandler κ (ω κ) x) (𝒜.budget κ) []
  (XInit κ (ω κ) x)).1`, read as the one-bit verdict.
- `XHandler` answers challenge and key queries by **deterministic** Lean functions of the MDDH
  challenge `x` and the advice. The per-query randomness of the hybrid (T_j, R_j, the
  garbling coins, the outer scheme's s's) is hardwired in `ω κ`, indexed by the query number
  `j < q(κ)`.
- **Reductions never sample.** ω* is fixed by averaging (`exists_expect_sample_le`,
  `abs_expect_sub_le_expect`), as in design-r2 § 4.4.
- **Search before defining `runDet`.** At `cbce64d1`, no deterministic interpreter exists in
  `Games/` (`git grep` for `runDet`, `evalDet`, `detRun`, `runWith`: none). The nearest are
  `Games.buildComp` (`Games/Machines.lean:112`) and `PolyHandler.impl` (`Efficiency.lean:287`).
  Disclose the helper with its searches. If a later `<BASE>` has an equivalent, reuse it.

**Advice.** Each `XAdvice κ` is a finite type, inhabited at every κ, with an explicit encoding
and a `PolyExpr` length bound. It is over `ZMod (p κ)` and cast into the drawn group's `ZMod`
through `hp` (design-r2 § 4.4). It contains:
- the matrices and exponents Wee20's reductions sample;
- q(κ) per-query blocks;
- for the outer hops, the Π-level advice of the derived Π adversary (§ 4.8).

**R-DLOG (binding, new).** Lean can compute discrete logarithms (a finite group). A reduction's
pre-processing or handler that used one would be unrealisable by a PPT machine, and Phase B would
fail. So **no reduction function, handler, simulator or honest algorithm may invert
exponentiation**:
- no `Function.invFun` or `Classical.choose` on `pow_val_bijective*`;
- no `exists_pow_eq` witness;
- no `ZMod`-valued function of a group element.

Group elements are only multiplied, exponentiated by known scalars and paired. **Games** (the
challenger's definitions) may define values through the exponent where the paper's challenger
does; even there, [Wee20]'s leaks are computable by group operations (§ 4.8, Π's leak). The
statements gate checks this rule by grep and by reading.

**Vacuity rule (binding, new).** Realisability hypotheses quantify only over adversaries that
come from machines. These are `NUPPT.toSAAdv A q` for oracle NUPPTs `A`, and `TwoStage.toSA A q`
for Def 4.3 pairs. They **never quantify over all typed adversaries `SAAdv`**: a typed
adversary can be any Lean function, so "every typed adversary's reductions are realisable" is
false, and a corollary assuming it would be vacuous. The core inequalities are stated for every
typed adversary; only the corollaries' realisability hypotheses are restricted.

### 4.5 Generic FE: Def 4.3, the semi-adaptive notion, and the derivation (replaces design-r2 § 4.5's game paragraphs; its `FnClass`, `FEScheme`, correctness and Def 4.3 `Simulator`/`simGame`/`simAdv`/`SimSecure` text stands, with Q1 A)

**The semi-adaptive notion** ([Wee20, §2.2, p. 5] = [AGW20, §4.1, p. 11] at N = 1; Wee20 cites
Chen–Wee [9]):
```lean
/-- Oracles of the semi-adaptive game: 0 = the challenge (x*, z*), answered once by ct*;
1 = KeyGen, answered after the challenge (⊥ before it, as Wee20's adversary gets the KeyGen
oracle only with ct*). Bit-string oracles (`bitSpec`), as `IBEScheme.sidSpec`. -/
abbrev saSpec (κ : ℕ) : OracleSpec (Fin 2) := bitSpec (S.saIn κ) (S.saOut κ)
/-- A typed semi-adaptive adversary with a query budget: coin polynomial `coins`, budget `budget`,
and, at each κ, an oracle computation from the encoded (pp, mpk) and its coins. -/
structure SAAdv (S) where
  coins : PolyExpr
  budget : PolyExpr
  run : (κ : ℕ) → List Bool → (Fin (coins.eval κ) → Bool) → OracleComp (S.saSpec κ) Bool
/-- An oracle NUPPT as a semi-adaptive adversary (`NUPPT.toCompOn` with `S.saCodec κ`, as
`IBEScheme.sidGame` runs `A.toComp`). -/
def _root_.Complexity.NUPPT.toSAAdv (A : NUPPT) (q : PolyExpr) : S.SAAdv
/-- The semi-adaptive simulator [Wee20, §2.2]: Setup*, Enc*(msk*, x*), KeyGen*(msk*, x*, f, λ)
with λ the leak (stateful). -/
structure SASimulator (Λ : (κ : ℕ) → S.Pub κ → Type) where
  St : ℕ → Type
  setup : (κ : ℕ) → (pp : S.Pub κ) → ProbComp (S.MPK κ × St κ)
  enc   : (κ : ℕ) → (pp : S.Pub κ) → St κ → S.PubIn κ pp → ProbComp (S.CT κ × St κ)
  key   : (κ : ℕ) → (pp : S.Pub κ) → St κ → S.PubIn κ pp → S.Fn κ pp → Λ κ pp →
            ProbComp (S.SK κ × St κ)
noncomputable def saGame (Sim) (leak) (𝒜 : S.SAAdv) (ideal : Bool) (κ : ℕ) : ProbComp Bool
noncomputable def saSimAdv (Sim) (leak) (𝒜) (κ) : ℝ := advantage (saGame … false κ) (saGame … true κ)
/-- [Wee20, §2.2]: semi-adaptive simulation security against oracle NUPPT adversaries with any
polynomial query budget. -/
def SASimSecure (leak) : Prop :=
  ∃ Sim, ∀ (A : NUPPT) (q : PolyExpr), Negligible (S.saSimAdv Sim leak (A.toSAAdv q))
def SubexpSASimSecure (leak) : Prop :=
  ∃ Sim, SubexpHard fun (Aq : NUPPT × PolyExpr) => S.saSimAdv Sim leak (Aq.1.toSAAdv Aq.2)
```
- **Rule 15 reading of this block (§ 1E.1).**
  - The structure shown as `SASimulator` is `SASimulator.Raw`.
  - `SASimulator` extends it with efficiency fields.
  - `saGame`/`saSimAdv` take raw simulators.
  - `SASimSecure`/`SubexpSASimSecure` quantify over efficient ones, with `SASimSecureWith` for a
    given raw simulator.
  - The same holds for `Simulator` and `SimSecure` (Def 4.3), and the game is over
    `FEScheme.Raw`.
- `saGame`, step by step:
  - pp ← pubGen;
  - real: (mpk, msk) ← setup; ideal: (mpk, st) ← Sim.setup;
  - r ← uniform `Fin (𝒜.coins.eval κ) → Bool`;
  - `simulate (saImpl …) (𝒜.run κ ⟨encPub pp, encMPK mpk⟩ r) init`, and output the bit.
- `saImpl` decodes the challenge (fixed width, residues mod the drawn order), as design-r2's
  Def 4.3 game decodes A₁'s output. It has case lemmas and `_onSpec` readers, as `IBEScheme`
  does.
- **The leak.** For the outer PHFE, `leak = eval` with values in `ZMod (order)`: µ = h(z*)f(x*)^⊤
  [Wee20, §2.2], Q1 (A).
- **The budget** is Wee20's "unbounded keys" made polynomial, as `IBEScheme.SIDSecure` quantifies
  `q : PolyExpr`. It is needed anyway: [Wee20, Lemma 4]'s MDDH^n_{k,mQ} has Q = the number of
  keys.

**The derivation of [GJLS21, Definition 4.3]** (G3; the "special case" of ruling Q3):
```lean
/-- A Def 4.3 pair as a semi-adaptive adversary: ignore mpk for A₁; run A₁ on 1^κ (its coins
first); ask the challenge (x*, y*); ask the committed keys f_1, …, f_q in order; run A₂ on
⟨st, ⟨pp, pk, sk_1, …, sk_q, x*, ct*⟩⟩ (its coins second). Coins A₁.coins + A₂.coins, budget
q + 1. -/
def TwoStage.toSA (A : TwoStage) (q : PolyExpr) : S.SAAdv
/-- Setup~ = Setup*, Enc~(td, ω) = Enc*(td, x*), KeyGen~(td, f_j, ω) = KeyGen*(td, x*, f_j, µ_j). -/
def SASimulator.toSim (Sim : S.SASimulator Λ) (leak) : S.Simulator
/-- **Definition 4.3 is the special case** (any scheme, any semi-adaptive simulator):
the Def 4.3 advantage of a two-stage adversary equals the semi-adaptive advantage of its
semi-adaptive form. -/
theorem simAdv_eq_saSimAdv (Sim) (A : TwoStage) (q : PolyExpr) (κ : ℕ) :
    S.simAdv (Sim.toSim eval) A q κ = S.saSimAdv Sim eval (A.toSA q) κ
```
- **Proof sketch.**
  - A₁'s activation does not depend on pp or on the setup coins, so it commutes to the front
    (`expect_sample_comm`, `expect_expect_sample`).
  - The derived adversary makes exactly q + 1 queries, so `simulate` unrolls finitely
    (`simulate_bind`, `saImpl`'s case lemmas).
  - The coin string splits into A₁'s and A₂'s halves (`finSumFinEquiv`, `expect_sample_equiv`).
  - Real matches real; ideal matches ideal with `toSim`.
- Corollary: `SASimSecure eval → (∀ A q, … realisers …) → SimSecure` is **not** stated as an
  abstract implication: that would need an oracle machine built from (A₁, A₂), a Phase B
  construction. The headlines instead apply the semi-adaptive **core inequality** (for every
  typed adversary) to `A.toSA q` and rewrite with `simAdv_eq_saSimAdv` (§ 4.10).

### 4.7 Partial garbling (replaces design-r2 § 4.7)

**The interface** ([Wee20, Lemma 1, §4.1, pp. 8–9] = [AGW20, Lemma 2, §4.2, p. 12]; shapes per
[AGW20, App. A, (32), p. 38]; reading W1):
```lean
/-- A partial garbling scheme for `z f(x)^⊤`, `f` in a class `Fn` of maps ℤ_p^ℓ → ℤ_p^{n'},
affine in `x` [Wee20, Lemma 1]. Index types are finite and explicit: `MIdx f` (m) and the
randomness `TIdx f ⊕ Fin n'`, whose `inr` part is t̲ ("the last n' entries"). -/
structure PartialGarbling (p ℓ n' : ℕ) (Fn : Type) where
  MIdx TIdx : Fn → Type   -- [Fintype], [DecidableEq]
  m₀ : (f : Fn) → MIdx f   -- the coordinate e₁ of pgb*
  eval : Fn → (Fin ℓ → ZMod p) → Fin n' → ZMod p
  /-- lgen: L₁ ∈ ℤ_p^{t×mn}, L₀ ∈ ℤ_p^{t×m} (corrected shapes, W1). -/
  L₁ : (f : Fn) → Matrix (TIdx f ⊕ Fin n') (Fin ℓ × MIdx f) (ZMod p)
  L₀ : (f : Fn) → Matrix (TIdx f ⊕ Fin n') (MIdx f) (ZMod p)
  rec : (f : Fn) → (Fin ℓ → ZMod p) → (Fin n' ⊕ MIdx f) → ZMod p
  rec_spec : ∀ f x z t, pgb f x z t ⬝ᵥ rec f x = z ⬝ᵥ eval f x       -- reconstruction
  privacy : ∀ f x z (g : (Fin n' ⊕ MIdx f → ZMod p) → ℝ),
    expect (sample _) (g ∘ pgb f x z) = expect (sample _) (g ∘ pgb' f x (z ⬝ᵥ eval f x))
```
- **`pgb` and `pgb'` (pgb*) are definitions beside the structure,** with `_eq` readers, fixed by
  L₀ and L₁ exactly as Lemma 1 writes them:
  - `pgb f x z t = Sum.elim (z − t̲) (t ᵥ* (L₁ f * (xᵀ ⊗ₖ I) + L₀ f))`;
  - `pgb'` is the same with `−t̲`, plus `µ` at `m₀ f`.

  Because pgb is a definition, the syntax (affine in x, linear in t) is not a field, so an
  instance cannot cheat on it.
- The `Fin 1` index of `xᵀ ⊗ₖ I` (Mathlib's `kroneckerMap`) is Codex's to tidy, with
  disclosure.
- **Privacy is exact**: an equality of laws, stated through `expect` for every test function
  ([IW14, Def 1]: "identically distributed"; [AGW20, App. A]). Wee20's ≈_s is the weaker
  reading R4. So [Wee20, Lemma 5] becomes an identity, and Π's slack has no q·δ term.
- **A group-lifted reader** (a lemma, not a field): `[pgb' f x µ t]` is computed from `[µ]` by
  group operations (`expVec` of `pgb' f x 0 t` times `[µ]` at `m₀`). This is what Π's KeyGen*
  needs under R-DLOG.
- r2's δ parameter is dropped.
- **Rule 15:** the structure above is `PartialGarbling.Raw`. `PartialGarbling` extends it with
  `lgen_eff` and `rec_eff` (§ 1E.1), since Lemma 1 asks for "four efficient algorithms".

**The instance** (`PartialGarbling/Layered.lean`): `layeredPG_raw p ℓ n' d : PartialGarbling.Raw …` (rule 15: the efficient `layeredPG hT` is assembled in `Wee20/Targets.lean`, § 1E.3) for `Fn` = coefficient
tensors `C : Fin n' → (Fin d → Fin (ℓ+1)) → ZMod p`, eval `f_j(x) = Σ_τ C j τ ∏_i x̂ (τ i)` (the
`quadClass` representation of design-r2 § 4.6, x̂ = (x, 1)).
- **Source:** [AGW20, App. A, (28)–(32), pp. 37–38] on the layered ABP Γ_C, the case t = 1 of
  [IW14, §4.2, Theorem 3]; see `sources-r3.md` § 3.
- **Index types:**
  - `MIdx = Σ k : Fin (d + 1), (Fin k → Fin (ℓ+1))` (the nodes v₀ = the empty tuple, …, the
    d-tuples); `m₀ = ⟨0, Fin.elim0⟩`;
  - `TIdx = Σ k : Fin d, (Fin (k + 1) → Fin (ℓ+1))` (all nodes but v₀, the output nodes and v₁).
  - Then m = Σ_{k≤d}(ℓ+1)^k and t = m + n' − 1, depending on (ℓ, d, n') only.
- **L₀ and L₁** are the explicit matrices of (32):
  - L₁ block `i` has a 1 at (child `u·i`, column (i, u));
  - L₀ has 1 at (`u·last`, u), −1 at (u, u) for u ≠ v₀, and `C j τ` at (output node j, τ).

  Children use `Fin.snoc`, with `Fin.castSucc i` for x_i and `Fin.last ℓ` for the constant 1.
- **Proofs, by path sums** (disclosed route deviation from AGW20's determinant argument; the
  statements are AGW20's):
  - `rec f x` is the forward path value: `∏_{i<k} x̂ (u i)` at node u, and `f_j(x)` at output
    node j.
  - `rec_spec`: the sum telescopes, because each node's forward value is the label-weighted sum
    of its parents' (`Fintype.sum_sigma`, `Fin.snoc` readers, `Fin.prod_univ_castSucc`).
  - `privacy`: the backward path value `s` (s_j = z_j; s_τ = Σ_j C j τ · z_j at depth d;
    s_u = Σ_a x̂ a · s_{u·a}) satisfies `pgb f x z t = pgb' f x (s v₀) (t − s)` and
    `s v₀ = z ⬝ᵥ eval f x`. The translation is a bijection (`expect_sample_equiv`,
    `Equiv.addRight`).
  - No determinant, no ABP datatype, no [IK02] lemma.
- **Size:** interface 150–250; instance 500–1,000 (r2: 1,200–2,500 for both). The general ABP
  instance (determinant route) is a documented extension (§ 9).

### 4.8 Π and the quadratic scheme, semi-adaptive (replaces design-r2 § 4.8's security bullets; the scheme, correctness and simulator text stands)

**Π's semi-adaptive game** ([Wee20, §4, p. 8; §2.2]).
- Π's keys carry a **group matrix** [M]₂ ([Wee20, §4]: "the matrix [M]₂ is specified by the
  function corresponding to the secret key … decryption only gets [M]₂ and not M").
- So Π does **not** instantiate the generic `FEScheme`, whose functions live over ℤ_p. It gets
  its own `Linear.SAAdv`, `Linear.saGame` and `Linear.saSimAdv`, written to the generic
  definitions' shape (§ 4.5) and documented as such. Codex may generalise `FnClass` to
  pp-dependent functions instead, if that is cheap, with disclosure.
- **The game:** pp ← G; (mpk₀, msk₀) ← Setup; the adversary gets (pp, mpk₀); it commits to
  (x*, z*) in the clear; it gets ct*; it asks (f_j, [M_j]₂) adaptively, up to q(κ) times.
- **Π's leak** to KeyGen* is [z*M_j f_j(x*)^⊤]₂ = ∏_{a,b} ([M_j]_{ab})^{z*_a f_{j,b}(x*)}: group
  operations only (R-DLOG).

**Theorem 1, semi-adaptive** ([Wee20, App. B, Thm 1, Lemmas 2–5, pp. 12–14]; analogue
[AGW20, Thm 2, Lemmas 3–7, pp. 15–18]), for **every typed** Π adversary `𝒜` with budget `q`:
```lean
theorem linear_saSimAdv_le (p) (hp) (𝒜 : Linear.SAAdv …) :
    ∃ ω : (i : Fin 2) → ∀ κ, Linear.Advice … i κ, ∀ D : Fin 2 → NUPPT,
      (D 0).RealizesOn (G.mddhEnc 1 3) 𝒜.coins (Linear.red₀ 𝒜 (ω 0)) →     -- Lemma 2
      (D 1).RealizesOn (G.mddhEnc ℓ (m * q)) 𝒜.coins (Linear.red₁ 𝒜 (ω 1)) → -- Lemma 4
      ∀ κ, Linear.saSimAdv … 𝒜 κ ≤
        G.mddhAdv 1 3 (D 0) κ + G.mddhAdv ℓ (m * q) (D 1) κ + linearSlack G p κ
```
- **Lemma 2** (Game 0 ≈ 1, MDDH¹_{2,3}): W, U, V are hardwired; the keys are answered from them.
- **Lemma 3 (Game 2 ≡ 3, adaptive).** Wee20 argues the identity for fixed (x*, z*), then extends
  it to adaptive choices "via a random guessing argument" (p. 14). **r3 replaces the guessing
  argument by an exact change of variables:**
  - (U, W, V) ↦ (U + a^⊥Δ_U, W + a^⊥Δ_W, V + a^⊥Δ_V), with Δ's depending on (x*, z*) only.
  - A^⊤a^⊥ = 0, so the shift fixes the public part (A^⊤U, A^⊤W, A^⊤V) that (x*, z*) may
    depend on. The map is therefore a bijection for fixed (A, c) and adversary coins: its
    inverse subtracts the same Δ.
  - Likewise per key query, T_j ↦ T_j + a^⊥(…), inside the oracle implementation
    (`expect_sample_equiv` per query, coupled by `expect_simulate_rel`).
  - The only loss is the full-rank event of (A | c): `linearSlack`, explicit over the drawn
    order (Wee20's 1/p; `Matrix.card_GL_field` gives an exact form).
  - This is a disclosed proof-route deviation with the same statement.
- **Lemma 4** (Game 3 ≈ 4, MDDH^ℓ_{2,mq}): the reduction reads all q blocks R_j from the MDDH
  challenge up front and answers the j-th adaptive query with block j. Here m is the layered
  instance's m, which is independent of f, so Wee20's "same m" assumption holds.
- **Lemma 5** (Game 4 ≡ 5): exact, by the change of variables û_j ↦ û_j − t̲_jL_{1,j} and the
  interface's exact privacy. There is no slack term.

**The quadratic scheme, semi-adaptive** ([Wee20, §3.3, pp. 7–8]), for every typed outer
adversary `𝒜` (generic `SAAdv` of the quadratic scheme), Games 0–4:
- **Game 0 → 1 (by Π's inequality).**
  - Average over the outer reduction's own randomness (A₁, A₂, s₁, s₂), fixing ω₀ by
    `exists_expect_sample_le`.
  - The **derived Π adversary** `𝒜'(𝒜, ω₀)` is a typed `Linear.SAAdv` with coins `𝒜.coins` and
    budget `𝒜.budget`. It does the following:
    - builds mpk from (pp, mpk₀) and ω₀;
    - runs 𝒜;
    - commits Π's challenge (x*, s₁ ⊗ z*₂ ‖ (s₁A₁ + z*₁) ⊗ s₂) in the clear, as Wee20's
      reduction sends it (p. 7);
    - returns ct = ([y₁], [y₂], ct₀);
    - forwards each key query f as (f, [M]₂).
  - Then `linear_saSimAdv_le` at 𝒜' bounds the gap. The outer advice includes Π's advice for
    𝒜'.
- **Game 2 ≡ 1** by identity (5).
- **Game 3** (MDDH¹_{2,n} on A₁; symmetric bilateral 2-Lin): z*₁ is added in the exponent
  after the commitment. This is adaptive-safe, as Wee20 notes ("even if z*₁ is adaptively chosen
  after seeing [A₁]").
- **Game 4** (MDDH¹_{2,n} on A₂).
- The outer simulator ([Wee20, §3.2]) computes g^µ from µ ∈ ℤ_p, then [(y₁ ⊗ y₂)f(x*)^⊤] ·
  [µ]^{−1} (reading W4), with group operations only.

Total: **four MDDH-level reductions** (Π: 2; outer: 2), each composed with `dlinToMddh` at L1.
This is the count r2 named; Codex fixes it at M0.

### 4.10 Headlines (replaces design-r2 § 4.10)

**On the raw bundles** (rule 15, § 1E). The core inequalities are about `wee20PHFE_raw` with
the raw simulators, for any raw garbling scheme `PG`:
```lean
/-- THE CORE INEQUALITY, semi-adaptive [Wee20, §3, p. 6; §3.3], for every typed adversary. -/
theorem wee20PHFE_saSimAdv_le (p) (hp) (𝒜 : (wee20PHFE_raw G PG ℓ n d).SAAdv) :
    ∃ ω : (i : Fin 4) → ∀ κ, Wee20Advice G p ℓ n d 𝒜 i κ, ∀ D : Fin 4 → NUPPT,
      (∀ i, (D i).RealizesOn (G.mddhEnc (dimD i) (dimL i)) 𝒜.coins (wee20Red … 𝒜 i (ω i))) →
      ∀ κ, (wee20PHFE_raw G PG ℓ n d).saSimAdv (wee20SASim_raw …) eval 𝒜 κ ≤
        ∑ i, G.mddhAdv (dimD i) (dimL i) (D i) κ + wee20Slack G ℓ n d p κ
/-- Def 4.3 form (the GJLS21 target), for two-stage adversaries: by `simAdv_eq_saSimAdv`. -/
theorem wee20PHFE_simAdv_le (p) (hp) (A : TwoStage) (q : PolyExpr) : … (same, at A.toSA q,
    with `wee20Sim_raw`)
/-- Phase B obligations (realisability), restricted to machine-derived adversaries (§ 4.4). -/
def Wee20RealizableSA (G p hp ℓ n d) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr) i ω, ∃ D : NUPPT,
    D.RealizesOn (G.mddhEnc (dimD i) (dimL i)) A.coins (wee20Red … (A.toSAAdv q) i ω)
def Wee20Realizable43 (G p hp ℓ n d) : Prop :=
  ∀ (A : TwoStage) (q : PolyExpr) i ω, ∃ D : NUPPT,
    D.RealizesOn (G.mddhEnc (dimD i) (dimL i)) (A.toSA q).coins (wee20Red … (A.toSA q) i ω)
def MDDHRealizable (G p hp d ℓ) : Prop :=
  ∀ (D : NUPPT) ω, ∃ B : NUPPT, B.RealizesOn G.dlinEnc D.coins (dlinToMddh G hp d ℓ D ω)
/-- Raw-simulator forms (the raw bundle with its raw simulator). -/
theorem wee20PHFE_raw_saSimSecureWith (p hp) (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : Wee20RealizableSA …)
    (hM : ∀ i, MDDHRealizable G p hp (dimD i) (dimL i)) (h : G.DLINAssumption) :
    (wee20PHFE_raw G PG ℓ n d).SASimSecureWith (wee20SASim_raw …) eval
theorem wee20PHFE_raw_simSecureWith (p hp hpb) (hR : Wee20Realizable43 …) (hM …)
    (h : G.DLINAssumption) : (wee20PHFE_raw G PG ℓ n d).SimSecureWith (wee20Sim_raw …)
-- and the `Subexp` forms under `G.SubexpDLIN`
```

**On the primitives** (assembled from targets, § 1E.3): the library-level statements, where the
simulator's existence includes its efficiency.
```lean
theorem wee20PHFE_simSecure (p hp hpb) (hT : Wee20.Targets G ℓ n d) (hR : Wee20Realizable43 …)
    (h : G.DLINAssumption) :
    (wee20PHFE G ℓ n d hT).SimSecure            -- [GJLS21, Def 4.3], ε = 1, many-key
theorem wee20PHFE_subexpSimSecure … (h : G.SubexpDLIN) : (wee20PHFE G ℓ n d hT).SubexpSimSecure
theorem wee20PHFE_saSimSecure (p hp hpb) (hT) (hR : Wee20RealizableSA …) (h : G.DLINAssumption) :
    (wee20PHFE G ℓ n d hT).SASimSecure eval
theorem wee20PHFE_subexpSASimSecure … (h : G.SubexpDLIN) : … .SubexpSASimSecure eval
/-- [GJLS21, §9]'s PHFE ingredient: correct (Def 4.2), simulation secure (Def 4.3, ε = 1,
many-key), linear efficiency (Def 4.6). -/
theorem wee20PHFE_gjls21 (p hp hpb) (hT) (hR) (h) :
    (wee20PHFE G ℓ n d hT).CorrectExcept 0 ∧ (wee20PHFE G ℓ n d hT).SimSecure ∧
      Wee20.LinearEfficient G ℓ n d
```
- At the primitive level, `hM` is discharged by `mddhRealizable_of_preTarget` from `hT`'s
  `MddhPreTargets`, so it is not a hypothesis. `hR` (the L2 realisers) stays a Phase B
  hypothesis.
- `wee20PHFE_correct`, `wee20PHFE_correctExcept` and `wee20PHFE_ctLen_eq` are unchanged
  (design-r2 § 4.10), on the raw bundle. Readers transfer them to the primitive through
  `wee20PHFE_toRaw`.
- **`wee20Slack`** is explicit: Π's full-rank term plus the four `mddhSlack` terms after
  composition. There is **no partial-garbling term** (exact privacy). It is `SubexpSmall c` for
  c < 1 under `hpb`, as r2 described.
- **Composition.** Each corollary composes the core inequality with `mddhAdv_le` per `D i` (L1).
  The subexponential exponent is uniform because there are four hops (r2's argument).
- **The `Phase B` docstring note** on `hR`: L2 via `Games.exists_handlerMachine`. Realising
  `TwoStage.toSA` needs a machine that runs A₁ then A₂ as one oracle machine, which is also
  Phase B.

### 4.11 Efficiency statements (replaces design-r2 § 4.11)

Under rule 15 the written efficiency `Prop`s of design-r2 § 4.11 are no longer free-standing.
They are the **targets** of § 1E.3, which inhabit the primitives, plus `Wee20.LinearEfficient`
([GJLS21, Def 4.6]). Each target is a named `Prop` with an `_iff` reader and the docstring
"Phase B obligation; not proved in this development". There is no `sorry`, and no target is a
hypothesis of a raw-bundle theorem.

## 5. Proof plan (replaces design-r2 § 5's table)

| Step | Statement | Source | Kind |
|---|---|---|---|
| P1 | DLIN ⇒ MDDH^d_{2,ℓ} (`mddhAdv_le`) | [Wee20, §2.1] citing [EHKRV13] | reduction function + statistics (unchanged) |
| P2 | layered partial garbling: `rec_spec`, exact `privacy` | [AGW20, App. A, (28)–(32)]; [IW14, Def 1, §4.2] | path sums + translation |
| P3 | Π correctness | [Wee20, §4.2, (9)–(11)] | algebra |
| P4 | Π semi-adaptive inequality | [Wee20, Thm 1, Lemmas 2–5]; [AGW20, Thm 2, Lemmas 3–7] | typed hops over oracle runs, 2 MDDH reductions; Lemma 3 by the public-part-preserving bijection |
| P5 | quadratic correctness | [Wee20, §3.1, (4)–(5)] | algebra |
| P6 | quadratic semi-adaptive inequality | [Wee20, §3.3] | derived Π adversary + 2 MDDH reductions |
| P7 | class embedding, `wee20PHFE` correctness | [GJLS21, §9]; G2 | identity |
| P8 | `simAdv_eq_saSimAdv` and the Def 4.3 inequality | [GJLS21, Def 4.3]; [Wee20, §2.2]; G3 | game identity |
| P9 | corollaries, both notions | [GJLS21, Remark 4.5]; #374 | asymptotics |

- **Oracle-game hops.** Real/ideal oracle couplings use `expect_simulate_rel`,
  `prob_simulate_rel` and `expect_sample_rel` (`Games/Relational.lean:85, 111, 130`).
- **Hop to reduction.** Each computational hop is: typed game gap = the typed MDDH advantage of
  the reduction's run (`runDet` reader), then the verdict lemma (`RealizesOn.distinguisherL_eq`).

## 6. Milestones and size (replaces design-r2 § 6)

| M | Content | Push | Est. lines |
|---|---|---|---|
| **M0** | **Statements commit.** Contents:<br>- every new file with its definitions and readers (readers proved), **including the raw/primitive splits, the efficiency fields, the targets and the assembly definitions**;<br>- every theorem stated with `sorry` under its sketch;<br>- in REPORT, the fidelity table (GJLS21 Defs 4.1–4.3, 4.6, §9 first; then Wee20 §2.2 and the Wee20/AGW20/IW14 table);<br>- **the rule-15 table** (each interface, its efficiency fields, its raw bundle, the targets that inhabit it);<br>- facade lines and a size re-estimate | checkpoint 0 | 2,500–3,700 (inside the totals) |
| M1 | Exponents; DLIN; MDDH; P1 | checkpoint 1 | 1,400–2,500 |
| M2 | generic FE (raw and efficient forms): Def 4.3 readers, `runDet`, the semi-adaptive notion, P8; classes, P7's identity; partial garbling: interface (both forms) and the layered raw instance (P2) | checkpoint 2 | 2,400–4,300 |
| M3 | Π: P3, P4 (semi-adaptive) | checkpoint 3 | 2,400–4,500 |
| M4 | quadratic: P5, P6 (semi-adaptive) | checkpoint 4 | 1,600–2,900 |
| M5 | `wee20PHFE_raw`, headlines for both notions on the raw bundle, P9, ct width; **the targets, the assembly, `mddhRealizable_of_preTarget`, the primitive-level headlines**; final checks | final | 1,000–1,900 |
| | **Total** | | **≈ 8,800–16,100 (central ≈ 12,000)** |

- **Against r2 (7,400–13,800).**
  - Q3 (B) adds ≈ +1,300–2,500: the semi-adaptive notion and `runDet` (+600–1,050), adaptive Π
    hops (+400–800), the adaptive outer hops and derived Π adversary (+300–600), and the second
    set of headlines (+200–400).
  - **Rule 15 adds ≈ +700–1,200**: the raw/primitive splits of `FEScheme`, both simulators and
    `PartialGarbling`; the targets; the assembly; and the L1 link.
  - The layered instance saves ≈ −700 to −1,500 (500–1,000 against 1,200–2,500).
  - The shared realisation file saves 0–150.
- **Overrun.** A PARTIAL final (Q4 A) carries:
  - all statements;
  - every proved declaration, standard-axiom-only;
  - the remaining sorries listed;
  - a continuation note.

  Suggested order of value if time is short: M0, M2 (garbling, notions), M3, M1, M4, M5.

**Statements-gate order (binding).**
1. Source fidelity ([GJLS21] Defs 4.1–4.3, 4.6, §9; then [Wee20], [AGW20], [IW14] items and
   pages).
2. **Definitions carry efficiency (rule 15).** Checks:
   - each of `FEScheme`, `Simulator`, `SASimulator` and `PartialGarbling` has its efficiency
     fields in uniform form only (§ 1E.2);
   - no bare `∃ A : NUPPT, A.Computes f`;
   - no value of those types is constructed except by the assembly from targets;
   - the raw bundles carry the correctness and security theorems;
   - the targets together inhabit every primitive the job constructs.
3. Then the rest: R-DLOG, the vacuity rule, Rule 10, statement shapes.

## 7. Questions

### 7.1 Settled since r2

| r2 | Ruling (decision-log row) | Consequence |
|---|---|---|
| Q1 simulator input | (A) µ ∈ ℤ_p (*first batch*) | § 0; disclosed deviation; Π gets g^µ |
| Q2 partial garbling | (A) interface + proved instance (*first batch*; sources received) | § 4.7; `sources-r3.md` § 3 |
| Q3 notion per layer | Wee20's semi-adaptive SIM for both layers, Def 4.3 derived (*second batch*) | §§ 4.4, 4.5, 4.8, 4.10 |
| Q4 one job or two | (A) one job, PARTIAL final allowed (*first batch*) | § 6 |
| Q5 home of `RealizesOn` | (A) shared `Asymptotic/Realization.lean` (*first batch*; *Shared … written*) | § 4.4, must-reuse |

r2's table of r1 questions settled stands, with Q11 amended as § 0 says.

| (new) efficiency in definitions | rule 15 (*Efficiency is mandatory*; *Efficiency baked into definitions*) | § 1E; the gate order (§ 6) |

### 7.2 Open (multiple choice, recommended first)

- **Q-E1. Where `SamplesEfficiently` lives** (the same question as the sPRG pack's Q-E1; rule
  them together). Both jobs state sampler efficiency with one shape (sPRG design-r3 § 1.2), and
  parallel definitions would be a duplication.
  - **(A)** One shared in-house file, written by the maintainer before dispatch and stacked into
    `<BASE>`, as the realisation file was: `TCSlib/Cryptography/CoinSampling/Contract.lean`
    (`SamplesEfficiently` and readers, ≈ 60–120 lines, on #378). Both jobs reuse it
    (must-reuse). If it is not at `<BASE>`, the job writes the same declaration in
    `FunctionalEncryption/SamplerEfficiency.lean` for a mechanical move later. *Recommended.*
  - (B) Each job defines its own, unified after both land (a disclosed duplication).
  - (C) No named predicate: the fields are written out inline in each structure.

## 8. Risks (replaces design-r2 § 8)

- **Adaptive oracle games** are the largest new cost. Mitigations:
  - follow `IBEScheme.sidImpl`'s case-lemma and `_onSpec` style;
  - keep `saImpl`'s state small (an `Option` for the challenge plus the query count).
- **Lemma 3's bijection** must fix exactly what the adversary sees before the challenge. If the
  public part is larger than (A^⊤U, A^⊤W, A^⊤V) (for example through pp), Codex re-derives Δ's
  domain. If the bijection fails, escalate E-STMT rather than fall back to guessing (complexity
  leveraging would lose a factor p^{ℓ+n'}).
- **Rule 15 assembly** chooses target witnesses (`Classical.choose`) for the efficiency fields
  only. The laws, algorithms and simulators of the primitive are the raw bundle's, by
  `wee20PHFE_toRaw`, which is a reader of the assembly. A gate check confirms that no law
  depends on a chosen witness.
- **Phase B fit of L2 realisers.** `Games.exists_handlerMachine` gives `B` and a coin bijection φ
  with `B.runAt n z (φ (ω, r))`, not literally `B.coins = A.coins` with the identity layout.
  Phase B will need `NUPPT.coinsCongr` and possibly a layout lemma. This is a Phase B risk
  recorded now; the Phase A statements are fixed by `RealizesOn`.
- **R-DLOG** violations are easy to write by accident (`pow_val_bijective` inverses). Statements
  gate check.
- The symmetric adaptation, dependent types, Stage 2 drift and parallel jobs are as design-r2
  § 8.

## 9. Documented extensions (replaces design-r2 § 9)

- **General ABP partial garbling**: [AGW20, App. A] with [IK02]'s determinant lemma ([AGW20,
  Lemma 12] = [IW14, Lemma 1]) and [IW14, §4.2]. AGW20's "Extension" (shifts by δ).
- **Fully adaptive security**; many challenge ciphertexts; IND ([GJLS21, Def 4.4]); ε < 1.
- Secret-key PHFE; the ABP/NC¹ class; general k-Lin; IBE as an FE instance.
- Phase B: RAM programs, efficiency proofs, realisers (T1 for L2, the pre-target lemma for L1),
  and the unconditional corollaries.
