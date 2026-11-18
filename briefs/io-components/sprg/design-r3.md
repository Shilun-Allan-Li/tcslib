# io-sprg design r3: the structured-seed PRG of [JLS26, §2–§4, Theorem 4.1], Phase A

**Status.** Design note for the end-to-end Codex job `io-sprg`, **Phase A**. The Codex prompt
`dispatch-prompt-r3.md` points here.

**r3 is a delta over `design-r2.md`.**
- Every section of design-r2 not changed below is **binding as written there**, as are the
  design-r1 sections design-r2 marks "unchanged from r1".
- Precedence: `rulings.md` > design-r3 > design-r2 > design-r1.
- Everything marked **proposed** stays a starting shape. Codex may refine it **with disclosure**
  (REPORT.md § *Deviations from the design note*), never silently.

| Pin | Value |
|---|---|
| Rulings | every decision-log row dated 2026-11-18 in `IOComponentsPlan.md`, read at records `32a40963de5ed5f7abb472cd9d432c6561c2e833` (rule 15's two commits, after
`65b8fe45`). The rows used: *Phase A rulings, first batch* and *second batch*; *Sampler bridge implemented*; *Shared `Asymptotic/Realization.lean` written*; **Efficiency is mandatory** and **Efficiency baked into definitions** (standing rule 15, `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2) |
| Shared realisation file | branch `foundations/realization`, head `cdc0934f36365533d410607d0664a0570ae92679`, one commit on #374's `cbce64d1`. It adds `TCSlib/Cryptography/Asymptotic/Realization.lean` (250 lines) and 4 facade lines. Report: `briefs/io-components/realization/REPORT.md` |
| Sampler bridge | draft PR #378, branch `foundations/coin-sampling`, head `51dc767269bf81c4c7450d9a6430ad6bd3016470` on `cbce64d1`: `CoinSampling/*` (7 modules plus a facade) and `Games/Closeness.lean`, with facade lines only elsewhere |
| Lean base | `<BASE>`: a branch stacking #374 + `foundations/realization` + #378 (+ the shared sampler-efficiency file of Q-E1 (A), if written; § 7) |
| Base tree | relative to `cbce64d1`, `<BASE>` adds only new files and facade lines. So every file:line of design-r2 and `duplication-sweep-r2.md` stays valid; the new rows are in `duplication-sweep-r3.md` |

## What changed from r2

1. **Rule 15: efficiency is mandatory, and baked into the definitions** (§ 1, the largest
   change).
   - The generic `SPRG`, `BoolPRG` and the LPN family carry their honest algorithms' efficiency
     as **structure fields**:
     - deterministic maps as uniform `PolyTimeComputable`, with the modulus/pp on the input;
     - samplers as an exact-law core plus a #378 `UniformSampler`.
   - The construction is built as the **raw bundle** `jlsSPRG_raw` (r2's `jlsSPRG`), with
     correctness and security proved for it.
   - The inhabited primitive `jlsSPRG P π hT : SPRG` is assembled from the raw bundle and the
     efficiency targets.
   - Reductions stay in `RealizesOn` form with the Q-S11 link (`realizable_of_targets`).
   - **The statements gate checks "definitions carry efficiency" first after source fidelity.**
2. **`CoinSampling.Efficiency` is now imported**, because a design section needs it: the type
   `UniformSampler` in the sampler-efficiency fields (§ 1.2). It is imported **only** for that.
   The job builds no sampler, proves no sampler efficient, and does not import any other
   `CoinSampling` module or `Games.Closeness`.
3. **Q-S9 ruled (A) and the shared file exists.** `Complexity.NUPPT.RealizesOn` and its API at
   `<BASE>` are **must-reuse** (§ 2). `StructuredSeed/Realization.lean` is dropped.
4. **The predicate's body is weaker than design-r2 §4.8's draft.** It constrains only coin
   strings of length `c.eval m`. Statements are unchanged; "for every realiser" theorems get
   stronger and realisability easier (Dv16).
5. **Q-S10 (A), Q-S11 (A), Q-S12 (A) ruled.**
   - The Q-S11 link goes through the shared `exists_realizesOn_of_preTarget`.
   - Q-S10's targets grow by the sampler targets T5–T6, which rule 15 needs (§ 1.3).
6. **Size** ≈ 4,950–8,450 lines (r2: 4,600–7,900) (§ 4).
7. **One new question**, Q-E1: where the sampler-efficiency predicate lives (§ 7). The PHFE pack
   asks the same question; rule them together.

## 1. Rule 15 in this job (new; binding)

### 1.1 Raw bundles and primitives

Every primitive the job defines splits into a **raw bundle** (algorithms, laws, lengths and
bounds) and the **primitive**, which extends the raw bundle with **efficiency fields**:

| Primitive | Raw bundle (security, correctness, complexity are defined here) | Primitive (adds the efficiency fields) |
|---|---|---|
| sPRG, Defs 3.1–3.3 | `SPRG.Raw`: r2's `SPRG` fields, with the samplers in core-plus-draw form (§ 1.2) | `structure SPRG extends SPRG.Raw` with `eval_eff`, `idSamp_eff`, `sdSamp_eff` |
| Boolean PRG, Def 3.4 | — (the job never constructs one) | `BoolPRG` carries `eval_eff` (r2's `BoolPRG.EvalEfficient`, now a field) and `idSamp_eff` |
| LPN family, Def 2.3 | `LPNFamily.Raw`: r2's `LPNFamily` (the laws, `toLWE`, `adv`, `Assumption`) | `LPNFamily extends LPNFamily.Raw` with `sample_eff`: the matrix, secret and noise samplers (core + `UniformSampler`) |

- **No primitive instance exists without its efficiency proofs.**
- **Security, correctness, stretch and complexity predicates are defined on the raw bundle.**
  The primitive reads them through `toRaw`, with `_iff`/`_eq` readers (`SPRG.Secure S :=
  S.toRaw.Secure`, …).
- Assumptions quantify over primitives with efficiency where the job takes them as inputs:
  `Params.G : BoolPRG` is efficient. The LPN assumption is a property of the law
  (`LPNFamily.Raw.Assumption`); the construction's own family is raw (`P.lpnFamily_raw π`), and
  `P.lpnFamily π hT : LPNFamily` is assembled from target T6.
- **Disclosed:** existing interfaces the job only reuses (`LWE.Family`) still lack efficiency
  fields. The rule-15 audit retrofits them; this job edits no existing file.

### 1.2 Efficiency field forms (uniform only; S11)

- **Deterministic algorithms** (Eval′; the samplers' cores): `∃ f, PolyTimeComputable f ∧ ∀ κ …,
  f (NUPPT.advInput κ ⟨public parameter, ⟨inputs⟩⟩) = output`. These are design-r2 §4.4's
  `EvalEfficient` forms, now fields.
  - The map `f` is quantified before κ and before the public parameter.
  - The public parameter (`encPP`) is on the input; nothing computes p.
- **Samplers.** Every honest sampler is `core <$> sample (Draw κ …)`, a deterministic core
  applied to one exact uniform draw on a finite type (design-r2 C14, promoted to the interface:
  `SPRG.Raw` has fields `IdDraw`, `idCore`, `SdDraw`, `sdCore`, and `idSamp`/`sdSamp` are
  derived definitions with readers).
  - Its efficiency is the predicate `SamplesEfficiently y encDraw encOut core` (proposed; home:
    Q-E1). In words: there exist
    - a #378 `UniformSampler U` and a coin polynomial `c`;
    - an **explicit** equivalence `U.Ω (y κ π) ≃ Draw κ π`, compatible with `encDraw`;
    - failure `(U.sampler (y κ π) (c.eval κ)).fail ≤ 2^{-κ}` at every κ;
    - a `PolyTimeComputable f` computing `core` on `⟨1^κ, ⟨y κ π, encDraw d⟩⟩`.
  - Here `y κ π` is the **parameter word on the machine's input** (the encoded public parameter
    and the sampler's other inputs, for example the index I for SdSamp). The predicate:
  ```lean
  def SamplesEfficiently {P : ℕ → Type} {Draw : (κ : ℕ) → P κ → Type}
      [∀ κ π, Fintype (Draw κ π)] {β : (κ : ℕ) → P κ → Type}
      (y : ∀ κ, P κ → List Bool) (encDraw : ∀ κ π, Draw κ π → List Bool)
      (encOut : ∀ κ π, β κ π → List Bool) (core : ∀ κ π, Draw κ π → β κ π) : Prop :=
    ∃ (U : CoinSampling.UniformSampler) (c : PolyExpr) (e : ∀ κ π, U.Ω (y κ π) ≃ Draw κ π)
      (f : List Bool → List Bool),
      (∀ κ π w, U.enc (y κ π) w = encDraw κ π (e κ π w)) ∧
      (∀ κ π, (U.sampler (y κ π) (c.eval κ)).fail ≤ (2 : ℝ)⁻¹ ^ κ) ∧
      PolyTimeComputable f ∧
      ∀ κ π d, f (NUPPT.advInput κ (pairEncode (y κ π) (encDraw κ π d))) = encOut κ π (core κ π d)
  ```
  - Why this form: it uses only the #378 contract.
    - `UniformSampler` is one machine for every parameter word (no κ-indexed program, no
      hard-wired modulus).
    - The failure bound gives both negligible and `SubexpSmall 1` slack when Phase B transfers
      security to the coin samplers (`drawSlack`, `subexpSmall_drawSlack`).
    - The exact law stays the definition's law (S2).
  - Codex may refine the form (for example a different failure bound) with disclosure.

### 1.3 Targets and assembly

The Q-S10 targets of design-r2 §4.10 (T1 `evalTarget`, T2 `qGenTarget`, T3 `coreTarget`,
T4 `lpnPreTarget`/`prgPreTarget`) gain two:

| Target | Statement (named `Prop`, `_iff` reader, docstring "Phase B obligation; not proved in this development") |
|---|---|
| **T5** `P.drawSamplerTarget` | the `UniformSampler` halves of `SamplesEfficiently` for IdSamp′'s draw and SdSamp′'s draw (`Draw κ pp`), at every `pp` read from the input. Phase B route: #378's `zmod`, `bucket`, `pi`, `prod`, `ofEquiv` and their raw maps |
| **T6** `P.lpnSamplerTarget` | `SamplesEfficiently` for the construction's LPN family (matrix, secret, noise seeds; the noise core is `lpnNoise`'s pushforward). Phase B route: #378's `noiseSeeds`, `lweSeeds`, `zmod` |

`P.Targets := T1 ∧ T2 ∧ T3 ∧ T4 ∧ T5 ∧ T6`. **Assembly** (Phase A, pure, sorry-free):
```lean
/-- The raw bundle: r2's `jlsSPRG`, renamed. -/
def jlsSPRG_raw (P : Params) (π : PrimeSchedule) : SPRG.Raw
/-- THE PRIMITIVE [JLS26, §4, construction, p. 15]: the raw bundle with its efficiency fields,
assembled from the efficiency targets (T1, T3, T5; the targets' witnesses are chosen). -/
noncomputable def jlsSPRG (P : Params) (π : PrimeSchedule) (hT : P.Targets) : SPRG
theorem jlsSPRG_toRaw (P π hT) : (jlsSPRG P π hT).toRaw = jlsSPRG_raw P π
noncomputable def Params.lpnFamily (P) (π) (hT : P.Targets) : LPNFamily   -- from T6
```

### 1.4 Results, renamed and extended (replaces design-r2 §4.9's statement subjects)

- **On the raw bundle** (unchanged statements, subject renamed): `G4_eval_eq`,
  `jls_hasComplexity`, `jls_hasPolyStretch`, `claim42`, `prop41`, `jls_secure`,
  `jls_subexpSmall`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`.
  - The subject is `jlsSPRG_raw P π`, and the LPN family is `P.lpnFamily_raw π`.
  - r2's `exists_sprg`/`exists_sprg_subexp` become `exists_sprg_raw`/`exists_sprg_raw_subexp`
    (∃ `S : SPRG.Raw`), because a primitive needs efficiency.
- **On the primitive** (rule 15; Q-S11):
  ```lean
  theorem theorem41_of_targets (P) (π) {cLoc τ} (hLoc) (hτ) (hs) (hE) (hT : P.Targets)
      (hG : P.G.Secure) (hLPN : (P.lpnFamily_raw π).Assumption) :
      (jlsSPRG P π hT).Secure ∧ (jlsSPRG P π hT).HasComplexityEff P.d 2 ∧
        (jlsSPRG P π hT).HasPolyStretch
  /-- [JLS26, Theorem 4.1] as the library states primitives: an efficient sPRG exists. -/
  theorem exists_sprg_of_targets … (hT : ∀ P : Params, P.Targets) … :
      ∃ S : SPRG, (∀ κ, S.modulus κ = (π κ).p) ∧ S.Secure ∧ S.HasComplexityEff d 2 ∧
        S.HasPolyStretch
  ```
  plus the `_subexp` forms.
- **Realisability.** These no longer assume `P.Realizable π`: `realizable_of_targets` (from T4)
  supplies the realisers, so the only hypotheses beyond the assumptions are the efficiency
  targets.
  - `HasComplexityEff` (Def 3.3's "efficiently generated") follows from T2 and
    `jls_hasComplexity` (`hasComplexityEff_of_target`, as r2).
  - `evalEfficient_of_target` becomes the `eval_eff` field's proof inside the assembly.

## 2. The shared realisation API (must-reuse; replaces design-r2 §4.8's "realisation predicate")

All names are in the root namespace `Complexity.NUPPT` (declared with `_root_` inside
`namespace TCSlib.Cryptography`). Lines are at `foundations/realization` head `cdc0934f`.

| Name | Line | Statement (short) | Use in this job |
|---|---|---|---|
| `NUPPT.RealizesOn B enc c R` | 96 | `B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`. `B`'s advice is never read back | every realiser hypothesis (`prop41`, `LPNRealizable`, `PRGRealizable`) |
| `NUPPT.realizesOn_iff` | 103 | the reader (`Iff.rfl`) | Rule 10 reader |
| `RealizesOn.coins_eq`, `.runAtL_eq` | 113, 118 | `B.coins = c`; agreement at a coin string of length `c(m)` | hop lemmas |
| `RealizesOn.runAt_eq`, `.distinguisherL_eq` | 124, 132 | typed coins; the verdict lemma | hop lemmas |
| `RealizesOn.runAt_coinsEquivPoly_symm` | 141 | coins carried from `Fin (c.eval m) → Bool` | sums over coins |
| `NUPPT.realizesOn_of_forall`, `RealizesOn.congr` | 149, 157 | introduction from every coin string; change `R` | matching shapes |
| `realizesOn_self`, `realizesOn_self_take` | 167, 179 | non-vacuity | non-vacuity table |
| **`exists_realizesOn_of_preTarget`** | 220 | typed advice `Ω m`, encoding `encΩ`, pre-processing `pre`, a `PolyTimeComputable f` with `f ⟨encΩ m w, enc m x⟩ = pre m w x`, advice `ω` with length bound `b`, `φ ≤ p` ⇒ `∃ B, B.RealizesOn enc (A.coins.subst p) (fun m x r => A.runAtL (φ m) (pre m (ω m) x) (r.take (A.coinLen (φ m))))` | **M6: `realizable_of_targets`** |
| `exists_realizesOn_of_preTarget_id`, `exists_realizesOn_reparam_pre_post` | 239, 198 | the φ = id case; the string form | not needed |

`realizable_of_targets (P) (hT4 : P.ReductionTargets) (π) : P.Realizable π`. Per reduction,
apply `NUPPT.exists_realizesOn_of_preTarget A φX .var hφX encX (encXAdvice π) (XPre π) hf (hT4.X π)
ω b hb` with `φX = κOf`/`κOfN` and `b` the advice encoding's length bound. Use `exact`, or
`RealizesOn.congr` if the definitional shapes differ. The shared report's probe elaborated
exactly this (`realization/REPORT.md` §2).

## 3. Phase B outlook (replaces design-r2 §9's sampler sentence)

Phase B proves T1–T6 from word-RAM programs and the RAM bridge. For T5 and T6 it uses #378:
- the decoders `CoinSampling.CoinSampler` (`Basic.lean:93`), `bucket`/`fail_bucket_le`
  (`Buckets.lean:138, 176`), `zmod`/`fail_zmod_le` (`Instances.lean:56, 71`), `pi`/`prod`
  (`Basic.lean:322, 408`), `noiseSeeds`, `lweSeeds` (`Instances.lean:95, 116`);
- the raw maps `UniformSampler`, `bucketRaw`, `polyTimeComputable_bucketRaw`, `bucketSampler`
  (`Efficiency.lean:93, 169, 284, 308`);
- the game transfer `draw`, `close_draw_bind`, `allOutputs_draw_bind` (`Transfer.lean:73, 106,
  163`) and `Games.ProbComp.Close`/`advantage_le_of_close` (`Games/Closeness.lean:69, 196`).

Then `jlsSPRG P π hT` and `exists_sprg_of_targets` become unconditional. Phase A uses only the
type `UniformSampler` (§ 1.2).

## 4. Layout and size (amends design-r2 §2.2; imports §2.3)

| File (under `Obfuscation/StructuredSeed/`) | r2 | r3 |
|---|---|---|
| `Realization.lean` | 0–150 | **removed** |
| `LPN.lean` | 150–250 | 200–330 (`LPNFamily.Raw` / `LPNFamily` split, `sample_eff`) |
| `BoolPRG.lean` | 200–340 | 220–370 (`eval_eff`, `idSamp_eff` fields) |
| `SamplerEfficiency.lean` | — | 0 if Q-E1 (A) at `<BASE>`; else 60–120 (`SamplesEfficiently` + readers, for a mechanical move later) |
| `Defs.lean` | 280–450 | 420–700 (`SPRG.Raw`/`SPRG` split; draw/core fields; efficiency fields; lifted predicates and readers) |
| `Samplers.lean` | 330–500 | 350–540 (`jlsSPRG_raw`; draw/core form already C14) |
| `Targets.lean` | 220–400 | 380–650 (T5, T6; `realizable_of_targets` via the shared lemma; the assembly `jlsSPRG`, `lpnFamily`; `theorem41_of_targets`, `exists_sprg_of_targets(_subexp)`) |
| `Security.lean` | 220–400 | 220–400 (raw subjects) |
| other files | as design-r2 | as design-r2 |
| **Total** | 20 modules + 2 facades, ≈ 4,600–7,900 | **19–20 modules + 2 facades, ≈ 4,950–8,450 (central ≈ 6,500)** |

**Imports (amends design-r2 §2.3).**
- Add `TCSlib.Cryptography.Asymptotic.Realization` (where realisers appear).
- Add **`TCSlib.Cryptography.CoinSampling.Efficiency`, only in the files that state
  sampler-efficiency fields or targets** (`Defs`, `BoolPRG`, `LPN`, `Targets`, or the
  `SamplesEfficiently` home), and only for the type `UniformSampler` (with `encodeOption` and
  `CoinSampler.fail`).
- **Do not import** any other `CoinSampling` module or `Games.Closeness`, nor
  `TCSlib/Programs/*`, `TCSlib/Complexity/RAMSimulation/*`, the design-r1 §2.3 list, or the
  Phase B appendix modules.

**Milestones** (design-r2 §5, amended):

| M | r3 change | Lines (cum.) |
|---|---|---|
| M0 | raw/primitive splits; efficiency fields final; T5–T6; the assembly definitions; no local `RealizesOn`; REPORT gains the **rule-15 table** (every primitive, its efficiency fields, the raw bundle, the target that inhabits it) | 2,100–3,200 |
| M1–M5 | subjects renamed to the raw bundle; otherwise as design-r2 | as design-r2 |
| M6 | `realizable_of_targets` via the shared lemma; the assembly proofs (`jlsSPRG`, `lpnFamily`); `theorem41_of_targets`, `exists_sprg_of_targets(_subexp)`, `hasComplexityEff_of_target` | +300–700 |
| **Total** | | **≈ 4,950–8,450** |

## 5. Statements-gate order (binding)

1. **Source fidelity** ([JLS26] items and pages).
2. **Definitions carry efficiency (rule 15).** Each of `SPRG`, `BoolPRG` and `LPNFamily` carries
   its honest algorithms' efficiency as fields, in uniform form only:
   - `PolyTimeComputable` of the deterministic maps with the public parameter on the input;
   - samplers via `SamplesEfficiently`/`UniformSampler`.

   Further checks:
   - no bare `∃ A : NUPPT, A.Computes f`;
   - no primitive value is constructed except by the assembly from targets;
   - raw bundles carry the correctness/security statements;
   - the targets T1–T6 together inhabit every primitive the job constructs.
3. Then the rest of design-r2's gate (statements, non-vacuity, Rule 10, uniformity of targets).

## 6. Disclosed deviations (adds to design-r2 §8)

- **Dv16. Realisation body.** The shared `NUPPT.RealizesOn` constrains a realiser only on encoded
  challenges and on coin strings of length `c(m)`. It is weaker than "agrees on every input and
  every coin string", so every "for every realiser" theorem is at least as strong. One sentence
  in the docstrings of `prop41` and of the realisability propositions.
- **Dv17. Samplers in core-plus-draw form at the interface.** Def 3.1's PPT samplers are stated
  as an exact-law core applied to one uniform draw on a finite type, with their efficiency
  through a `UniformSampler` that is exact on success and fails with probability ≤ 2^{-κ}. This
  is not "a PPT machine whose output law is the law".
  - The reason is that rule 15 requires the efficiency in the definition, and #378 is the
    library's sampler contract.
  - The exact law stays the definition's law.
- **Dv18. Raw bundle vs primitive.** [JLS26, §4]'s construction is `jlsSPRG_raw` (proved correct
  and secure). The sPRG of Theorem 4.1 is `jlsSPRG P π hT`, which exists once the efficiency
  targets are proved (Phase B).

## 7. Questions

### 7.1 Settled since r2

| r2 question | Status | Ruling (decision-log row) | Consequence in r3 |
|---|---|---|---|
| Q-S9 home of the realisation predicate | **settled: A** | *Phase A rulings, first batch*; *Shared `Asymptotic/Realization.lean` written* | § 2; Dv16 |
| Q-S10 efficiency statements | **settled: A** | *Phase A rulings, second batch* | design-r2 §4.10 as written, plus T5–T6 (§ 1.3) under rule 15 |
| Q-S11 targets ⇒ realisers in Phase A | **settled: A** | *Phase A rulings, second batch* | M6; `exists_realizesOn_of_preTarget` |
| Q-S12 schedule in the generic sPRG | **settled: A** | *Phase A rulings, second batch* | design-r2 §4.1/§4.4 as written; the efficiency fields read `encPP` from the input |
| (new) efficiency in definitions | **ruled** | *Efficiency is mandatory*; *Efficiency baked into definitions* (rule 15) | § 1, § 5 |

Q-S1–Q-S8 stay as design-r2 §10.1 records them.

### 7.2 Open (multiple choice, recommended first)

- **Q-E1. Where `SamplesEfficiently` lives** (the same question as the PHFE pack's Q-E1; rule
  them together). Both jobs state sampler efficiency with the same shape (§ 1.2), and parallel
  definitions would be a duplication.
  - **(A)** One shared in-house file, written by the maintainer before dispatch and stacked into
    `<BASE>`, as the realisation file was: `TCSlib/Cryptography/CoinSampling/Contract.lean`
    (`SamplesEfficiently` and readers, ≈ 60–120 lines), on #378. The job reuses it (must-reuse).
    If it is not at `<BASE>`, the job writes the same declaration in
    `StructuredSeed/SamplerEfficiency.lean`, inside its namespace, for a mechanical move later.
    *Recommended.*
  - (B) Each job defines its own, unified after both land (a disclosed duplication).
  - (C) No named predicate: the fields are written out inline in each structure (longer
    structures; Phase B states each sampler's contract separately).
