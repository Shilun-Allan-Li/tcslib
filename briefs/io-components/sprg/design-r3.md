# io-sprg design r3: the structured-seed PRG of [JLS26, §2–§4, Theorem 4.1], Phase A

**Status.** Design note for the end-to-end Codex job `io-sprg`, **Phase A**. The Codex prompt
`dispatch-prompt-r3.md` points here. r3 is a **delta over `design-r2.md`**:
- every section of design-r2 not changed below is **binding as written there**;
- the same holds for the design-r1 sections that design-r2 marks "unchanged from r1".

Precedence: `rulings.md` > design-r3 > design-r2 > design-r1. Everything marked **proposed** in
design-r2 stays a starting shape. Codex may refine it **with disclosure** (REPORT.md §
*Deviations from the design note*), never silently.

| Pin | Value |
|---|---|
| Rulings | every decision-log row dated 2026-11-18 in `IOComponentsPlan.md`, read at records `43eacf952cfc9517f9be8f93e367f658effd9b47`. The rows used here are *Phase A rulings, first batch*, *Phase A rulings, second batch*, *Sampler bridge implemented* and *Shared `Asymptotic/Realization.lean` written* |
| Shared realisation file | branch `foundations/realization`, head `cdc0934f36365533d410607d0664a0570ae92679`, one commit on #374's `cbce64d1`. It adds `TCSlib/Cryptography/Asymptotic/Realization.lean` (250 lines) and 4 facade lines in `Asymptotic.lean`. Report: `briefs/io-components/realization/REPORT.md` |
| Sampler bridge | draft PR #378, branch `foundations/coin-sampling`, head `51dc767269bf81c4c7450d9a6430ad6bd3016470` on `cbce64d1`. It adds `CoinSampling/*` (7 modules plus a facade) and `Games/Closeness.lean`, plus facade lines in `TCSlib.lean` and `Games.lean`. It edits no other file |
| Lean base | `<BASE>`: a branch stacking #374 + `foundations/realization` + #378 (ruling *Phase A rulings*). It is filled by the maintainer |
| Base tree | relative to `cbce64d1`, `<BASE>` adds only new files and facade lines (`git diff --stat` of each stacked branch, read at the heads above). So every file:line of design-r2 and of `duplication-sweep-r2.md` stays valid. The new rows are in `duplication-sweep-r3.md` |

## What changed from r2

1. **Q-S9 ruled (A) and the shared file exists.** `Complexity.NUPPT.RealizesOn` and its API live
   in `TCSlib/Cryptography/Asymptotic/Realization.lean` at `<BASE>`. They are **must-reuse**.
   - The job defines no realisation predicate, no variant and no local copy.
   - `StructuredSeed/Realization.lean` is **dropped** from the layout.
   - The exact names are in §1 below.
2. **The predicate's body is weaker than design-r2 §4.8's draft.** It constrains only coin
   strings of length `c.eval m`:
   `B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`.
   - Every statement of design-r2 is **unchanged** syntactically.
   - "For every realiser B" theorems get stronger, since more machines realise.
   - The realisability propositions get easier to discharge.
   - Consumers read realisers through typed coins (`RealizesOn.runAt_eq`,
     `RealizesOn.distinguisherL_eq`), so no proof loses anything.
   - Docstrings and REPORT.md say so (Dv16, §5).
3. **Q-S10 (A), Q-S11 (A), Q-S12 (A) ruled**, as recommended (*Phase A rulings, second batch*).
   - design-r2 §4.10 and §4.1 are now settled, no longer proposals awaiting a ruling.
   - **The Q-S11 link goes through the shared file's link lemma,
     `Complexity.NUPPT.exists_realizesOn_of_preTarget`.** design-r2 §4.10 instead instantiated
     `exists_reparam_pre_post` directly (§2 below).
4. **Base and stacking.** `<BASE>` carries #378 (`CoinSampling`, `Games.Closeness`), so that
   Phase B's sampler API is visible for the outlook only.
   - **No design section of Phase A needs it.** S2 of design-r2 stands: the job must not import
     `CoinSampling` or `Games.Closeness`.
   - The Phase B outlook (design-r2 §9) now names the bridge's real declarations (§4 below).
5. **No open questions remain** (§6).

## 1. The shared realisation API (must-reuse; replaces design-r2 §4.8's "realisation predicate")

All names are in the root namespace `Complexity.NUPPT`. The file's namespace is
`TCSlib.Cryptography`, and it declares them with `_root_`. Lines are at
`foundations/realization` head `cdc0934f`.

| Name | Line | Statement (short) | Use in this job |
|---|---|---|---|
| `NUPPT.RealizesOn B enc c R` | 96 | `B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`. `X : ℕ → Type*`; `B`'s advice is never read back | every realiser hypothesis (`prop41`, `LPNRealizable`, `PRGRealizable`) |
| `NUPPT.realizesOn_iff` | 103 | the reader (`Iff.rfl`) | Rule 10 reader |
| `RealizesOn.coins_eq`, `RealizesOn.runAtL_eq` | 113, 118 | `B.coins = c`; agreement at a coin string of length `c(m)` | hop lemmas |
| `RealizesOn.runAt_eq` | 124 | `B.runAt m (enc m x) ρ = R m x (List.ofFn ρ)` | hop lemmas (typed coins) |
| `RealizesOn.distinguisherL_eq` | 132 | the verdict lemma: `B.distinguisherL m (enc m x) ρ = decide (R m x (List.ofFn ρ) = [true])` | hop lemmas (the realiser's advantage = the reduction function's) |
| `RealizesOn.runAt_coinsEquivPoly_symm` | 141 | the activation on coins carried from `Fin (c.eval m) → Bool` | moving sums over `B.Coins m` to `{0,1}^{c(m)}` |
| `NUPPT.realizesOn_of_forall` | 149 | from agreement on **every** coin string (the drafts' body) | if a proof produces the strong form |
| `RealizesOn.congr` | 157 | change `R` along agreement on coin strings of length `c(m)` | matching a construction's conclusion to `lpnRed`/`prgRed` |
| `realizesOn_self`, `realizesOn_self_take` | 167, 179 | non-vacuity: every machine realises its own activation, and the identity reduction | non-vacuity table (REPORT) |
| `exists_realizesOn_reparam_pre_post` | 198 | string form of `exists_reparam_pre_post` in this vocabulary | not needed if the next row is used |
| **`exists_realizesOn_of_preTarget`** | 220 | typed advice `Ω m` with encoding `encΩ`, a pre-processing `pre m w x`, a `PolyTimeComputable f` with `f ⟨encΩ m w, enc m x⟩ = pre m w x`, an advice family `ω` with a length bound `b` ⇒ `∃ B, B.RealizesOn enc (A.coins.subst p) (fun m x r => A.runAtL (φ m) (pre m (ω m) x) (r.take (A.coinLen (φ m))))`, for `φ ≤ p` | **M6: `realizable_of_targets`** (Q-S11 A) |
| `exists_realizesOn_of_preTarget_id` | 239 | the `φ := id` case | not used (sPRG has `φ = κOf`, `κOfN`) |

**The vacuity rule of design-r2 §7 (3)(iii) is now met by construction.** The predicate
constrains neither non-encodings nor coin strings of other lengths, nor `B`'s advice.

## 2. Changes to design-r2 §4.8–§4.10 (statement shapes)

- **§4.8.** Delete the `RealizesOn` code block and its "home" paragraph. Every
  `BL.RealizesOn … (A.coins.subst .var) …` and `BG.RealizesOn …` of §4.8/§4.9 now refers to the
  shared definition, and the statements are unchanged. Hop lemmas read realisers through
  `RealizesOn.runAt_eq` / `RealizesOn.distinguisherL_eq`, never by unfolding `RealizesOn`
  (Rule 10; the shared file is foreign).
- **§4.9.** Unchanged: `prop41`, `Params.LPNRealizable`, `PRGRealizable`, `Realizable`, and the
  corollaries.
  - Docstrings of the realisability propositions add one sentence: "A realiser is constrained
    only on encoded challenges and on coin strings of the layout's length (`RealizesOn`)."
- **§4.10, Q-S11 (A), settled.**
  ```lean
  theorem realizable_of_targets (P : Params) (hT : P.ReductionTargets) (π : PrimeSchedule) :
      P.Realizable π
  ```
  - **Proof route.** Per reduction X ∈ {lpn, prg}, apply `NUPPT.exists_realizesOn_of_preTarget A
    φX .var hφX (encX) (encXAdvice π) (XPre π) hf (hT.X π) ω b hb`, with:
    - `φX` = `κOf` (LPN) or `κOfN` (PRG), and `hφX : ∀ m, φX m ≤ m` (`κOf_le`, `κOfN_le`);
    - `b` and `hb` the advice encoding's `PolyExpr` length bound (M0 definitions, M6 proofs).
    The conclusion is `XRed π A · (ω ·)` up to δ-reduction (`exact`, or `RealizesOn.congr` if the
    definitional shapes differ).
  - The shared report's probe elaborated exactly this instantiation for the sPRG shape
    (`realization/REPORT.md` §2).
  - `theorem41_of_targets`, `exists_sprg_of_targets`, `evalEfficient_of_target` and
    `hasComplexityEff_of_target` are unchanged.
- **§4.10, Q-S10 (A), settled.** T1–T4 as named `PolyTimeComputable` propositions, with `_iff`
  readers and no `sorry`, as design-r2 §4.10 wrote them. No change.
- **§4.1, Q-S12 (A), settled.**
  - The generic `SPRG` keeps a modulus schedule and publishes it (`encPP`).
  - The construction's algorithms take `pp : PrimeParam κ` and are assembled per schedule
    (`jlsSPRG P π`).
  - No change.

## 3. Layout and size (replaces design-r2 §2.2's two affected rows and the total)

| File (under `Obfuscation/StructuredSeed/`) | r2 | r3 |
|---|---|---|
| `Realization.lean` | 0–150 (only if Q-S9 not A at `<BASE>`) | **removed** (the shared file is at `<BASE>`) |
| `Targets.lean` | 220–400 | 200–370: the link is one lemma application per reduction (`exists_realizesOn_of_preTarget`) |
| **Total** | 20 modules + 2 facades, ≈ 4,600–7,900 (central ≈ 6,000) | **19 modules + 2 facades, ≈ 4,550–7,700 (central ≈ 5,900)** |

Imports (design-r2 §2.3) **add** `TCSlib.Cryptography.Asymptotic.Realization` (in `Security.lean`,
`Reductions/*.lean`, `Targets.lean` as needed). The do-not-import list still includes:
- `CoinSampling` (any module) and `Games.Closeness`;
- `TCSlib/Programs/*` and `TCSlib/Complexity/RAMSimulation/*`;
- the modules of design-r1 §2.3 *Do not import*;
- the Phase B appendix modules.

Milestones (design-r2 §5) are unchanged except:

| M | r3 change | Lines (cum.) |
|---|---|---|
| M0 | no local `RealizesOn`; the non-vacuity table cites `realizesOn_self_take` for the predicate's satisfiability | 1,850–2,850 |
| M6 | `realizable_of_targets` through `exists_realizesOn_of_preTarget` | +150–420 |
| **Total** | | **≈ 4,550–7,700** |

## 4. Phase B outlook (replaces the sampler-bridge sentence of design-r2 §9)

The in-house sampler bridge is implemented (draft PR #378, `foundations/coin-sampling` head
`51dc7672`; `sampler-bridge/IMPL-REPORT.md`).
- Phase B composes the cores of T3 (`coreTarget`) with:
  - its exact-on-success decoders, `CoinSampling.CoinSampler` (`Basic.lean:93`), `bucket` and
    `fail_bucket_le` (`Buckets.lean:138, 176`), `zmod` and `fail_zmod_le` (`Instances.lean:56,
    71`), `CoinSampler.pi`/`prod` (`Basic.lean:322, 408`);
  - the game transfer: `draw`, `drawD`, `close_draw_bind`, `close_drawD_bind`,
    `allOutputs_draw_bind` (`Transfer.lean:73, 83, 106, 125, 163`); `Games.ProbComp.Close`, its
    `advantage_le_of_close`, `OutputsSubset` (`Games/Closeness.lean:69, 196, 217`);
  - the asymptotic slack: `drawSlack`, `negligible_drawSlack`, `subexpSmall_drawSlack`
    (`Asymptotic.lean:99, 115, 123`);
  - the efficiency layer: `UniformSampler`, `toNUPPT`, `toNUPPT_runAt`, `bucketRaw`,
    `polyTimeComputable_bucketRaw`, `bucketSampler` (`Efficiency.lean:93, 117, 136, 169, 284,
    308`).
- **Perfect correctness of `HasComplexity`** transfers through `allOutputs_draw_bind` (an
  `AllOutputs` statement survives a decoder that is exact on success).
- **Realisers come from the targets.** With Q-S11 (A), `realizable_of_targets` already turns
  T4 into realisers. Phase B only proves T1–T4 from word-RAM programs and the RAM bridge, and
  composes the samplers.
- **None of this is imported or used in Phase A.**

## 5. Disclosed deviations (adds to design-r2 §8)

- **Dv16. Realisation body.** The realisation predicate is the shared `NUPPT.RealizesOn`. It
  constrains a realiser only on encoded challenges and on coin strings of length `c(m)`.
  - It is weaker than "agrees on every input and every coin string", so it admits more
    realisers.
  - Every "for every realiser" theorem is therefore at least as strong.
  - The docstrings of `prop41` and of the realisability propositions say so in one sentence.

## 6. Questions

### 6.1 Settled since r2

| r2 question | Status | Ruling (decision-log row) | Consequence in r3 |
|---|---|---|---|
| Q-S9 home of the realisation predicate | **settled: A** | *Phase A rulings, first batch*; *Shared `Asymptotic/Realization.lean` written* | §1; `StructuredSeed/Realization.lean` dropped; Dv16 |
| Q-S10 efficiency statements | **settled: A** | *Phase A rulings, second batch* | design-r2 §4.10 as written (T1–T4, `SPRG.EvalEfficient`, `HasComplexityEff`, `BoolPRG.EvalEfficient`, `MultilinearRep.TermsEfficient`) |
| Q-S11 targets ⇒ realisers in Phase A | **settled: A** | *Phase A rulings, second batch* | M6; the link lemma `exists_realizesOn_of_preTarget` (§2) |
| Q-S12 schedule in the generic sPRG | **settled: A** | *Phase A rulings, second batch* | design-r2 §4.1/§4.4 as written |

Q-S1–Q-S8 stay as design-r2 §10.1 records them.

### 6.2 Open

None.
