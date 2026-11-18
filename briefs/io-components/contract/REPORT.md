# Shared sampler-efficiency contract and the iO Phase A base: report

Filed by the maintainer from the sub-agent's returned report (its own write of this file was refused by the
harness, which returns sub-agent reports as text). Ruling Q-E1 (A), records `1ebea1fb`.

## Heads
- `foundations/coin-contract` = `8e01b720aa127f6cbdb066e629f883258b73cf9e`: one SSH-signed commit on #378's
  `51dc767269bf81c4c7450d9a6430ad6bd3016470`; adds `TCSlib/Cryptography/CoinSampling/Contract.lean` (373 lines) and
  one import line + one Contents bullet in the `CoinSampling` facade.
- `iO/phase-a-base` = `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`: signed `--no-ff` merge of
  `foundations/realization` (`cdc0934f36365533d410607d0664a0570ae92679`) into the contract branch; tree
  `9155903018d18fbc735791f21485abaaee3e161a` (as `git merge-tree` predicted, no conflicts). Contains #374, #378,
  #380 and the contract.

## Statements (`namespace TCSlib.Cryptography.CoinSampling`)
```lean
def DrawSamplable (y : ∀ κ, P κ → List Bool) (encDraw : ∀ κ π, Draw κ π → List Bool) : Prop :=
  ∃ (U : UniformSampler) (c : PolyExpr) (e : ∀ κ π, U.Ω (y κ π) ≃ Draw κ π),
    (∀ κ π w, U.enc (y κ π) w = encDraw κ π (e κ π w)) ∧
    ∀ κ π, (U.sampler (y κ π) (c.eval κ)).fail ≤ (2 : ℝ)⁻¹ ^ κ
def CoreComputable y encDraw (encOut : ∀ κ π, β κ π → List Bool) (core : ∀ κ π, Draw κ π → β κ π) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ κ π d,
    f (NUPPT.advInput κ (pairEncode (y κ π) (encDraw κ π d))) = encOut κ π (core κ π d)
def SamplesEfficiently y encDraw encOut core : Prop :=
  DrawSamplable y encDraw ∧ CoreComputable y encDraw encOut core
```
Docstrings: for **honest** samplers, **uniform** ([PS10, Def 23.4]: no advice, no κ-indexed program, no hard-wired
modulus); the law stays the exact `core <$> sample Draw`; `e` need not be computable (`U.raw` and the encoding
equation fix the machine's output).

- Readers: `drawSamplable_iff`, `coreComputable_iff`, `samplesEfficiently_iff` (`Iff.rfl`),
  `samplesEfficiently_iff_exists` (design-r3 §1.2's one-existential form), projections, `SamplesEfficiently.intro`.
- Closure (Glue): `coreComputable_id`; `CoreComputable.map`/`SamplesEfficiently.map` (pushforward with the
  parameter word on the input); `.map_output`; `CoreComputable.pair`/`SamplesEfficiently.pair`;
  `DrawSamplable.congr`/`SamplesEfficiently.congr`.
- Non-vacuity: `BoundedModulus b κ := {q : ℕ+ // q ≤ 2^{b κ}}`, `modulusWord`, `residueEnc`;
  `listToNat_modulusWord`, `drawSamplable_residue b`, `samplesEfficiently_residue b` (uniform `ZMod q`, identity core;
  witness `bucketSampler` with coins `b + var`; failure from `fail_bucket_le`).
- Deviations from design-r3 §1.2 (disclosed): the unused `[Fintype (Draw κ π)]` binder dropped (strictly more
  general); defined as two named halves (sPRG T5 targets `DrawSamplable`, T3 `CoreComputable`).
- **Not included: products of draws.** A `UniformSampler` fixes `sampler y s` from the coin count alone and the
  contract has no monotonicity of `fail` in `s`, so a product needs a concrete product `UniformSampler`
  (`CoinSampler.prod` with a polynomial-time coin splitter): Phase B, on sPRG T5's route. Included: pairing cores on
  one draw, and draws that are already product types.

## Mapping onto the packs
Both packs import `CoinSampling.Contract`; their `[Q-E1]` items take the "file at `<BASE>`: must-reuse" arm; `<BASE>`
= `iO/phase-a-base` @ `5ed465f6…`.
- sPRG: `SPRG.idSamp_eff`/`sdSamp_eff`, `BoolPRG.idSamp_eff`, `LPNFamily.sample_eff` → `SamplesEfficiently`;
  T5 → `DrawSamplable`; T3 → `CoreComputable` (assembled with T5 via `.intro`); T6 → `SamplesEfficiently` (`.map`,
  `.map_output`, `.pair`).
- PHFE: `FEScheme.setup_eff`/`enc_eff`/`keyGen_eff`, the `Simulator`/`SASimulator` fields, `Wee20.SchemeTargets`/
  `SimTargets` → `SamplesEfficiently`; y is the encoded pp plus the sampler's other inputs.
- Deterministic algorithms (Eval′, Dec, lgen/rec) keep `PolyTimeComputable`, outside this file.
- Line pointers in `Contract.lean`: `SamplesEfficiently` 128, `DrawSamplable` 90, `CoreComputable` 106, readers and
  closure 96–300, non-vacuity 305–372 (the only `UniformSampler` instantiation).

## Checks
- `lean_check_tree.sh` on `cp -al` copies of snapshot #10, one Lean process at a time, no `lake build`, no cache get.
- Contract branch: Closeness, CoinSampling Basic/Buckets/Transfer/Efficiency/Contract/Asymptotic/Instances,
  Foundations/Subexponential, CoinSampling facade: rc 0, 0 errors, 0 warnings.
- Merged base, fresh copy, dependency order (Subexponential, Foundations facade, Realization, Asymptotic facade,
  Closeness, Games facade, the CoinSampling modules and facade, root `TCSlib.lean` with the recipe's Mathlib overlay in
  the copy only): all rc 0, 0 errors, 0 warnings, no `sorry`.
- Snapshot #10 unmodified (`snapmap.py verify`, 1478 files, 0/0/0, RESULT OK, before and after).
- `style_lint`: 0 findings on all 11 new files; lines ≤ 100; no `sorry`/`admit`/`native_decide`/`axiom`.
- `#print axioms` on all 28 declarations of `Contract.lean`: standard only (`[propext, Classical.choice,
  Quot.sound]`, or subsets); no `sorryAx`.
