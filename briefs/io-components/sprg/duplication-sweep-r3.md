# io-sprg: duplication sweep r3 (Phase A), a delta over r2

Static sweep (no Lean run), refreshed for pack r3. **`duplication-sweep-r2.md` stays the
must-reuse list.** This file amends it as stated below and adds rows; every r2 row not named here
is unchanged.

**Base.** `<BASE>` stacks three branches:
- #374 (`foundations/subexp` `cbce64d1c135c710b7c036968ed9d4f21414aa72`);
- `foundations/realization` (`cdc0934f36365533d410607d0664a0570ae92679`);
- #378 (`foundations/coin-sampling` `51dc767269bf81c4c7450d9a6430ad6bd3016470`).

Read with `git diff --stat`, each stacked branch adds only new files and facade lines over
`cbce64d1`:
- realization: `Asymptotic/Realization.lean` +250 and `Asymptotic.lean` +4;
- coin-sampling: `CoinSampling.lean`, `CoinSampling/*.lean`, `Games/Closeness.lean`, plus
  `TCSlib.lean` +1 and `Games.lean` +3.

So **every r2 file:line is valid at `<BASE>`**. The new rows were read at the heads above with
`git show`. If `<BASE>` is rebuilt differently, the worker re-checks these lines.

Legend as r2: **MR** must reuse; **R** reuse if the route needs it; **NR** nearest relative;
**X** do not use; **B** Phase B only.

## Amended r2 rows

| r2 row | r2 status | r3 status |
|---|---|---|
| §D, "The shared realisation file (Q-S9 A …) only if present at `<BASE>`" | MR when present; otherwise a local file | **MR, present.** The rows below replace it. The job writes no `StructuredSeed/Realization.lean` and no variant |
| Search "no hit: a generic machine realises a function on encoded challenges predicate" | no hit (job may add) | **hit**: `Complexity.NUPPT.RealizesOn` (below); adding one is a major |
| §D, `NUPPT.exists_reparam_pre_post` (`Asymptotic/UniversalLemmas.lean:79`) | MR for `realizable_of_targets` | **R**: superseded for the link by `exists_realizesOn_of_preTarget`, which wraps it. Use it directly only if the wrapper's shape does not fit, and say why |
| Appendix, "Sampler bridge … in-house … not at `cbce64d1`" | B (and X even if a later `<BASE>` has it) | now at `<BASE>` with real names (§S below). **X/B, except the type `UniformSampler`** (and `CoinSampler.fail`), which rule 15's efficiency fields use (`CoinSampling.Efficiency` imported for that only) |
| §D `NUPPT.Uniform`, `Computes`, `PolyTimeComputable` | MR for efficiency statements | **MR for the efficiency fields** of `SPRG`, `BoolPRG`, `LPNFamily` (rule 15) and for T1–T6 |

## R. The shared realisation API (`TCSlib/Cryptography/Asymptotic/Realization.lean`, at `<BASE>`)

Names are `Complexity.NUPPT.*` (declared with `_root_` inside `namespace TCSlib.Cryptography`).

| Name | Line | Use |
|---|---|---|
| `RealizesOn` (`B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r`) | 96 | **MR**: every realiser hypothesis |
| `realizesOn_iff` | 103 | **MR** (the reader; never unfold `RealizesOn`) |
| `RealizesOn.coins_eq`, `RealizesOn.runAtL_eq` | 113, 118 | **MR** |
| `RealizesOn.runAt_eq`, `RealizesOn.distinguisherL_eq` (the verdict lemma) | 124, 132 | **MR**: hop lemmas |
| `RealizesOn.runAt_coinsEquivPoly_symm` | 141 | **MR** where sums over `B.Coins m` move to bit vectors (do not re-derive with `coinsEquivPoly`) |
| `realizesOn_of_forall`, `RealizesOn.congr` | 149, 157 | **MR** where a conclusion must be matched to `lpnRed`/`prgRed` |
| `realizesOn_self`, `realizesOn_self_take` | 167, 179 | **MR** for the non-vacuity table |
| `exists_realizesOn_reparam_pre_post` | 198 | R |
| `exists_realizesOn_of_preTarget` | 220 | **MR**: `realizable_of_targets` (Q-S11 A) |
| `exists_realizesOn_of_preTarget_id` | 239 | NR (`φ = id` shape; the sPRG's `φ` is `κOf`/`κOfN`) |

## S. The sampler bridge at `<BASE>` (#378)

Namespace `TCSlib.Cryptography.CoinSampling` (and `TCSlib.Cryptography.Games` for `Closeness`).

**Rule 15 (design-r3 § 1) changes one row.** The efficiency fields of the job's primitives are
stated with the type `UniformSampler`, so `CoinSampling.Efficiency` is imported, and used only
for:

| Name | File:line | Status |
|---|---|---|
| `UniformSampler` (fields `Ω`, `enc`, `sampler`, `raw`, `raw_layout`, `polyTime`) | `CoinSampling/Efficiency.lean:93` | **MR (type only)**: the sampler half of `SamplesEfficiently`; never instantiated in Phase A |
| `CoinSampler.fail` (+ `fail_eq`) | `CoinSampling/Basic.lean:106, 110` | **MR (type only)**: the failure bound in `SamplesEfficiently` |
| `encodeOption` (+ `_none`, `_some`) | `CoinSampling/Efficiency.lean:74, 79, 82` | R (if a field needs it) |
| `SamplesEfficiently` (shared file of Q-E1 (A), if at `<BASE>`) | `CoinSampling/Contract.lean` (proposed) | **MR when present**; otherwise a local `StructuredSeed/SamplerEfficiency.lean` with the same declaration |

Everything else in #378 is **not used, not re-created**. Phase A builds no sampler, proves no
sampler efficient, and does not import `Games.Closeness`. The samplers' laws stay exact
(design-r2 S2).

| Name | File:line | Status |
|---|---|---|
| `CoinSampler Ω s` (decoder `Fin s → Bool → Option Ω`, exact on success), `fail`, `pi`, `prod`, `ofRejection` | `CoinSampling/Basic.lean:93, 106, 322, 408, 451` | **X / B** |
| `bucket`, `fail_bucket_le`, `ofEquiv`, `weighted` | `CoinSampling/Buckets.lean:138, 176, 189, 228` | **X / B** |
| `zmod`, `fail_zmod_le`, `noiseSeeds`, `lweSeeds`, `statClose_lweSample_coins` | `CoinSampling/Instances.lean:56, 71, 95, 116, 148` | **X / B** (ℤ_p and LWE/LPN noise from coins) |
| `draw`, `drawD`, `close_draw_bind`, `close_drawD_bind`, `allOutputs_draw_bind` | `CoinSampling/Transfer.lean:73, 83, 106, 125, 163` | **X / B** |
| `drawSlack`, `negligible_drawSlack`, `subexpSmall_drawSlack`, `subexpSmall_polyExpr_mul` | `CoinSampling/Asymptotic.lean:99, 115, 123, 78` | **X / B** (do not use `subexpSmall_polyExpr_mul` as a shortcut either: Phase A takes the `2κ` factor through `SubexpSmall.mul_pow`, r2 §C) |
| `UniformSampler.toNUPPT`, `toNUPPT_runAt`, `bucketRaw`, `polyTimeComputable_bucketRaw`, `bucketSampler` | `CoinSampling/Efficiency.lean:117, 136, 169, 284, 308` | **X / B** (Phase B proves T5–T6 with them) |
| `Games.ProbComp.Close`, `Close.abs_prob_sub_le`, `advantage_le_of_close`, `OutputsSubset` | `Games/Closeness.lean:69, 143, 196, 217` | **X / B** (the job has no approximate laws) |

## Searches re-run for r3

- `git grep -n 'RealizesOn'` at `cdc0934f`: only `Asymptotic/Realization.lean` (the 14
  declarations above) and its facade line.
- `git grep -n 'Realiz'` under `TCSlib/Cryptography/Obfuscation/`: absent (the area does not
  exist at `<BASE>`).
- No new hit for LPN, structured-seed PRG, polynomial term-list encodings or a prime-parameter
  structure on either stacked branch (both add only the files listed).
