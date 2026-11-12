# dl-consolidation · checkpoint 1 (groups P, S, H)

**Worker** Claude. **Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` (`cryptography/pass-shelat-ch2-4`,
merge of #293). **Proof branch** `fill/dl-consolidation` (local), checkpoint commit
`01b4f556b921c298749288e198cc9969816a9f83`. Lean 4.25.0 and the Mathlib pin of the base manifest.

This is a checkpoint. The final delivery will replace this report with the full one: census, axioms,
seals, unfold scan and the fresh sweep.

## 1. Environment

- Pack verified at exchange `abbcb1127`: all `SHA256SUMS` OK. All 406 sources of the base match
  `SOURCE-SHA256SUMS` (`evidence/logs/source-sha256.log`).
- Separate checkout: a git worktree at `fill/dl-consolidation`, with its own `.lake/packages`.
- Narrowed Mathlib cache fetch of the 112 roots of `roots.txt` (`cache-get.log`, exit 0).
  `packages-check.log` and `cache-probe.log` confirm that the packages match the manifest.
- Preflight passes (`preflight.log`).
- No `lake build` was run. Each check is one module per `scripts/lean_check_tree.sh` call, with one
  Lean process at a time.
- **Bootstrap** (`bootstrap.log`): 406/406 modules, status 0. Its sorry census
  (`sorry-census-bootstrap.txt`) is `base-sorries.txt`: 48 in 26 modules.
- **Base declaration dump** (`decl-dump-base.log`): 1896 constants of the 35 candidate modules, plus
  the axioms of the nine campaign endpoints. Every endpoint is `[propext, Classical.choice, Quot.sound]`.
- **Base lint** (`lint-base.log`): 190 FAIL, 103 WARN over 286 files.

## 2. Items of this checkpoint

`Games.ProbComp` below is `TCSlib.Cryptography.Games.ProbComp`. Old names are given in full under
`TCSlib.Cryptography.Composability`.

| Item | Disposition | Old → new |
|---|---|---|
| P1 | done | `ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` → `Games.ProbComp.` same names, in `Games/Probability.lean` (new section `Sampling`) |
| P2 | not a copy, kept | `ChallengeSim.expect_sample_prod` (`𝔼_{α×β} g = 𝔼_a 𝔼_b g (a, b)`) is a corollary of `Bridge.expect_sample_pair` (`𝔼 (bind-of-two-samples-then-pure) g = 𝔼_{α×β} g`), not a restatement: its proof is that lemma plus `expect_bind`/`expect_pure`. It stays in ChallengeSim. |
| P3 | done | `BitwiseSim.expect_sample_update` (general `ι`) → `Games.ProbComp.expect_sample_update`. `AdaptiveCPA.expect_sample_update` (`Fin κ`) → `Games.ProbComp.expect_sample_coord`, generalized to any finite `ι` and derived from the general form with `expect_sample_comm`. The names are distinct. |
| P4 | done | `PRFGame.abs_expect_sub_le` → `Games.ProbComp.abs_expect_sub_le` |
| S1 | done (both kept, see note) | `PRFGame.simulate_eq_of_abs_bounded` → `Games.simulate_eq_of_abs_bounded`; `AdaptiveCPA.simulate_eq_of_abs` → `Games.simulate_eq_of_abs` (`Games/Simulate.lean`) |
| S2 | done | `AdaptiveCPA.castImpl`, `castImpl_eq`, `castImpl_self`, `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn` → `Games.` same names (`Games/BitCodec.lean`, section `Transport`) |
| S3a | done | `PRFGame.expect_simulate_congr` → `Games.ProbComp.expect_simulate_congr` (`Games/Hopping.lean`) |
| S3b | escalated, moved to ChallengeSim | `BitwiseSim.expect_simulate_eager` → `ChallengeSim.expect_simulate_eager` |
| H1 | done | `PRFGame.prob_bad_le`, `PRFGame.expect_sample_mem_le` → `Games.ProbComp.` same names (`Games/Hopping.lean`). The `prob_bad_le` docstring states the per-query potential bound `Pr[bad] ≤ q·(size + q)·δ`. |

All copies were deleted, with no aliases. All uses were re-pointed:
- `AdaptiveCPA.expect_sample_update` → `expect_sample_coord` in `AdaptiveCPA/Hybrid` and
  `OracleFromPRF/Games`;
- `BitwiseSim.expect_sample_update` → `ProbComp.expect_sample_update` in `OracleFromPRF/Lazy`;
- the rest resolve to the new names unchanged through the enclosing namespaces and `open`s.

Docstrings that cited the old names were updated (`OracleFromPRF.lean`, `BitwiseCPA.lean`, `Eager.lean`,
`Collision.lean`, `Hybrid.lean`). Every module docstring's main-results or contents list that names a
moved declaration was updated. `audits/` uses none of these names (grep receipt).

**Notes on the dispositions.**
- **S1, both forms kept.** The brief asks to derive `simulate_eq_of_abs` from the bounded form, or to
  re-point its uses and delete it. Neither is possible without a statement change, because the
  bounded form does not generalize the unbounded one:
  - The bounded form assumes that every call of `impl₂` below the budget is a deterministic
    `.pure (y, s')`, and that the computation has a query bound `c.CostBoundedBy (fun _ => 1) m`
    with `cnt s + m ≤ κ`.
  - `simulate_eq_of_abs` allows any probabilistic `impl₂` (`impl₁ i x (f s) = (impl₂ i x s).bind …`)
    and any computation.
  - Its one use (`AdaptiveCPA/Reduction`, private `prob_red_tape`) applies it to the reduction's
    handler composed with the CPA oracle, which samples. That lemma's statement has no query budget.

  Both forms now live side by side in `Games/Simulate.lean`, with no copy left anywhere else.
- **S3b, escalated.**
  - **Obstruction.** The statement of `expect_simulate_eager` is about `ChallengeSim.chRun`, which
    is defined in `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`. No Games module can state
    it without importing a downstream module.
  - **Smallest correction.** Give it its home beside `chRun` in `ChallengeSim`. This is the
    lowest module whose imports cover the statement. It is no longer a BitwiseCPA-local lemma.
- **S2.** `castImpl`'s type uses `unifSpec` and `ProbComp`. These are not in `BitCodec`'s base
  imports, so `Games/BitCodec.lean` now imports `TCSlib.Cryptography.Games.Probability` (see §3).

## 3. Import changes

| Module | Added import | Reason | Acyclic |
|---|---|---|---|
| `Games/BitCodec.lean` | `TCSlib.Cryptography.Games.Probability` | `castImpl` (S2) is a `QueryImpl … unifSpec`, and its readers use `ProbComp.expect`. | yes: `Games/Probability` imports only `Games/Simulate`, `Games/Machines` and Mathlib, never `BitCodec` |

The sweep order moves `Games/Probability` before `Games/BitCodec` (`evidence/logs/order-cp1.txt`).
No other order change.

## 4. Changed files (base → checkpoint lines; all below 1000)

| File | Base | Now |
|---|---|---|
| `Games/Probability.lean` | 291 | 397 |
| `Games/Simulate.lean` | 276 | 327 |
| `Games/Hopping.lean` | 352 | 444 |
| `Games/BitCodec.lean` | 297 | 370 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 274 | 295 |
| `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean` | 411 | 289 |
| `Encryption/PublicKey/BitwiseCPA/Eager.lean` | 167 | 86 |
| `Encryption/PublicKey/BitwiseCPA.lean` (docstring) | 558 | 558 |
| `Encryption/PrivateKey/OracleFromPRF/Collision.lean` | 514 | 426 |
| `Encryption/PrivateKey/OracleFromPRF/Games.lean` | 329 | 307 |
| `Encryption/PrivateKey/OracleFromPRF/Reduction.lean` | 367 | 337 |
| `Encryption/PrivateKey/OracleFromPRF/Lazy.lean` (re-pointing) | 484 | 484 |
| `Encryption/PrivateKey/OracleFromPRF.lean` (docstrings) | 886 | 886 |

## 5. Checkpoint evidence

- **Rebuild** (`evidence/logs/rebuild-cp1.log`, list `rebuild-cp1-list.txt`). The first edited module
  in the order is `Games/Simulate` (position 162 of `order-cp1.txt`). That module and everything after
  it were rebuilt: **245/245 modules, status 0**.
- **Admissions.** The sorry warnings of the rebuilt modules are exactly the `base-sorries.txt` lines of
  those modules: 17 modules, 29 sorries, identical names. The other 9 base lines are in modules
  before `Games/Simulate`, which were not rebuilt.
- **Other warnings.** The non-sorry warnings of the rebuilt modules are identical to the bootstrap's
  for the same modules: 61 = 61, none new, none gone.
- **Lint** (`evidence/logs/lint-cp1.log`). 190 FAIL, 103 WARN over 286 files. The FAIL/WARN lines are
  identical to `lint-base.log`.
- **Grep receipts** (`evidence/grep-receipts.txt`). One search per item over `TCSlib` and `audits` at
  the base, all groups, with every hit.
- **Tools** (`evidence/tools/`): `check.sh`, `sweep_chunk.sh`, `mk.py`, `census.py`, `blk.py`,
  `mkdump.py`, `payload.sh`.

## 6. Further copies found so far (P, S, H)

- The grep receipts found no further copy of P1, P4, S1–S3 or H1 under another name.
- `ChallengeSim.expect_sample_prod` is related to `Bridge.expect_sample_pair` (P2 above).

## 7. Next

- **Checkpoint 2** (groups A, L).
  - Create the new module `Foundations/BitLists.lean`, with Mathlib imports only.
  - Promote the `padFin`/`blocks` readers to `Asymptotic/Adversary.lean`, the `zeroBits` readers to
    `Games/BitCodec.lean`, and `ofFn_padFin_eq_padL` to `Asymptotic/EnsemblesLemmas.lean`.
  - Move `ofFn_splitHalf_fst/_snd` to `Encryption/PrivateKey/OracleSecurity.lean`.
- **Checkpoint 3** (groups R, O).
