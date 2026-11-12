# dl-consolidation · checkpoint 2 (groups P, S, H, A, L)

**Worker** Claude. **Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` (`cryptography/pass-shelat-ch2-4`,
merge of #293). **Proof branch** `fill/dl-consolidation` (local). Checkpoint commits:
- `01b4f556b921c298749288e198cc9969816a9f83`: checkpoint 1, groups P, S, H;
- `d4639a1d198a12be407062641d9170b5aa634842`: checkpoint 2, groups A, L.

Lean 4.25.0 and the Mathlib pin of the base manifest.

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

## 2. Items

`Games.ProbComp` is `TCSlib.Cryptography.Games.ProbComp`. Unqualified old names are under
`TCSlib.Cryptography.Composability`, and new names without a prefix are under `TCSlib.Cryptography`.

### 2.1 Checkpoint 1: P, S, H (Games layer)

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

**Notes on the checkpoint-1 dispositions.**
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

### 2.2 Checkpoint 2: A (padFin, blocks), L (shared list module)

| Item | Disposition | Old → new |
|---|---|---|
| A1 | done | `ofFn_padFin_of_length` (public, `Asymptotic/HardCoreGLColl.lean`) moved to `Asymptotic/Adversary.lean` beside `padFin`. Full name and statement are unchanged. Deleted: `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`, public) and ElGamal's private `dlc_ofFn_padFin`. 52 uses of the GGM name and 5 of the ElGamal name (2 in proofs, 3 in docstrings) were re-pointed. |
| A1′ | not used as the home | `Collection.ofFn_padFin_of_le` (`List.ofFn (padFin ℓ w) = w ++ 0^(ℓ - |w|)` for `|w| ≤ ℓ`) does not subsume A1 as a drop-in: getting the equality form takes three more rewrites (`h`, `Nat.sub_self`, `replicate_zero`, `append_nil`), which is exactly the deleted ElGamal copy. A1's 57 users need the equality form, and `ofFn_padFin_of_le` keeps its own users (Lamport, EncryptThenTag, the two Handlers). |
| A2 | done | `AdaptiveCPA.ofFn_cast` → `ofFn_cast` (`Adversary.lean`). The private `cca2OfFn_cast` (`OracleFromPRF.lean`) was deleted, and its 4 uses plus 9 uses of the AdaptiveCPA name were re-pointed. |
| A3 | done, home split | `ofFn_arrowCongr_finCongr` (`PRFGame`, Transfer) → `ofFn_arrowCongr_finCongr` (`Adversary.lean`). `AdaptiveCPA.padFin_ofFn_zeroBits`, `PRFGame.padFin_replicate_false` and `PRFGame.padFin_nil` → `Games.` same names (`Games/BitCodec.lean`, beside `zeroBits`). These three mention `zeroBits`, which is defined in `Games/BitCodec.lean`, downstream of `Adversary`. `BitCodec` imports `Adversary`, so they go beside `zeroBits`. Their docstrings say so; the brief allows `Games/BitCodec.lean` for group A. |
| A4 | done | Private `ofFn_padFin_eq_padL` in `AdaptiveCPA/Handler` and in `OracleFromPRF/Handler` → public `EnsembleLemmas.ofFn_padFin_eq_padL` beside `padL`. It holds by `rfl`, since `padL` is its home file's definition. |
| A5 | done | New `FunFamily.ofFn_blocks`: `⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`, beside `FunFamily.blocks` in `Adversary.lean`, read through `FunFamily.blocks_apply`. `AdaptiveCPA.ofFn_acTapes` and `PRFGame.ofFn_pkTapes` keep their names and statements, and are now derived from it. `ofFn_pkTapes` goes through `EnsembleLemmas.blocks_eq` and `ofFn_arrowCongr_finCongr`. |
| A6 | done | `BitwiseSim.decodeFin_nil_getD` → `Games.decodeFin_nil_getD` (`Games/BitCodec.lean`; it mentions `zeroBits`) |
| L1 | done | New module `Foundations/BitLists.lean` (Mathlib imports only). `headD_drop` is generalized to lists over any type, `(l.drop i).headD d = l.getD i d`. It replaces `CommitmentLemmas.headD_drop`, `BitwiseSim.headD_drop` (the `d = false` form), NextBit's private `headD_drop_ofFn`, and the further copy `GI.getD_eq_headD_drop` (reversed, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`, found by grep). |
| L2 | done | `BitwiseSim.flatten_ofFn_singleton` and Yao's private `flatten_ofFn_one` → `flatten_ofFn_one` (general blocks, Yao's form) and `flatten_ofFn_singleton` (constant blocks, derived from it), in BitLists |
| L3 | done | `AdaptiveCPA.headD_ofFn_one` → `headD_ofFn_one` (BitLists) |
| L4 | done | `PRFGame.zipWith_xor_cancel_left` → `zipWith_xor_cancel_left` (BitLists) |
| L5 | done | `PRFGame.xorPerm`, `PRFGame.xorPerm_apply` → `xorPerm`, `xorPerm_apply` (BitLists). `ctOf_xorPerm` stays in Collision. |
| L6 | done, promoted | `PRFGame.mem_keys_of_lookup_isSome` → `mem_keys_of_lookup_isSome` (BitLists). Core's `List.lookup_isSome_iff` exists at the pin, but it states `(l.lookup k).isSome ↔ ∃ p ∈ l, k == p.1`, not membership in `l.map Prod.fst`. Using it at the one use would change that proof beyond a re-pointing, so the lemma is promoted and re-proved through the core lemma (`List.mem_map`). |
| L7 | done | `AdaptiveCPA.ofFn_splitHalf_fst`, `_snd` → `FixedLengthScheme.ofFn_splitHalf_fst`, `_snd`, beside `splitHalf` in `Encryption/PrivateKey/OracleSecurity.lean`, read through `splitHalf_fst/_snd` |

**Re-pointing changes beyond renaming.**
- NextBit's one use of `headD_drop_ofFn` (a `rw` list) became
  `headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, closed by the existing `simp`.
- The ZK uses of `getD_eq_headD_drop` flip direction:
  - `getD_eq_headD_drop` becomes `← headD_drop` (2 uses);
  - `← getD_eq_headD_drop` becomes `headD_drop` (3 uses).

  Each rewrites the same pattern.
- `Games.padFin_ofFn_zeroBits` is re-proved by `getD_eq_getElem?_getD` and `getElem?_replicate`. The
  base proof used `List.getD_eq_getElem`/`getD_eq_default` from `Mathlib.Data.List.GetD`, which
  `BitCodec` does not import, and this way it needs no Mathlib import.
- Lines that became longer than 100 characters after a renaming were re-wrapped.

**L, the module choice.**
- The lemmas need only `Mathlib.Data.List.{OfFn,GetD}` and `Mathlib.Logic.Equiv.Prod`. All three are
  in `roots.txt`.
- No existing module fits:
  - `Foundations/` has no list module.
  - The only upstream homes for generic list lemmas are outside `TCSlib/Cryptography/` (out of
    scope).
  - Every cryptographic module that already holds some of these lemmas imports large parts of the
    library.
- `BitLists` is imported by its 11 consumers and listed in the `Foundations` facade's `## Contents`.

## 3. Import changes

| Module | Added import | Reason | Acyclic |
|---|---|---|---|
| `Games/BitCodec.lean` | `TCSlib.Cryptography.Games.Probability` | `castImpl` (S2) is a `QueryImpl … unifSpec`, and its readers use `ProbComp.expect` | yes: `Games/Probability` imports only `Games/Simulate`, `Games/Machines` and Mathlib, never `BitCodec` |
| `Foundations.lean` (facade) | `TCSlib.Cryptography.Foundations.BitLists` | the facade imports every child (lint rule) | yes: `BitLists` imports only Mathlib |
| new `Foundations/BitLists.lean` | `Mathlib.Data.List.OfFn`, `Mathlib.Data.List.GetD`, `Mathlib.Logic.Equiv.Prod` | the L lemmas | Mathlib only |
| consumers (not Games/Asymptotic/Foundations) | `TCSlib.Cryptography.Foundations.BitLists` | the L lemmas they use | yes |

The consumers are `AdaptiveCPA/{Games,Reduction}`, `BitwiseCPA/Planted`,
`OracleFromPRF{,/Reduction,/Lazy,/Collision}`, `Pseudorandom/NextBit`, `SecureComputation/Yao`,
`ZeroKnowledge/CommitmentLemmas` and `ZeroKnowledge/GraphIsomorphism/EfficiencyRep{,GI}`.

**Order** (`evidence/logs/order-cp2.txt`, 408 modules):
- `Games/Probability` moved before `Games/BitCodec` (checkpoint 1).
- `Foundations/BitLists` inserted before its first consumer in the order, `Pseudorandom/NextBit`.
- The `Foundations` facade is not in `order.txt`; it is inserted right after `BitLists`, because it
  was edited.

## 4. Changed and new files (base → now, lines)

All files are below 1000 lines, except `ElGamal.lean`, which is 1835 lines at the base and is now
1829.

| File | Base | Now |
|---|---|---|
| `Games/Probability.lean` | 291 | 397 |
| `Games/Simulate.lean` | 276 | 327 |
| `Games/Hopping.lean` | 352 | 444 |
| `Games/BitCodec.lean` | 297 | 399 |
| `Foundations.lean` | 32 | 35 |
| `Foundations/BitLists.lean` (new) | — | 105 |
| `Asymptotic/Adversary.lean` | 323 | 373 |
| `Asymptotic/EnsemblesLemmas.lean` | 860 | 865 |
| `Asymptotic/HardCoreGLColl.lean` | 405 | 399 |
| `Pseudorandom/Functions/Asymptotic/GGM/Run.lean` | 779 | 773 |
| `Pseudorandom/NextBit.lean` | 470 | 464 |
| `SecureComputation/Yao.lean` | 951 | 942 |
| `ZeroKnowledge/CommitmentLemmas.lean` | 506 | 503 |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | 639 | 636 |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean` | 334 | 335 |
| `Encryption/PublicKey/ElGamal.lean` | 1835 | 1829 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 274 | 295 |
| `Encryption/PublicKey/OracleSecurity/RecordHandler.lean` | 333 | 333 |
| `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean` | 411 | 289 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 596 | 576 |
| `Encryption/PublicKey/AdaptiveCPA/Games.lean` | 301 | 261 |
| `Encryption/PublicKey/AdaptiveCPA/Reduction.lean` | 274 | 275 |
| `Encryption/PublicKey/BitwiseCPA.lean` | 558 | 558 |
| `Encryption/PublicKey/BitwiseCPA/Eager.lean` | 167 | 86 |
| `Encryption/PublicKey/BitwiseCPA/Planted.lean` | 323 | 304 |
| `Encryption/PublicKey/BitwiseCPA/QueryHandler.lean` | 402 | 391 |
| `Encryption/PrivateKey/OracleSecurity.lean` | 374 | 396 |
| `Encryption/PrivateKey/OracleFromPRF.lean` | 886 | 880 |
| `Encryption/PrivateKey/OracleFromPRF/Collision.lean` | 514 | 401 |
| `Encryption/PrivateKey/OracleFromPRF/Games.lean` | 329 | 307 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 753 | 734 |
| `Encryption/PrivateKey/OracleFromPRF/Lazy.lean` | 484 | 476 |
| `Encryption/PrivateKey/OracleFromPRF/Reduction.lean` | 367 | 338 |
| `Encryption/PrivateKey/OracleFromPRF/Transfer.lean` | 202 | 183 |

## 5. Checkpoint evidence

- **Checkpoint 1 rebuild** (`rebuild-cp1.log`, list `rebuild-cp1-list.txt`, order `order-cp1.txt`).
  From `Games/Simulate`, the first edited module (position 162), to the end: **245/245 modules,
  status 0**.
  - The sorry warnings are exactly the `base-sorries.txt` lines of those modules: 17 modules,
    29 sorries.
  - The non-sorry warnings are identical to the bootstrap's: 61 = 61.
- **Checkpoint 2 rebuild** (`rebuild-cp2.log`, list `rebuild-cp2-list.txt`, order `order-cp2.txt`).
  From `Asymptotic/Adversary`, the first edited module (position 34), to the end: **375/375 modules,
  status 0**.
  - The sorry warnings are exactly the `base-sorries.txt` lines of those modules: 19 modules,
    31 sorries, identical names.
  - The other 7 base lines are in `TCSlib/Complexity` modules before `Adversary`.
  - The non-sorry warnings are identical to the bootstrap's for the same modules: 113 = 113, none
    new, none gone.
- **Lint** (`lint-cp1.log`, `lint-cp2.log`). Checkpoint 2 gives 190 FAIL, 103 WARN over 287 files.
  The FAIL/WARN lines are identical to `lint-base.log` except one: the existing ElGamal size WARN now
  reads 1829 lines instead of 1835.
- **Grep receipts** (`evidence/grep-receipts.txt`). One search per item over `TCSlib` and `audits` at
  the base, all groups, with every hit. `audits/` uses none of the moved names.
- **Tools** (`evidence/tools/`). The final report will describe them.

## 6. Further duplication found (so far)

Recorded, not folded: each one is outside the listed items, or folding it would change statements or
proofs beyond re-pointing.

- **The generic window of a block** has several further forms.
  - `OneWay.ofFn_block_eq_take_drop` (`Asymptotic/OneWayLemmas.lean`) states the A5 fact for
    `fun j => x (finProdFinEquiv (i, j))`. That function is `FunFamily.blocks q ℓ x i` only up to
    unfolding, so its users' `rw`s could not be re-pointed by name.
  - `EnsembleLemmas.take_drop_ofFn_blocks` is the A5 fact reversed, for the `blocks` alias in
    `EnsemblesLemmas`, which is out of scope.
  - `take_drop_ofFn_blocks` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean`, public) is
    derived from the EnsemblesLemmas one.
  - Local `have`s in `Candidates/Factoring.lean` (`fac_ofFn_halves`) and Primality's private
    `ofFn_chunk` restate it.
- **`ofFn_arrowCongr_finCongr`** has further copies:
  - the private `ofFn_arrowCongr` in `Asymptotic/UniversalPadding.lean`;
  - local `hofn` haves in `Candidates/Factoring.lean` and `ZeroKnowledge/ThreeColoring/ColZKMachine.lean`.
- **`EnsembleLemmas.padL_eq`** is `ofFn_padFin_eq_take` (`CollectionsLemmas`) read through `padL`.
- **The local `hA`/`hB` haves in `EncryptThenTag.lean`** restate A1 through `ofFn_padFin_of_le`.
- **BitwiseCPA/Planted.** `plantTuple` re-implements the `hybridPre` layout (`HybridMachine`), with a
  different input layout. This is for R2.
- **The ZeroKnowledge `GI.getD_eq_headD_drop` was folded** (L1 above).

## 7. Next

- **Checkpoint 3**, groups R and O:
  - publish the readers R1–R6;
  - decide R7;
  - make the O1 and O2 merges.
- **Then the final delivery**:
  - the fresh sweep;
  - the census;
  - the axioms;
  - the whole-file closure seals, with base controls and paired controls;
  - the explicit-unfold scan;
  - lint.
