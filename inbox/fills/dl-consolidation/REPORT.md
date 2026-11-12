# dl-consolidation · checkpoint 3 (all groups: P, S, H, A, L, R, O)

**Worker** Claude. **Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` (`cryptography/pass-shelat-ch2-4`,
merge of #293). **Proof branch** `fill/dl-consolidation` (local). Checkpoint commits:
- `01b4f556b921c298749288e198cc9969816a9f83`: checkpoint 1, groups P, S, H;
- `d4639a1d198a12be407062641d9170b5aa634842`: checkpoint 2, groups A, L;
- `454c509ed662f939bc95a736c5a34b97a3d6ada8`: checkpoint 3, groups R, O.

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

**Re-pointing changes beyond renaming (A, L).**
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

### 2.3 Checkpoint 3: R (published readers), O (leftovers)

| Item | Disposition | Old → new |
|---|---|---|
| R1 | done | `AdaptiveCPA.indCodec_eq_bitCodec` → `FixedLengthPKScheme.indCodec_eq_bitCodec` (`Encryption/PublicKey/OracleSecurity.lean`); `PRFGame.indCodec_eq_bitCodec` (Transfer) → `FixedLengthScheme.indCodec_eq_bitCodec` (`Encryption/PrivateKey/OracleSecurity.lean`). Both are published readers beside `indCodec` with the same statement, proved by `rfl` in their home files (the copies went through the three codec readers and structure eta). 4 uses re-pointed. |
| R2 | done, nothing to re-point | `hybridPre_eq` (the defining equation, `rfl`) added beside `hybridPre` in `HybridMachine.lean`. At the base no BitwiseCPA file reads `hybridPre` (grep receipt R2: every hit is in `HybridMachine.lean`), so there is no reading to re-point. The related `BitwiseSim.plantTuple` is recorded in §6. |
| R3 | done, published in the cast form | The private `expect_simulate_indImpl_cpa` of `Encryption/PublicKey/OracleSecurity.lean` is now public under that name (`Composability.expect_simulate_indImpl_cpa`), with a formula docstring and sketch, and `BitwiseSim.expect_simulate_indImpl_cpa` (Eager) is deleted. See the note below for the statement. Its uses: `padded_cpa_advantage_eq` (unchanged proof) and BitwiseCPA's `accept_indGame_eq` (now passes the state `none`). |
| R4 | escalated | `BitwiseSim.padded_enc_runAt`, `padded_enc_coins` stay in `BitwiseCPA/Eager.lean`. See the note below. |
| R5 | done | `BitwiseSim.chRun_toCompOn_transport_list` → `ChallengeSim.chRun_toCompOn_transport_list` (same statement). `ChallengeSim.chRun_toCompOn_transport` keeps its name and statement and is derived from it with `G = fun _ => w`. |
| R6 | done | The private round-input readers `rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt` of `AdaptiveCPA/Handler` and `rU`, `rW`, `rS`, `rI`, `rX`, `rL`, `rCnt` of `OracleFromPRF/Handler` → one public set `Games.InteractiveHandler.rU … rCnt` beside `InteractiveHandler.input` (`Games/Efficiency.lean`), with the readers `rU_input … rCnt_input` (each field of `input n z ω s i x L`) and `polyTimeComputable_rU … _rCnt`. Both private `impl_of_ret` → one generic `Games.InteractiveHandler.impl_of_ret` (any handler, any `perCall`). Both private `replicate_one` → core `List.replicate_one` after core `Fin.val_one`; core has it, so no List lemma is added. |
| R7 | escalated (one function up to parameters) | See the note below. |
| O1 | done | The private `bitwise_runAtL` (BitwiseCPA) is deleted; `bitwise_runAt_blocks` now uses the published `BitPublicKeyScheme.bitwise_enc` and `bitwise_enc_runAtL` directly. The private `ofFn_half` is kept, because no published lemma states its shape (the selected half as `List.ofFn` of `getD`, which `bitwise_runAt_blocks` needs). It is re-proved from the published `FixedLengthScheme.ofFn_splitHalf_fst/_snd` instead of re-deriving them through `splitHalf_fst/_snd` and indices. |
| O2 | done | `cca2CtLen` deleted; its 2 uses read `prf_ctLen_eval` and `ctP_eval` from PRFStep. `cca2Gen` and `cca2Encrypt` keep their statements (their existential shapes are used by `obtain`), and are now one-line corollaries of PRFStep's `prf_gen_runAt`/`ofFn_prfKeyEq` and `ofFn_prf_encryptAt`/`ofFn_prfNonceEq`. `cca2Decrypt` vs `ofFn_prf_decAnswer` is not merged; the reason is in the note. |

**Re-pointing changes beyond renaming (R, O).**
- The `fields_input` lemmas of both handlers used to unfold the private readers by
  `simp only [InteractiveHandler.input_eq, rU, …]`. They now `simp only` with the published
  `rU_input, …, rCnt_input`.
- The three `have`s of `acHandler_impl_dec` are the published `rI_input`, `rU_input`, `rS_input`.
- The `have hU : PolyTimeComputable rU := hF.comp hF` lines of `polyTimeComputable_acRun/_pkRun` are
  now the published `polyTimeComputable_rU …`. The composition proof would read the published
  definitions through their bodies.
- At the 5 uses of `impl_of_ret`, `refine InteractiveHandler.impl_of_ret _ n z ω x s _ _ ?_` is
  followed by `show acRun S cap _ = _` (resp. `pkRun`). This reads the home file's `acHandler` and
  `pkHandler`.
- One reverse use `← replicate_one` (AdaptiveCPA, before `decodeBitMove_query`) is dropped: `exact`
  checks `[true] = List.replicate ↑(1 : Fin 2) true` definitionally, which unfolds only core
  definitions.
- In O2, the two `rw [cca2CtLen]` become `rw [prf_ctLen_eval, PRFGame.ctP_eval]`.

**Notes on the checkpoint-3 dispositions.**
- **R3, statement.** The private lemma's statement is
  `… (chRun (fun mm => … (if b then (splitHalf mm).2 else (splitHalf mm).1) …) c s)`, where
  `mm : (S.indSpec n).dom 1` is fed to `splitHalf` at type `Fin (m + m) → Bool`. That typechecks
  only by unfolding `indSpec` and `inLens`. A consumer instantiating it, as BitwiseCPA does, would
  read `OracleSecurity`'s definitions through their bodies (Rule 10).
  - The deleted copy read the domain through the published cast `indSpec_challengeDom`, but had
    the state fixed to `none`.
  - The published lemma combines the two: the OracleSecurity lemma with the general state `s`, and
    the halves read through `cast (S.indSpec_challengeDom n) mm`.
  - The two statements are definitionally equal (the cast is along a definitional equality). The
    lemma's proof is unchanged, and so is the proof of its home use `padded_cpa_advantage_eq`.
- **R4, escalated.**
  - **Obstruction: file size.** `Encryption/PublicKey/OracleSecurity.lean` is 982 lines at the base
    and 989 after R1 and R3 (the R1 reader, and the R3 docstring and `## Main results` lines).
  - The two readers need at least 15 lines beside the padded readers, even when stated with the
    section variables of `PublicKeyPaddedReaders`. That takes the file to at least 1004 lines,
    over the 1000-line limit.
  - They stay in `BitwiseCPA/Eager.lean`, which keeps only them, and their names are unchanged
    (`BitwiseSim.padded_enc_runAt`, `_coins`).
  - **Smallest correction.** Split `OracleSecurity.lean` by moving the padded constructor and its
    reader sections (`ofPadded`, `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`, about
    lines 249–460) into a child module `OracleSecurity/Padded.lean` that `OracleSecurity.lean`
    imports. Then add `PublicKeyScheme.padded_enc_runAt` and `_coins` there. This moves existing
    declarations between modules without renaming them, which this refactor was not asked to do.
- **R7, escalated.**
  - `recDin Lc = ![Lc, 2]`, `recDout Lc = ![2, Lc]` (`RecordHandler`),
    `acDin S = ![ctLen, msgLen + msgLen]`, `acDout S = ![msgLen + 1, ctLen]` (`AdaptiveCPA/Handler`)
    and `qDin Lc Lq = ![Lc, Lq]`, `qDout Ld Lc = ![Ld, Lc]` (`QueryHandler`) are one function up to
    parameters. `qDin` and `qDout` are themselves the generic two-entry vector, and the others are
    instances of it.
  - **Obstruction.** These definitions occur in the statements of public declarations: the handler
    types `PolyHandler 2 (recDin Lc) (recDout Lc)`, `acHandler`, `qHandler`, `exists_qHandlerMachine`,
    and every lemma about their lengths. Re-pointing the uses to one published function changes
    those statements.
  - Keeping the six names as thin wrappers of a published function would delete no copy of a
    declaration. Their readers (`recDin_zero`, …) would then read a foreign body, so it would only
    add an indirection.
  - **Smallest correction.** Publish one `Games.lens2 (a b : PolyExpr) : Fin 2 → PolyExpr` with
    `lens2_zero`/`lens2_one` (or use `![a, b]`) beside `bitSpecAt` in `Games/Efficiency.lean`. Then,
    in a statement-changing follow-up approved at the gate, replace the six definitions by it. The
    3-entry `pkDin`/`pkDout` (`OracleFromPRF/Handler`) is a different arity and is not a copy.
- **O2, not merged.** `cca2Decrypt` (`decodeFin n (Dec ⟨k, ⟨x, v⟩⟩) = some (v + F n k x)` for every
  `n`) and `ofFn_prf_decAnswer` (the oracle's answer list `decAnswer`, with the well-formedness test,
  for `n > 0`) have different statements and hypotheses. They share only the core step
  `runAt_prfDec`. Neither is a restatement of the other.

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

Checkpoint 3 adds no import line; the R6 consumers use `open … InteractiveHandler (rU …)`.

**Order** (`evidence/logs/order-cp2.txt` = `order-cp3.txt`, 408 modules):
- `Games/Probability` moved before `Games/BitCodec` (checkpoint 1).
- `Foundations/BitLists` inserted before its first consumer in the order, `Pseudorandom/NextBit`.
- The `Foundations` facade is not in `order.txt`; it is inserted right after `BitLists`, because it
  was edited.

## 4. Changed and new files (base → now, lines)

All files are below 1000 lines, except `ElGamal.lean`, which is 1835 lines at the base and is now
1829. 37 files: 36 changed and 1 new.

| File | Base | Now |
|---|---|---|
| `Games/Probability.lean` | 291 | 397 |
| `Games/Simulate.lean` | 276 | 327 |
| `Games/Hopping.lean` | 352 | 444 |
| `Games/BitCodec.lean` | 297 | 399 |
| `Games/Efficiency.lean` | 706 | 842 |
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
| `Encryption/PublicKey/HybridMachine.lean` | 393 | 411 |
| `Encryption/PublicKey/OracleSecurity.lean` | 982 | 989 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 274 | 315 |
| `Encryption/PublicKey/OracleSecurity/RecordHandler.lean` | 333 | 333 |
| `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean` | 411 | 289 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 596 | 543 |
| `Encryption/PublicKey/AdaptiveCPA/Games.lean` | 301 | 240 |
| `Encryption/PublicKey/AdaptiveCPA/Reduction.lean` | 274 | 275 |
| `Encryption/PublicKey/BitwiseCPA.lean` | 558 | 552 |
| `Encryption/PublicKey/BitwiseCPA/Eager.lean` | 167 | 59 |
| `Encryption/PublicKey/BitwiseCPA/Planted.lean` | 323 | 304 |
| `Encryption/PublicKey/BitwiseCPA/QueryHandler.lean` | 402 | 369 |
| `Encryption/PrivateKey/OracleSecurity.lean` | 374 | 400 |
| `Encryption/PrivateKey/OracleFromPRF.lean` | 886 | 859 |
| `Encryption/PrivateKey/OracleFromPRF/Collision.lean` | 514 | 401 |
| `Encryption/PrivateKey/OracleFromPRF/Games.lean` | 329 | 307 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 753 | 702 |
| `Encryption/PrivateKey/OracleFromPRF/Lazy.lean` | 484 | 476 |
| `Encryption/PrivateKey/OracleFromPRF/Reduction.lean` | 367 | 338 |
| `Encryption/PrivateKey/OracleFromPRF/Transfer.lean` | 202 | 163 |

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
- **Checkpoint 3 rebuild** (`rebuild-cp3.log`, list `rebuild-cp3-list.txt`, order `order-cp3.txt`).
  From `Encryption/PublicKey/HybridMachine`, the first edited module (position 157), to the end:
  **252/252 modules, status 0**.
  - The sorry warnings are exactly the `base-sorries.txt` lines of those modules: 17 modules,
    29 sorries.
  - The non-sorry warnings are identical to the bootstrap's: 62 = 62.
- **Lint** (`lint-cp1.log`, `lint-cp2.log`, `lint-cp3.log`). Checkpoints 2 and 3 each give 190 FAIL,
  103 WARN over 287 files.
  The FAIL/WARN lines are identical to `lint-base.log` except one: the existing ElGamal size WARN now
  reads 1829 lines instead of 1835.
- **Grep receipts** (`evidence/grep-receipts.txt`). One search per item over `TCSlib` and `audits` at
  the base, all groups, with every hit. `audits/` uses none of the moved names.
- **Tools** (`evidence/tools/`). The final report will describe them.

## 6. Further duplication found

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
- **`AdaptiveCPA`'s private `rFwd` and `PRFGame`'s private `rY` are one reader**:
  `pairSndD (pairSndD (pairFstD (rL w)))`, the answer of the first entry of the outer log. They are
  not folded, because they are not among the listed R6 readers: a published version reads the
  outer codec's log encoding, not `InteractiveHandler.input`, so it would need its own reader on
  `encodeLog [⟨j, x, y⟩]`.
- **`PRFGame`'s private `impl_of_query`** (one outer query, then return) has an inline counterpart
  in `AdaptiveCPA.acHandler_impl_forward`. It is a candidate for a generic
  `InteractiveHandler.impl_of_query`, beside the published `impl_of_ret`.
- **PublicKey/OracleSecurity's private `ofFn_splitHalf_bit`** is the one-bit case of BitwiseCPA's
  private `ofFn_half`. Both are private, in files of different chapters, and outside the listed
  items.

## 7. Next

The final delivery:
- the fresh sweep at the final head;
- the census against the base and the name map;
- the axioms;
- the whole-file closure seals of the 37 files, with base controls and paired controls (with and
  without `PolyExpr.eval` sealed);
- the explicit-unfold scan;
- lint.
