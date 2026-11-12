# dl-consolidation · final delivery (DL-30 to DL-34)

**Worker** Claude. **Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` (`cryptography/pass-shelat-ch2-4`,
merge of #293). **Proof branch** `fill/dl-consolidation` (local). **Final head**
`6917e5716066b858a4dbdc33cf7f8653f9a40aa5`, which is 4 commits on the base:

| Commit | Content |
|---|---|
| `01b4f556b` | checkpoint 1: groups P, S, H (Games layer) |
| `d4639a1d1` | checkpoint 2: groups A, L (padFin and blocks readers, new `Foundations/BitLists`) |
| `454c509ed` | checkpoint 3: groups R, O (published readers, leftovers) |
| `6917e5716` | after checkpoint 3: R3 restated through `ChallengeSim.expect_simulate_eager` (this fixed a seal finding), R4 done, the emptied `BitwiseCPA/Eager` module removed |

Lean 4.25.0 and the Mathlib pin of the base manifest.

**Result.**
- 28 items are done, P2 is not a copy, and S3b and R7 are escalated with their obstruction and
  smallest correction.
- S1 is done with both forms kept, with a reason.
- No audited statement changed.
- The fresh sweep of all 407 modules passes, and the sorry census equals `base-sorries.txt`.
- Every stored constant of the changed and new files, and every campaign endpoint, uses only
  `propext`, `Classical.choice` and `Quot.sound`. The exception is the 4 Yao constants that rest on
  the base's admitted sorries, unchanged from the base.
- The whole-file closure seals introduce no new reading through a foreign body. Two pre-existing
  failures (`cca2Encrypt`, `cca2Gen`, the Gate 17 finding) are gone.
- Lint has no new FAIL, and two fewer than the base.

## 1. Environment and method

- **Pack.** Verified at exchange `abbcb1127`: all `SHA256SUMS` OK. All 406 sources of the base match
  `SOURCE-SHA256SUMS` (`evidence/logs/source-sha256.log`).
- **Checkout.** A separate git worktree at `fill/dl-consolidation`, with its own `.lake/packages`.
  - Narrowed Mathlib cache fetch of the 112 roots of `roots.txt` (`cache-get.log`, exit 0).
  - `packages-check.log` and `cache-probe.log` confirm that the packages match the manifest.
  - Preflight passes (`preflight.log`).
- **Checking.**
  - No `lake build` was run.
  - Every check is one module per `scripts/lean_check_tree.sh` call, with one Lean process at a
    time (`evidence/tools/check.sh`, `sweep_chunk.sh`, `mk.py`).
  - The repository's `AGENTS.md` asks for VS Code's infoview instead of command-line checks. That
    is not available here, and the brief and the environment addendum prescribe exactly these
    `lean_check_tree.sh` checks.
- **Bootstrap** (`bootstrap.log`): 406/406 modules, status 0. Its sorry census
  (`sorry-census-bootstrap.txt`) is `base-sorries.txt`: 48 in 26 modules.
- **Base tree for the controls** (`base-tree.log`). A second worktree, detached at the base, with
  its own olean tree and the same packages, built from `order.txt`: 406/406, status 0. It provides
  the base controls (§7) and the extended base dump (§5).

## 2. Items

`Games.ProbComp` is `TCSlib.Cryptography.Games.ProbComp`. Unqualified old names are under
`TCSlib.Cryptography.Composability`, and new names without a prefix are under `TCSlib.Cryptography`.
The census (§5) checks every row of this table against the declaration dumps.

### 2.1 P, S, H (Games layer; checkpoint 1)

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

**Notes on P, S, H.**
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

### 2.2 A (padFin, blocks), L (shared list module; checkpoint 2)

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

### 2.3 R (published readers), O (leftovers; checkpoint 3 and after)

| Item | Disposition | Old → new |
|---|---|---|
| R1 | done | `AdaptiveCPA.indCodec_eq_bitCodec` → `FixedLengthPKScheme.indCodec_eq_bitCodec` (`Encryption/PublicKey/OracleSecurity.lean`); `PRFGame.indCodec_eq_bitCodec` (Transfer) → `FixedLengthScheme.indCodec_eq_bitCodec` (`Encryption/PrivateKey/OracleSecurity.lean`). Both are published readers beside `indCodec` with the same statement, proved by `rfl` in their home files (the copies went through the three codec readers and structure eta). 4 uses re-pointed. |
| R2 | done, nothing to re-point | `hybridPre_eq` (the defining equation, `rfl`) added beside `hybridPre` in `HybridMachine.lean`. At the base no BitwiseCPA file reads `hybridPre` (grep receipt R2: every hit is in `HybridMachine.lean`), so there is no reading to re-point. The related `BitwiseSim.plantTuple` is recorded in §11. |
| R3 | done; statement read through readers | The private `expect_simulate_indImpl_cpa` of `Encryption/PublicKey/OracleSecurity.lean` is published under that name (`Composability.expect_simulate_indImpl_cpa`), with a formula docstring and a sketch. `BitwiseSim.expect_simulate_indImpl_cpa` (Eager) is deleted. The published lemma keeps the general state `s`, and reads the halves and the record through `indSpec_challengeDom`/`indSpec_challengeRng`. It is now a corollary of the generic `ChallengeSim.expect_simulate_eager`, which removes a second copy of the eager induction. See the note. Its uses: `padded_cpa_advantage_eq` (proof unchanged) and BitwiseCPA's `accept_indGame_eq` (now passes the state `none`). |
| R4 | done (after checkpoint 3) | `BitwiseSim.padded_enc_runAt`, `padded_enc_coins` → `PublicKeyScheme.padded_enc_runAt`, `PublicKeyScheme.padded_enc_coins`, beside the padded readers (section `PublicKeyPaddedReaders` of `Encryption/PublicKey/OracleSecurity.lean`). They take the section's variables, in the same argument order. At checkpoint 3 this was escalated for file size; R3's re-proof freed 19 lines, so the file is 987 lines with them. `BitwiseCPA/Eager.lean` was left empty and is removed (see §3). |
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

**Notes on R, O.**
- **R3, statement.** The private lemma's statement is
  `… (chRun (fun mm => … (splitHalf mm) …) c s)`, which typechecks only by unfolding `indSpec`,
  `inLens` and `outLens`:
  - `mm : (S.indSpec n).dom 1` is fed to `splitHalf` at type `Fin (m + m) → Bool`;
  - the state `s : Option (Fin (ctLen n) → Bool)` is fed to `chRun` at type
    `Option (Fin (outLens n 1) → Bool)`.

  A consumer instantiating it, as BitwiseCPA does, would read `OracleSecurity`'s definitions
  through their bodies.
  - **The seal caught this.** The checkpoint-3 form had fixed the halves, but still passed `s`
    directly. The final-head seal of `BitwiseCPA.lean` failed at `accept_indGame_eq`, on exactly
    that state type (`seal-final.out` at `454c509ed`, kept in the dev logs).
  - **The final statement** reads both through the published casts:
    `cast (S.indSpec_challengeDom n) mm`, and the state `s.map (cast (S.indSpec_challengeRng n).symm)`.
    This is the shape of `ChallengeSim.expect_simulate_eager`, so the lemma is that generic lemma
    instantiated with the published oracle equations `indImpl_*_onSpec`. That is the proof the
    deleted BitwiseSim copy had, for the state `none`.
  - The private induction that re-proved the generic eager lemma is gone.
  - With `s = none`, the statement is the deleted copy's, up to `none.map f ≡ none`.
  - Both seals now pass.
- **R4.** At checkpoint 3, `OracleSecurity.lean` would have exceeded 1000 lines with the readers
  (989 + at least 15). The R3 re-proof through `ChallengeSim.expect_simulate_eager` replaced the
  private induction and freed 19 lines (970), so R4 was done: the file is 987 lines, below the
  limit.
  `BitwiseCPA/Eager.lean` held nothing else and was removed. Its two importers now import its only
  import, `OracleSecurity`, or nothing, so no import closure changes.
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

| Module | Change | Reason | Acyclic |
|---|---|---|---|
| `Games/BitCodec.lean` | + `TCSlib.Cryptography.Games.Probability` | `castImpl` (S2) is a `QueryImpl … unifSpec`, and its readers use `ProbComp.expect` | yes: `Games/Probability` imports only `Games/Simulate`, `Games/Machines` and Mathlib |
| `Foundations.lean` (facade) | + `TCSlib.Cryptography.Foundations.BitLists` | the facade imports every child | yes: `BitLists` imports only Mathlib |
| `Foundations/BitLists.lean` (new) | `Mathlib.Data.List.OfFn`, `Mathlib.Data.List.GetD`, `Mathlib.Logic.Equiv.Prod` | the L lemmas | Mathlib only; all three are in `roots.txt` |
| 11 consumers | + `TCSlib.Cryptography.Foundations.BitLists` | the L lemmas they use | yes |
| `OracleFromPRF/Lazy.lean` | `BitwiseCPA.Eager` → `Encryption.PublicKey.OracleSecurity` | `Eager` was removed; `OracleSecurity` was its only import, so the import closure is unchanged | yes |
| `BitwiseCPA.lean` | − `BitwiseCPA.Eager` | `Eager` was removed; its content now lives in `OracleSecurity`, which `BitwiseCPA` already imports through `AdaptiveCPA` | yes |

- The 11 consumers are `AdaptiveCPA/{Games,Reduction}`, `BitwiseCPA/Planted`,
  `OracleFromPRF{,/Reduction,/Lazy,/Collision}`, `Pseudorandom/NextBit`, `SecureComputation/Yao`,
  `ZeroKnowledge/CommitmentLemmas` and `ZeroKnowledge/GraphIsomorphism/EfficiencyRep{,GI}`.
- The R6 consumers use `open TCSlib.Cryptography.Games.InteractiveHandler (rU …)`, which adds no
  import.
- **Final order** (`evidence/logs/order-final.txt`, 407 modules). This is `order.txt` with three
  changes:
  - `Games/Probability` moved before `Games/BitCodec`;
  - `Foundations/BitLists` inserted before its first consumer, `Pseudorandom/NextBit`, followed by
    the `Foundations` facade (not in `order.txt`, but edited);
  - `BitwiseCPA/Eager` removed.

## 4. Changed, new and deleted files (base → final, lines)

37 paths: 35 changed, 1 new (`Foundations/BitLists.lean`), 1 deleted (`BitwiseCPA/Eager.lean`). Every
file is below 1000 lines, except `ElGamal.lean`, which is 1835 lines at the base (lint WARN at the
base) and is now 1829.

| File | Base | Final |
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
| `Encryption/PublicKey/OracleSecurity.lean` | 982 | 987 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 274 | 315 |
| `Encryption/PublicKey/OracleSecurity/RecordHandler.lean` | 333 | 333 |
| `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean` | 411 | 289 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 596 | 543 |
| `Encryption/PublicKey/AdaptiveCPA/Games.lean` | 301 | 240 |
| `Encryption/PublicKey/AdaptiveCPA/Reduction.lean` | 274 | 275 |
| `Encryption/PublicKey/BitwiseCPA.lean` | 558 | 549 |
| `Encryption/PublicKey/BitwiseCPA/Eager.lean` (deleted) | 167 | — |
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

Net: 17,979 lines at the base, 17,929 at the final head.

## 5. Census (`evidence/logs/census.txt`, `namemap-check.txt`)

- **Dumps.**
  - `decl-dump-base-ext.log` was taken at the base tree. It has every stored constant of the 35
    candidate modules plus `ZeroKnowledge/GraphIsomorphism/EfficiencyRep{,GI}` and the
    `Foundations` facade.
  - `decl-dump-final.log` was taken at the final head over the same modules, with
    `Foundations/BitLists` added and the deleted `Eager` removed.
  - Each row is `name | module | kind | type hash | attributes (reducibility, simp, instance,
    protected) | axioms`.
  - The checkpoint-time `decl-dump-base.log` (35 modules) agrees with the extended base dump on
    every common row (1896 rows, 0 differ).
- **Comparison** (`tools/cmpdump.py`), restricted to the 37 changed paths:

  | Class | Count | Content |
  |---|---|---|
  | rows (base / final) | 1994 / 1981 | stored constants of the 37 changed paths (the 35 modified modules, `BitLists`, `Eager`) |
  | **removed** | 102 | 70 named: exactly the listed copies (§2) and the further copies folded in (`GI.getD_eq_headD_drop`, ElGamal's `dlc_ofFn_padFin`, `cca2OfFn_cast`, `cca2CtLen`, the private readers, `impl_of_ret`, `replicate_one`, `bitwise_runAtL`), and Eager's `padded_enc_runAt/_coins`. 32 are their auxiliaries (`match_`, `_proof_`, `eq_1`). |
  | **added** | 89 | 68 named: the promoted lemmas, the published readers (`indCodec_eq_bitCodec` ×2, `hybridPre_eq`, `expect_simulate_indImpl_cpa`, `rU … rCnt` with `_input` and `polyTimeComputable_`, `impl_of_ret`) and the new A5 lemma `FunFamily.ofFn_blocks`. 21 are auxiliaries. All 89 are `regular`, not `simp`, not instances, not protected. |
  | **moved** (same name, type, attributes) | 2 | `ofFn_padFin_of_length` (HardCoreGLColl → Adversary, A1), and the auto-generated `ProbComp.sample.congr_simp`. The second is now generated in `Games/Probability`, where the promoted sampling lemmas first need it, not in `PrivateKey/OracleSecurity`. |
  | **changed** (type hash) | 25 | none in statement: see the next row |
  | changed modulo the name map | **0** | `typecmp.txt`: each of the 25 base types, with every moved constant renamed by `namemap.txt`, hashes to the final type. They change only because they mention a moved declaration: `castImpl` (`castImpl_adaptiveIndImpl`, `castImpl_indImpl_challenge`, private `comp_acAbs`), `xorPerm` (`ctOf_xorPerm`), or the R6 readers (the private handler definitions' `eq_1` lemmas, `fields_input`, `polyTimeComputable_acRun` auxiliaries). Attributes and visibility: 0 changed. |
  | axioms changed | 1 | `BitwiseSim.plantOut_recorded`: `[Classical.choice, Quot.sound, propext]` → `[Quot.sound, propext]`, a subset. Its `rw` used the induction-and-`simp` proof of the deleted `BitwiseSim.headD_drop`, and now uses the `rw` proof of the promoted `headD_drop`. |


- **Name map** (`tools/namemap_check.py` over `namemap.txt`). For every old name: whether it is gone,
  whether the new name exists, and whether the types are identical (type hash).

  - **69 rows** (`evidence/namemap.txt`, `logs/namemap-check.txt`): every old name is gone except the
    moved `ofFn_padFin_of_length`, and every new name exists. The 3 that point outside the dumps are
    core `List.replicate_one` (×2) and `BitPublicKeyScheme.bitwise_enc_runAtL` (`EnsembleSecurity`).
  - **Same statement modulo renaming:** 54 pairs (`typecmp.txt`); binder names do not count. 2 rows
    are new declarations.
  - **Different statement, all intended:** 15 pairs.
    - P3: `ProbComp.expect_sample_update` binds `β` before `ι`, because `β` is the section
      variable. `expect_sample_coord` generalizes `Fin κ` to any finite `ι`.
    - L1: `headD_drop` is generalized from `Bool` (and from `d = false` for BitwiseSim's). It replaces
      NextBit's `ofFn` form and the reversed `GI.getD_eq_headD_drop`.
    - L2: Yao's `flatten_ofFn_one` differs only in the proof term `⟨0, by omega⟩` inside the
      statement.
    - R3: the cast form, see §2.3.
    - R6: the generic `impl_of_ret`, and core's `List.replicate_one`.
    - O1: `bitwise_runAtL` → `bitwise_enc_runAtL`, after `bitwise_enc`.
    - O2: `cca2CtLen` → `prf_ctLen_eval` + `ctP_eval`.

## 6. Axioms (`decl-dump-final.log`)

- **Every stored constant** of the 36 final files and the 2 further candidate modules: 1981 rows
  for the changed paths, 2011 in the dump.
  - Each uses a subset of `propext`, `Classical.choice`, `Quot.sound`: 1153 use all three, 293
    `[Quot.sound, propext]`, 185 `[propext]`, 10 `[Classical.choice]`, 6 `[Quot.sound]`, 330 none.
  - The only exceptions are the 4 Yao constants that use `sorryAx`: the 3 admitted statements of
    `base-sorries.txt` (`yaoSeed_good_whp`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`), and
    `yaoHybrid_hbcSecure`, which uses them. These are the same 4 as in the extended base dump.
- **The nine campaign endpoints** each print `[Classical.choice, Quot.sound, propext]`, as at the
  base: `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`,
  `FixedLengthPKScheme.INDSecure.adaptive_cpa`, `BitPublicKeyScheme.SingleBitSecure.{bitwise_padded_cpa,
  exists_adaptive_cpa, padded_cpa}` and `Implications.PublicKey.exists_adaptiveCPA_of_{rsa,factoring}`.
- **Changed axioms:** only `plantOut_recorded`, to a subset (§5).

## 7. Rule 10

### 7.1 Whole-file closure seals

The seals follow the Gate 17 audit's method: the whole import closure, abbreviations excluded, and
the instance-unfolding mask (`tools/seal_gen.py`, `tools/seal_run.py`).
- Each sealed copy is a verbatim copy of the file with its own imports and `import Lean`.
- Right after the imports, a `run_cmd` makes **every TCSlib definition of the import closure**
  `irreducible` with `attribute [local irreducible]` (between 17 and 1573 definitions
  per file; 0 for `BitLists`, whose closure is Mathlib only), and removes them from the
  instance-unfolding set.
- Two kinds of definition are excluded:
  - abbreviations (`abbrev` hints: structure projections, `casesOn`, `noConfusion`, notation such
    as `bitSpec`, `indSpec`);
  - in the second variant, `PolyExpr.eval`.
- The copy is a new module, so the file's own definitions stay transparent. The whole file must
  elaborate while reading every other TCSlib definition only through its published lemmas.

**Final head** (`seal-final.jsonl`, `seal-final.out`; `PolyExpr.eval` sealed), 36 files:
- **26 of 36 pass:**
  - all five Games files, the `Foundations` facade and `BitLists`, and `Adversary`;
  - every `OracleFromPRF` file and `PrivateKey/OracleSecurity`;
  - `AdaptiveCPA/{Games,Hybrid,Reduction}`, `BitwiseCPA` with `Planted` and `QueryHandler`;
  - `ChallengeSim`, `RecordHandler`, `ElGamal` and `NextBit`.
- **10 fail**, all at declarations that this job did not write:

| File | Final, eval sealed | Base, eval sealed | Final, eval open | Base, eval open |
|---|---|---|---|---|
| `Asymptotic/EnsemblesLemmas.lean` | 11 errors in 10 decls | 11 errors in 10 decls | 11 errors in 10 decls | 11 errors in 10 decls |
| `Asymptotic/HardCoreGLColl.lean` | 3 errors in 2 decls | 3 errors in 2 decls | pass | pass |
| `Encryption/PrivateKey/OracleFromPRF.lean` | **pass** | 2 errors in 2 decls (`cca2Encrypt`, `cca2Gen`) | — | pass |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 3 errors in 3 decls (`acTapes`, `acTapes_apply`, `acHandler_finish`) | the same | pass | pass |
| `Encryption/PublicKey/HybridMachine.lean` | 1 error (`blockEncFun_flatten`) | the same | 1 error | 1 error |
| `Encryption/PublicKey/OracleSecurity.lean` | 4 errors in 2 decls (`PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`) | the same | pass | pass |
| `Pseudorandom/Functions/Asymptotic/GGM/Run.lean` | 10 errors in 8 decls | the same | 9 errors in 7 decls | the same |
| `SecureComputation/Yao.lean` | 15 errors in 8 decls | the same | pass | pass |
| `ZeroKnowledge/CommitmentLemmas.lean` | 8 errors in 8 decls | the same | 6 errors in 6 decls | the same |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | 6 errors in 6 decls | the same | 4 errors in 4 decls | the same |
| `ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean` | 3 errors in 2 decls | the same | 3 errors in 2 decls | the same |

**Base controls** (`seal-base.jsonl`, `seal-base.out`). The base copies of the 35 files that exist at
the base, sealed the same way over the base tree:
- **24 of 35 pass.**
- **11 fail.** These are the 10 above, at the same declarations with the same error counts, plus
  `OracleFromPRF.lean` at `cca2Encrypt` and `cca2Gen`. That is the Gate 17 finding: they read
  `PolyExpr.eval .var` definitionally.

**Comparison** (`tools/cmp_scans.py seals`, `logs/seal-compare.txt`):
- **New failing declarations: 0**, with `PolyExpr.eval` sealed (`seal-compare.txt`) and with it open
  (`seal-compare-evalopen.txt`). In every failing file, the failing declarations are identical at
  the base and at the final head.
- **Two failures removed.** O2 re-derived `cca2Encrypt` and `cca2Gen` from PRFStep's
  `ofFn_prf_encryptAt`/`ofFn_prfNonceEq` and `prf_gen_runAt`/`ofFn_prfKeyEq`, which read the nonce
  and key widths through `finCongr (eval_var n)`. `OracleFromPRF.lean` now passes the full seal.
- **The new code passes every seal.** That covers:
  - all promoted lemmas and published readers (`Adversary`, `BitCodec`, `Probability`, `Simulate`,
    `Hopping`, `Efficiency`, `BitLists`, `ChallengeSim`, both `OracleSecurity` files,
    `HybridMachine`'s `hybridPre_eq`, `EnsemblesLemmas`' `ofFn_padFin_eq_padL`);
  - every re-pointed use.

  None of them is among the failing declarations.
- **The legacy failures that remain with `PolyExpr.eval` open** read other bodies. These are
  pre-existing, in code this job only re-points:
  - `EnsemblesLemmas` reads `uprob`/`acceptProb`;
  - `HybridMachine.blockEncFun_flatten` reads `NUPPT.layout`;
  - `GGM/Run` reads `simulate`/`evalLazy`;
  - `CommitmentLemmas` reads `distAdv` and `EnsembleLemmas.swapAux`;
  - `EfficiencyRep` reads `pairSndD []`;
  - `EfficiencyRepGI` reads `encGraph`/`permGraph` by `Iff.rfl`.

  The rest of each failure list is `PolyExpr.eval` readings.

**`PolyExpr.eval` open** (`seal-final-evalopen.jsonl`, `seal-base-evalopen.jsonl`). The failing files
re-sealed with `PolyExpr.eval` left transparent (the Gate 17 remark):
- **10 final files re-sealed**, and the 11 failing base files re-sealed.
- **4 final files then pass**: HardCoreGLColl, AdaptiveCPA/Handler, OracleSecurity and Yao. At the
  base, OracleFromPRF passes too. Their only readings are of `PolyExpr.eval`, for example `acTapes`'s
  `(cap.mul coins).eval n` read as `cap.eval n * coins.eval n`, and Yao's `(inB.mul var).eval n`.
- **6 still fail**, at the same declarations at the base: EnsemblesLemmas, HybridMachine, GGM/Run,
  CommitmentLemmas, EfficiencyRep and EfficiencyRepGI (the readings listed above).

### 7.2 Paired controls (`seal/SealControls*.lean`, `seal-controls-*.log`)

Ten examples read one TCSlib definition each through its body (`rfl`):
- `PolyExpr.eval`, `padFin`, `zeroBits`, `FunFamily.blocks`, `EnsembleLemmas.padL`, `xorPerm`,
  `InteractiveHandler.rU`;
- the public and private `indCodec`, and `splitHalf`.

These cover the definitions that the promoted lemmas and readers are about.

| Run | Result |
|---|---|
| Unsealed (`seal-controls-unsealed.log`) | **pass**, status 0 |
| Sealed, `PolyExpr.eval` included (`seal-controls-sealed.log`) | **10/10 fail**, one error per example, at lines 57, 58, 59, 61, 62, 63, 64, 66, 68, 70 |
| Sealed, `PolyExpr.eval` open (`seal-controls-sealed-evalopen.log`) | **9/10 fail**; only the `PolyExpr.eval` example (line 57) passes |

The seal is therefore active, and the `PolyExpr.eval` exclusion does exactly what it says.

### 7.3 Explicit-unfold scan (`tools/rwids.py`, `rwids_run.sh`; `rwids-final.tsv`, `rwids-base.tsv`)

`irreducible` does not block `rw [f]`, `simp [f]`, `unfold f` or `delta f`, so a separate scan does
this:
- It collects every identifier passed to `rw`, `rwa`, `nth_rw`, `rewrite`, `erw`, `simp`,
  `simp only`, `simp_all`, `simpa`, `dsimp`, `simp_rw`, `field_simp`, `norm_num`, `unfold` and
  `delta` in **each whole changed file**.
- It resolves each one in the file's namespaces with the file's `open`s.
- It classifies each one as a theorem, a definition of the file itself, a core or Mathlib
  definition, a **foreign TCSlib definition**, or unresolved (a local hypothesis or one of the
  file's private declarations).

| Identifiers | Final (36 files) | Base (35 files) |
|---|---|---|
| theorems | 1973 | 1957 |
| the file's own definitions | 109 | 101 |
| core or Mathlib definitions | 5 | 5 |
| unresolved (local hypotheses, the file's private declarations) | 551 | 584 |
| **foreign TCSlib definitions** | **0** | **0** |

- **Core and Mathlib.** The 5 entries are the same at both: the `reduceIte` simproc in Collision
  and BitwiseCPA, and `Ne`, `Prod.map`, `id` in ElGamal.
- **Own definitions.** The only new ones are in `Games/Efficiency.lean`: its own new readers
  `rU … rCnt`, unfolded in their `_input` lemmas.
- **Foreign.** No foreign TCSlib definition is passed explicitly, at the base or at the final head
  (`rwids-compare.txt`: new foreign explicit unfolds 0).
- **What R6 removed.** At the base, the handlers' `fields_input` and `acHandler_impl_dec` unfolded
  their private readers. Those readers are now published, and the handlers use their `_input`
  lemmas.

## 8. Sweep and admissions

- **Fresh sweep** (`sweep-final.log`, order `order-final.txt`, at `6917e5716`).
  - The olean tree was removed first.
  - **407/407 modules, status 0, 0 errors**, 38.6 min of checking.
- **Admissions** (`sorry-census-final.txt`): **48 sorry warnings in 26 modules**, identical to
  `base-sorries.txt` (`cmpcensus.sh`: CENSUS IDENTICAL).
- **Other warnings.** The non-sorry warnings are identical to the bootstrap's: 129 = 129, none new,
  none gone.
- **Base tree** (`base-tree.log`). 406/406, status 0, with the same 48 sorry warnings in the same 26
  modules. In `sorry-census-base-tree.txt`, Yao's three are shown by line, because `census.py` looks
  names up in the final sources.

## 9. Lint (`lint-final.log`)

- **Command:** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`.
- **Result:** 188 FAIL, 103 WARN over 286 files. The base gives 190 FAIL, 103 WARN over 286 files.
- **No new FAIL** (`lint-diff.txt`).
  - The two facade FAILs `Encryption.lean`/`PublicKey.lean` "does not import child module
    `BitwiseCPA.Eager`" disappeared with `Eager`.
  - The only other difference is the ElGamal size WARN, now 1829 lines instead of 1835.

## 10. Grep receipts (`evidence/grep-receipts.txt`)

- **The searches.** One search per item over `TCSlib` and `audits` at the base, with every hit:
  - 33 searches, 1120 lines;
  - groups P1–P4, S1–S3, H1, A1–A6, R1–R7, L, O1 and O2.
- **Further copies found by these searches.**
  - Folded: `GI.getD_eq_headD_drop` into L1, and ElGamal's `dlc_ofFn_padFin` into A1.
  - Recorded: everything else, in §11.
- `audits/` uses none of the moved names.

## 11. Further duplication found (recorded, not folded)

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
- **`AdaptiveCPA`'s `fields_input` and `PRFGame`'s `fields_input`** (both private) have the same
  structure: the published readers on the handler's own state encoding. They differ in the state
  layout, so they are not copies.

## 12. Checkpoints

- **Checkpoint 1** (`rebuild-cp1.log`). 245/245 modules from `Games/Simulate`, status 0. 17 modules
  and 29 sorries, as at the base. Non-sorry warnings 61 = 61.
- **Checkpoint 2** (`rebuild-cp2.log`). 375/375 modules from `Asymptotic/Adversary`, status 0.
  19 modules and 31 sorries, as at the base. Non-sorry warnings 113 = 113.
- **Checkpoint 3** (`rebuild-cp3.log`). 252/252 modules from `Encryption/PublicKey/HybridMachine`,
  status 0. 17 modules and 29 sorries, as at the base. Non-sorry warnings 62 = 62.
- **After checkpoint 3** (`6917e5716`). The fresh sweep (§8) covers it.

## 13. Evidence index

- `evidence/logs/`:
  - setup: `preflight`, `source-sha256`, `package-sha256`, `mathlib-roots`, `cache-*`,
    `packages-check`;
  - bootstrap: `bootstrap`, `sorry-census-bootstrap`;
  - rebuilds and orders: `rebuild-cp{1,2,3}` with lists, `order-cp{1,2,3}`, `order-final`;
  - the base tree: `base-tree`;
  - the fresh sweep: `sweep-final`, `sorry-census-final.txt`;
  - census: `decl-dump-base.log`, `decl-dump-base-ext.log`, `decl-dump-final.log`, `census.txt`,
    `namemap-check.txt`;
  - seals: `seal-{final,base}{,-evalopen}.jsonl/.out`, `seal-compare.txt`, `seal-controls-*.log`;
  - unfold scans: `rwids-{final,base}.{log,tsv}`, `rwids-compare.txt`;
  - lint: `lint-{base,cp1,cp2,cp3,final}.log`;
  - the final head: `final-head.txt`.
- `evidence/seal/`: the sealed copies, the controls, the dump sources and the scan modules.
- `evidence/tools/`: every script used.
- `evidence/grep-receipts.txt`.
- `patches/`: `git format-patch b96ab3ccc..6917e5716`, 4 patches.
- `src/`: the 36 final files.

**Final payload delivered — ready for maintainer review and the gate**
