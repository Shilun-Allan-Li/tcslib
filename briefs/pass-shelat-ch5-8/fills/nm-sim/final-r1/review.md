# nm-sim · maintainer delivery review (r1)

## Verdict: ACCEPT WITH LANDING EDITS

There is one landing edit, LE-W, which fixes line widths. Both targets are proved without admissions. Rule 10 holds under every check I ran. Findings 2–4 are undisclosed duplicates. They do not affect correctness, but under policy §1 each one needs the user to accept it as ledger debt (I propose a new ledger row, DL-37) or to send it back to the worker.

- **Delivery:** exchange commit `da56632fb066b657d3054865cc1b4f7535018951`. Checkpoints `fd99cad2bfc12f710daf1fc122d0501e20f51f21` and `8a27d9698d2c4d74cc486ca16a08014ebd22b659`.
- **Patches:** 3, on the issue base `262d6e9ae526c82eb68fe5a6169156bd1504e6d8`.
- **Landing branch:** local `land/pass-shelat-nm-sim`, head `61ebc3962708c4fe6ac6f1f16381735b87d0611a`, on campaign `691f30f81af5c1c28d3d2c9abaadb88dc42bd4b0`. Not pushed.

## Findings

1. **low — line widths.** 67 lines in all 11 files are longer than 100 characters, the longest 134 (`Simulator.lean:546`). The other recent NonMalleability files have none.
   - **Landing edit LE-W:** `landing-edits/landing-edits.diff`. It makes 68 re-wrap replacements and nothing else, and `apply_width_edits.py` asserts that the token sequence of every replacement is unchanged.
   - After LE-W, 0 lines exceed 100 characters. Every changed module and the 3 downstream facades (14 modules) compile. The decls2 diff is empty, the axioms of all 574 constants are identical, all 22 seals (A and B) pass, and the lint result is unchanged.
2. **medium-low — `chunkAt` duplicates published lemmas in its import closure (not disclosed).**
   - `NMSim.chunkAt k i w` (`Hybrid.lean:364`) is `TCSlib.Cryptography.coinBlock B i r` (`Asymptotic/Adversary.lean:85`): same body, same argument order. `Adversary.lean` is in Hybrid's import closure.
   - `chunkAt_eq` duplicates `coinBlock_eq`, and `length_chunkAt` duplicates `length_coinBlock` (same hypothesis).
   - `ofFn_block` generalizes `OneWayLemmas.ofFn_block_eq_take_drop` (in the closure; the case `sl = 0`), `NMCCA2.ofFn_nthCt`, and the consolidation's `EnsembleLemmas.take_drop_ofFn_blocks`.
   - `chunkAt_flatten_append` and `map_chunkAt_flatten` mirror Lamport's `coinBlock_flatten` and `coinBlock_flatten_ofFn` (outside the closure).
   - **Disposition:** ledger debt. Fold `chunkAt` onto `coinBlock` (58 uses) and put the block lemmas beside `coinBlock` at the next consolidation window. The worker's request to promote the `Hybrid` list facts is redirected there.
3. **low — private copy of a public lemma (not disclosed).** `Challenge.lean:234` `private padFin_replicate_false` has the statement of the public `PRFGame.padFin_replicate_false` (`PrivateKey/OracleFromPRF/Transfer.lean:48`, outside the closure). The consolidation moves that lemma to `Games.padFin_replicate_false`. It is also one rewrite from the in-closure `padFin_ofFn_zeroBits` and `ofFn_zeroBits`.
   - **Disposition:** delete it and use `Games.padFin_replicate_false` when the consolidation lands (re-point list below).
4. **low — generic lemmas next to existing ones, and one DL-34 item not disclosed as an overlap.**
   - `expect_eq_until_bad` repeats the induction of `Games.prob_eq_until_bad` (`Hopping.lean:205`). Its docstring says it generalizes that lemma.
   - `NMSim.expect_simulate_eager` has the same name as `BitwiseSim.expect_simulate_eager`, which the consolidation renames `ChallengeSim.expect_simulate_eager`. The nm-sim lemma is the general one-shot form; the existing one is CPA-shaped.
   - `expect_congr_of_allOutputs` is a two-line corollary of `ProbComp.expect_mono_of_allOutputs`.
   - `buildComp_budget_eq` is a sibling of `Games.EffFill.buildComp_of_replaysFrom` (`Efficiency/Replay.lean:70`).
   - `chunkMap` is a third instance of the iterate-and-emit pattern, after `relabelN` and `logEmit` (DL-36).
   - `Rounds.impl_of_ret` re-derives the private DL-34 `impl_of_ret` of `AdaptiveCPA/Handler.lean:415` and `PRFGame`. The worker listed it only as a promotion, not as a "DL-30–36 overlap".
   - `Simulator.finSt` is the same function as `Rounds.rdState`, which is the DL-34 reader `rS`. That is a second copy inside the delivery itself.
   - **Disposition:** ledger; destinations are in the promotion table below.
5. **nit — docstrings.**
   - `chalRun_eq`, `simFin_eq` and `nmFin_eq` are label-only ("the round described above").
   - 10 proofs of more than 20 lines have no `**Proof sketch**` (`statements/sketch-audit.tsv`): `chalHandler_impl_none` (49 lines), `polyTimeComputable_recView` (54), `polyTimeComputable_nmFin`, `nmFin_finInput`, `impl_of_query`, `polyTimeComputable_chunkMap`, `simFin_finInput`, and the private `expect_runB_good`, `realAcc_half`, `polyTimeComputable_tailFun`.
   - The module docstring of `SimINDGap` has no `## Main definitions`, although the file defines `simHandler`.
   - **Disposition:** fix later; no landing edit.
6. **nit — `ofFn_eq_map_range` (disclosed).** This is the third copy of the lemma; the other two are in the ZK files. `length_flatten_map_const` is `List.length_flatten` plus a constant sum.
7. **info — owned-file imports.** The owned file imports all 10 helpers, although `SimINDGap` and `IndSim` reach the rest. The `## Contents` section is present and correct.
8. **info — proof review: no issues.** Details in the next section.
9. **info — consolidation re-points.** If the consolidation lands first, 12 identifiers need re-pointing (listed in the evidence summary).
10. **info — downstream.** The root `TCSlib` reaches the changed modules through the facades, but cannot be built on this host: 33 Mathlib modules the full library imports are not in the shared cache. The three facades in between were built. `audits/pass-shelat/Checks` does not reach the changed modules.

## Proof review

**SIM ⇒ IND (`nmSecure_of_simNMSecure`).**
- **Quantifiers.** The quantifier order matches the definitions: `Sim` comes from `h M A' Q ℓ 0`, then `D' = tailDist D` and `D'' = halfDist` are applied to that one `Sim`.
- **Distinguishers are allowed.** `SimNMSecure` quantifies over every NUPPT distinguisher. So `D' = NUPPT.ofPolyTime … D.coins D.adv D.advice`, which uses D's advice and coins, is a legitimate distinguisher.
- **Constructions are NUPPT by construction.** The sampler `halfSamp` (`ofPolyTimeUniform`, one coin, `histLen = 0`, `hist_poly` constant), `A'` (T2) and both distinguishers carry their polynomial-time proofs.
- **Real gap.** `castImpl_indImpl_abs` holds for every `atk`: Dec availability, refusal of the challenge and decryption agree with `indImpl`, so CCA1 and CCA2 are covered. The flag-free tails equal `nmOutput` (`nmOutput_eq_entryTails`; a COPY entry has the all-zero payload, which is ⊥).
  - The bad event is `m₀ ≠ m₁`. It is sticky, and the empty state is good (no challenge means `a = 0`).
  - Equal-until-bad then gives `2·Pr[D'] − Pr[D''] = Pr[D(NM_1)] − Pr[D(NM_0)]`.
- **Ideal gap.** With `hl = 0` the oracle ignores `β` (`histImpl_coins`), so `2·Pr[D'] = Pr[D'']`.
- **Bound.** `abs_le_of_gap` gives `2ε' + ε''`.

**IND ⇒ SIM under CPA (`simNMSecure_of_nmSecure_cpa`).** Equalities hold for every `n`: `idealAcc = hybAcc true` and `realAcc = hybAcc false` for all `n`, and `accept NM_b = hybAcc b` when `msgLen(n) > 0`. When `msgLen(n) = 0`, `hybAcc true = hybAcc false` gives advantage 0. No step loses anything.
- **Budget reduction.** `buildComp_budget_eq` / `toCompOn_budget_eq` is general and sound: induction on `j`, any `K ≥ j`, and the timeout case only at `K = 0`.
- **Budget for the simulator.** `finCall = 1` makes T2's budget at least 1 even at `q = 0`. The run asks at most one query (`simulate_costBoundedBy_once`), and the finalization asks none.
- **Readback.** At most one ciphertext of each pair is the challenge (`guessBit_encPair`, by correctness). `ctLen_pos` needs `msgLen > 0`. Using one encryption tape for every pair is harmless, because only the decryptions are read.
- **Edge cases checked:** budget 0, `r = 0`, `sl = 0`, no challenge (the state stays `none` and the parameter is `0`), repeated challenges (`rImpl_some` / `chalHandler_impl_some`), A outputting the challenge (COPY), malformed ciphertexts (decrypted as given), codec timeouts (inside the transported whole-run equalities), the `ctLen = 0` branch, and `m₀ = m₁`.

## Promotion requests (worker's REPORT)

| Request | Decision | Destination |
|---|---|---|
| `buildComp_budget_eq`, `toCompOn_budget_eq`, `buildComp_of_ret` | accept | `Games/Machines.lean` (`buildComp_of_ret` beside `buildComp_*_of_ret`) or `Efficiency/Replay.lean` beside `buildComp_of_replaysFrom` |
| `impl_of_ret` | redirect | the consolidation's `InteractiveHandler.impl_of_ret`; keep the list form as a corollary there |
| `impl_of_query`, `finish_of_ret` | accept | beside `impl_of_ret` in `Games/Efficiency.lean` |
| `padFin_append_split` | accept | beside `padFin` |
| `chunkStep`, `chunkEmit`, `chunkMap`, `polyTimeComputable_chunkMap`, `chunkMap_flatten` | redirect | one generic iterate-emit definition beside `Complexity.polyTimeComputable_iterateEmit`, folding `relabelN` and `logEmit` (DL-36) |
| `seedEquiv`, `seedEquivPoly` | accept | `Asymptotic/EnsemblesLemmas.lean` beside `coinsEquiv` |
| `length_ofFn_coins` | reject | a one-line composite; keep it local |
| `expect_toCompOn_outLen` | accept | `Games/Efficiency.lean` |
| `expect_congr_of_allOutputs` | accept | `Games/Hopping.lean` beside `expect_mono_of_allOutputs` |
| `bind_congr_of_allOutputs` | accept | `Games/OracleComp.lean` beside `AllOutputs.bind` |
| `expect_expect_sample` | accept | `Games/Probability.lean` |
| `expect_simulate_eager` | accept | `Games/Hopping.lean`; later derive `ChallengeSim.expect_simulate_eager` from it |
| `expect_eq_until_bad` | accept | beside `prob_eq_until_bad`, re-deriving that lemma's first conjunct from it |
| `costBoundedBy_bind_of_allOutputs` | accept | `Games/OracleComp.lean` beside `CostBoundedBy.bind` |
| `simulate_costBoundedBy_once` | accept | `Games/Simulate` or `Games/Hopping` |
| private `lin_*` | reject | keep private |
| `chunkAt`, `length_chunkAt` | redirect | fold onto `coinBlock` and `length_coinBlock` (finding 2) |
| other `Hybrid` block lemmas | redirect | beside `coinBlock`; `ofFn_block` folds `ofFn_block_eq_take_drop`, `ofFn_nthCt` and `take_drop_ofFn_blocks` |
| `ofFn_natAdd_eq_drop`, `decide_map_ofFn`, `length_flatten_map_*`, `ofFn_eq_map_range` | accept | `Foundations/BitLists.lean` (new in the consolidation); merge with the two ZK copies of `ofFn_eq_map_range` |
| `ctLen_pos` | accept | `PublicKey/OracleSecurity.lean` after its split |
| `polyTimeComputable_guessBit` | accept | `Indistinguishability/Encrypt.lean`, replacing the content of the private `polyTimeComputable_guessFun` |

The four disclosed DL-30–36 overlaps are confirmed:
- `flatMap_range_drop` (private, general form);
- the round readers, which equal the DL-34 `rU`…`rL`;
- `ofFn_padFin_eq_padL`, which the consolidation publishes as `EnsembleLemmas.ofFn_padFin_eq_padL`;
- `polyTimeComputable_guessBit`.

## Evidence summary

**Integrity**
- The payload's `SHA256SUMS` checks 587/587 OK and covers every file.
- The three delivery commits touch only `inbox/fills/nm-sim`.
- `git am` of the 3 patches at the issue base exits 0. The resulting tree is `a39affb95d169d2693fa8a8cb2fe7d74a67c1965`, the tree the worker reported (head `110f4498c04d92085b5ac31dd694054d8f50aab1`).
- Exactly 11 files change, all byte-identical to `src/`.

**Landing**
- Parent `691f30f81af5c1c28d3d2c9abaadb88dc42bd4b0`. Since the issue base: 6 commits, all records (no `.lean`, lakefile, manifest or toolchain changes).
- `git am` applies cleanly, with authorship kept.
- Head `61ebc3962708c4fe6ac6f1f16381735b87d0611a`, tree `4669e14d2160173522b043137f8ff0fba0fcd78f`.
- The worktree has only the 3 delivered commits; no edits are committed. Nothing was pushed.

**Pins:** Lean 4.25.0 (`cdd38ac5`), Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; 11 packages OK, 4 absent; 97/97 roots present.

**Build**
- The order is 262 modules: the issued 252 plus the 10 helpers, placed before the owned file.
- On the fresh tree `nmsim-oleans`: 262/262 pass, 0 errors.
- Sorry census: 26 at the base, 24 at the head. Removed: exactly the two targets. Added: none.

**Statements**
- decls2 against the base: 269 ADDED, 0 CHANGED, 0 REMOVED.
- touched.py: in the owned file only the two targets' bodies and docstrings changed, plus 10 added declarations (3 private).

**Axioms**
- Both targets and `simNMSecure_cpa_iff_nmSecure_cpa`: [propext, Classical.choice, Quot.sound].
- All 574 stored constants of the 11 files:

| Axioms | Constants |
|---|---|
| propext, Classical.choice, Quot.sound | 466 |
| Quot.sound, propext | 41 |
| propext | 25 |
| Quot.sound | 2 |
| none | 40 |

- 0 constants use any other axiom, and 0 use `sorryAx`.

**Rule 10 seals.** Whole-file seals over the full TCSlib import closures, A with `PolyExpr.eval` exempt and B with it sealed. All 22 install and verify, then pass.

| File | Requests (A) | Stored constants |
|---|---|---|
| Generic | 2000 | 31 |
| Hybrid | 2214 | 81 |
| SimIND | 2237 | 70 |
| SimINDGap | 2252 | 10 |
| Rounds | 2003 | 49 |
| Challenge | 2247 | 61 |
| Simulator | 2256 | 61 |
| Reduction | 2281 | 74 |
| Recover | 2298 | 29 |
| IndSim | 2303 | 7 |
| owned file | 2304 | 101 |

B requests are one higher in every row.

- **Base control:** the base owned file passes A (2211 requests) and B (2212).
- **Paired controls:** 22 probe pairs per variant, ALL_OK in both. In A, 285/285 sealed negatives fail exactly once; in B, 296/296. Every positive passes, and every unsealed control passes (570 in A, 592 in B).
- **Explicit-unfold scan:** 1,850 items.

| Class | Items |
|---|---|
| Foreign TCSlib definitions | 0 |
| Own-file definitions | 29 |
| Theorems | 1,496 |
| Hypotheses or dot-notation theorems | 320 |
| Simprocs | 5 |

**Lint and size**
- Lint: 0 FAIL and 6 WARN, identical to the base.
- Sizes: owned file 792 lines (796 after LE-W); helpers 281–895 (288–899 after LE-W).

**LE-W**
- Diff SHA-256 `06dbeb07afb5eff90c9c71be7cb07b79406adde0438c6e08d9fd950680b344ae`; `git apply --check` passes at the landing head.
- Probe commit `fda8f142c5d105341e337db71824b46910d106ab` (dangling, on no branch).
- Edit tree: 14 modules pass, 22/22 seals pass, axioms and statements unchanged.

**Consolidation re-points.** If the consolidation lands first, these identifiers change:
- `AdaptiveCPA.castImpl`, `castImpl_eq`, `expect_simulate_castImpl_toCompOn`, `padFin_ofFn_zeroBits`, `simulate_eq_of_abs` → `Games.*`;
- `AdaptiveCPA.ofFn_cast` → `TCSlib.Cryptography.ofFn_cast`;
- `AdaptiveCPA.ofFn_splitHalf_fst` / `_snd` → `FixedLengthScheme.*`;
- `ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sub` → `Games.ProbComp.*`;
- `GGMRed.ofFn_padFin_of_length` → `TCSlib.Cryptography.ofFn_padFin_of_length` (26 sites).

The selective `open AdaptiveCPA (…)` lines at `Simulation.lean`, `SimIND.lean:49–50` and `Simulator.lean:48` must also change. Every site is listed in `consolidation/repoint-sites.txt`.

These nm-sim helpers become foldable onto consolidated names:
- `rdU`…`rdLog` and `finSt` → `InteractiveHandler.rU`…`rL`;
- `ofFn_padFin_eq_padL` → `EnsembleLemmas.ofFn_padFin_eq_padL`;
- the private `padFin_replicate_false` → `Games.padFin_replicate_false`;
- `impl_of_ret` → `InteractiveHandler.impl_of_ret`;
- `ofFn_block` ↔ `take_drop_ofFn_blocks`;
- `NMSim.expect_simulate_eager` ↔ `ChallengeSim.expect_simulate_eager`, where the consolidated lemma becomes the corollary.

**Evidence location**
- Folder: `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/nmsim-review/`, with `PROVENANCE.txt` and `SHA256SUMS` (685 files).
- Zip: `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/nmsim-review.zip`.
