## ===== briefs/pass-shelat-ch5-8/gates/19-nm-sim/pack.md =====

# Gate 19 · Simulation-based and indistinguishability-based non-malleability (Theorem 174.8)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #297](https://github.com/Shilun-Allan-Li/tcslib/pull/297) at
  `5da558b4d97aca00efd6dc396a1b0f3bffff268b` (branch `land/pass-shelat-nm-sim`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base `691f30f81af5c1c28d3d2c9abaadb88dc42bd4b0`. The fill was issued on
  `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` (the merge of #294). Every commit between the two, and every later base
  commit, touches records only.
- **Commits:** the worker's 3 commits (Claude fill `nm-sim`), then one maintainer commit of landing edits.
- **Scope:** this is a proof audit. Both statements passed Gate 06 (#232) and are unchanged.

## The targets

They live in `PublicKey/NonMalleability/Simulation.lean`, namespace
`TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.

```lean
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa
```

**Source.** [PS10, Theorem 174.8]: R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010.
The statement follows [PSV07]: SIM-NME′ at one message.

**Definitions.**
- `SimNMSecure` is Definition 173.7 as SIM-NME′. For every sampler `M`, adversary `A` and polynomials `q`, `r`,
  `sl`, there is a simulator `Sim` such that every distinguisher `D` has negligible advantage between `snmReal` and
  `snmIdeal`. The simulator runs through `simCodec` at query budget 1.
- `NMSecure` is Definition 172.6, proved equivalent to IND-CCA2 at Gate 18.

With both directions, `simNMSecure_cpa_iff_nmSecure_cpa` has no admission left, and neither does the
non-malleability chapter.

## The proof (check each step independently)

The 10 helper modules are under `NonMalleability/Simulation/`, namespace `…Composability.NMSim`.

The owned file's section *The experiments on T2's lengths* first reads both experiments as strings:
- `castImpl_snmImpl`;
- `snmView_realView`, `snmView_idealView`;
- `accept_snmReal_eq`, `accept_snmIdeal_eq`: `accept snmReal = NMSim.realAcc`, `accept snmIdeal = NMSim.idealAcc`.

### 1. SIM ⇒ IND, every attack (`nmSecure_of_simNMSecure`; bound `|adv_NM| ≤ 2·adv(D') + adv(D'')`)

**The objects.**
- **Sampler `halfSamp`.** The parameter is `⟨m₀, m₁⟩`. It outputs `m_β` for its one coin `β`, with `histLen = 0`.
- **SIM adversary.** It is T2's machine of `simHandler = copyHandler`, built on `NMCCA2.fwdHandler` (seed 0,
  `finCall = 0`). It forwards `Dec`, so it covers CCA1 and CCA2.
- **The simulator.** `Sim` comes from `h M A' (q·perCall + finCall) ℓ 0`.
- **D' = `tailDist`.** It uses `D`'s coins and advice. It outputs 0 if `m₀ = m₁`, and otherwise
  `[D(tails) = 1] == [m = m₁]`. The tails drop the `COPY` flag, so a copy reads as `nmDecrypt`'s ⊥
  (`nmOutput_eq_entryTails`).
- **D'' = `halfDist`.** It tests `m₀ ≠ m₁`.

**The two gaps.**
- **Real** (`real_gap`): `2·Pr[D'] − Pr[D''] = Pr[D(NM_1)] − Pr[D(NM_0)]`.
  - `accept_nmGame_eq_rImpl` and `castImpl_indImpl_abs` (the latter for every attack) reduce it to the hybrid
    oracle.
  - While `m₀ = m₁`, the two coins agree: `expect_runB_good`, an equal-until-bad coupling.
- **Ideal** (`ideal_gap`): `2·Pr[D'] = Pr[D'']` for every simulator. With `histLen = 0` the oracle ignores `β`
  (`histImpl_coins`).

`abs_le_of_gap` combines the two gaps.

### 2. IND ⇒ SIM under CPA (`simNMSecure_of_nmSecure_cpa`)

**Hybrids.** `H_b = hybAcc … b` runs `A` against `rImpl … b`. On the first challenge `a`, `rImpl` answers
`⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩`; under CPA, `Dec` answers ⊥. The real experiment is `H_false`
(`realAcc_eq_hybAcc`).

**Ideal = `H_true`** (`exists_simulator`).
- The simulator is T2's machine of `chalHandler (simParams …)`, with `M`'s advice hard-wired.
- It answers the one challenge with one query and replays the record for repeated challenges.
- It has a separate branch for `ctLen(n) = 0`.
- **Budget 1.** `finCall = 1`, the run makes at most one query (`chalHandler_costBoundedBy`), and the
  finalization makes none. The new generic lemma `toCompOn_budget_eq` / `buildComp_budget_eq` (any budget at least
  the cost gives the same run) then brings it to budget 1.

**`NM_b = H_b` when `msgLen(n) > 0`** (`exists_nmAdversary`).
- `B` asks `⟨M(a; ρ), M(a; ρ̃)⟩`.
- For each output `c_i` it emits `c_i ‖ Enc(f^L) ‖ Enc((¬f)^L)`, with `f = [c_i = y]`. It does the same for each bit
  of `a`, `m` and `σ`, giving `3r + 2(pl + L + sl)` ciphertexts.
- `recDist` reads the result back with `NMCCA2.guessBit`. In `guessBit_encPair`, correctness makes a pair's two
  ciphertexts differ, so at most one of them is the challenge. `ctLen_pos` shows that `msgLen(n) > 0` forces
  `ctLen(n) > 0`.

**`msgLen(n) = 0`.** `hybAcc_true_eq_false` follows from `rImpl_eq_of_msgLen_eq_zero`, so the advantage is 0.

### Questions for the audit

Is either reduction lossy? Does an equality fail on some branch? Check:
- budget 0, `r = 0`, `sl = 0`;
- no challenge, and repeated challenges;
- `A` outputting the challenge, or a malformed or invalid ciphertext;
- codec timeouts;
- `ctLen = 0`;
- `m₀ = m₁`.

Does `SimNMSecure`'s quantifier order (`Sim` chosen before `D`) allow D' and D'' to be used against the same `Sim`?
Is the budget lemma sound in general?

## Also check

**Statement freeze.**
- `decls2` against the base: 269 added, 0 changed, 0 removed.
- Every pre-existing declaration is byte-identical: `SimNMSecure`, `NMSecure`, both experiments and
  `simNMSecure_cpa_iff_nmSecure_cpa`.
- Only the two target bodies and their sketches changed.

**Rule 10.** No touched declaration reads another file's definition, including generated matchers and projections.
- The 10 helpers are foreign to each other, to the owned file, to `Indistinguishability/*`, `OracleSecurity`,
  `Games/*`, `AdaptiveCPA/*` and `ChallengeSim`.
- The review's whole-file seals A and B pass for all 11 files at the delivered head, and again at the landing head.
- The explicit-unfold scan finds 0 foreign definitions.

**API** (policy §3).
- Names, formula docstrings, sketches, module docstrings, and the owned file's `## Contents`.
- No `@[simp]`. The one public `abbrev`, `runB`, has `runB_eq`.
- Sizes are all below 1000 lines; the largest is `SimIND`, at 912.

**Duplication.** Ruling (Seyoon, 2026-11-13): the undisclosed duplicates are accepted as ledger debt **DL-37**, with
named payback. That disposition is not a finding. What you can still raise:
- a copy that DL-37 or DL-36 misses;
- a disagreement with the payback plan.

The DL-37 copies:
- `chunkAt` = `coinBlock`;
- the private `padFin_replicate_false`;
- `impl_of_ret`, `rdU`…`rdLog`, `rdState`, `finSt`;
- the generic neighbours.

**Landing edits** (`5da558b4d97aca00efd6dc396a1b0f3bffff268b`). They change no statement and no proof route; text outside comments is identical in
all 11 files.
- LE-W re-wraps the 68 lines that were longer than 100 characters.
- LE-D1 adds formula docstrings to `chalRun_eq`, `simFin_eq` and `nmFin_eq`.
- LE-D2 adds proof sketches to 10 long proofs.
- LE-D3 adds `SimINDGap`'s `## Main definitions`.

**Land order** (ruling 2026-11-13). nm-sim lands before the DL-30–DL-34 consolidation. When the consolidation lands,
it re-points these files to the moved names. That is not a finding here.

## Evidence

- **`review.md`:** the maintainer's independent review (ACCEPT WITH LANDING EDITS), with its findings, its
  promotion-request table and the consolidation re-point list.
- **`verification.zip`:** the review's raw evidence, at the delivered head. `PROVENANCE.txt` and the inner
  `SHA256SUMS` describe it. It covers:
  - integrity (587/587, patch replay to tree `a39affb9`);
  - a fresh build of 262 modules with 0 errors;
  - the admission census (26 → 24);
  - decls2;
  - the axioms of all 574 stored constants;
  - seals A and B for all 11 files, with a base control;
  - paired controls (22 probe pairs per variant, ALL_OK);
  - the explicit-unfold scan (1,850 items);
  - lint.
- **`landing.zip`:** the landing-edit run at the head. It holds:
  - the full diff;
  - the rebuild of the 11 modules and 3 facades;
  - decls2 from the delivered head to the landing head (empty);
  - all 574 constants' axioms, unchanged;
  - seals A and B, 22/22 at the head;
  - lint;
  - the widths;
  - the sketch audit.
- **`landing/`:** logs at the final head on the full-library tree.
  - `root-order.txt` and `root-checks.jsonl`: the 11 modules, the 3 facades and root `TCSlib`, all rc 0, each row's
    `source_sha256` matching `source-head.json`. `audits/pass-shelat/Checks` imports none of them.
  - `axioms-head.log`: the two targets and `simNMSecure_cpa_iff_nmSecure_cpa` each print
    `[propext, Classical.choice, Quot.sound]`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `da56632fb066b657d3054865cc1b4f7535018951`.
- **`pr.diff.txt`:** `git diff` from the base to the head.
- **`source-head.json`:** the head hashes of the 11 changed files.
- **`sources.zip`:** the source closure of the owned module at the head.

## Findings delivery

Return `gate19-nm-sim-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement change, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/19-nm-sim/review.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/19-nm-sim/worker-report.md =====

# Fill `nm-sim` — final: Theorem 174.8 proved (both targets)

**Worker:** Claude (external).
- **Issue base:** `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on `cryptography/pass-shelat-ch2-4` (the merge
  of #294).
- **Local proof branch:** `fill/nm-sim`, head `a0ea340a1`, never pushed. `patches/` holds the whole
  series from the base: 3 commits, replayed below.
- **Pack:** read at exchange `6f1e13ae6`. `SHA256SUMS` 7/7 OK; `order.txt` 252 modules, `roots.txt` 97,
  `base-sorries.txt` 26.
- **Earlier deliveries:** checkpoint 1 at `fd99cad2b` and checkpoint 2 at `8a27d9698`, both on
  `exchange/pass-shelat-ch5-8`.

## Status

| Target | Status | Axioms |
|---|---|---|
| `FixedLengthPKScheme.nmSecure_of_simNMSecure` (SIM ⇒ IND, every attack) | **proved** | `propext`, `Classical.choice`, `Quot.sound` |
| `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` (IND ⇒ SIM, CPA) | **proved** | `propext`, `Classical.choice`, `Quot.sound` |
| `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa` | **admission-free** | `propext`, `Classical.choice`, `Quot.sound` |

- Both target statements are unchanged, and so is every other declaration, the statement prose and the
  global simp attributes.
- There was no escalation, and no reader of a frozen file was needed. **Reader requests: none.**
- The non-malleability chapter has no admission left. The sweep's `sorry` census is 24, against 26 at
  the base; the only change is the removal of the two targets.

## The proofs

Both directions follow the maintainer's routes. The owned file's sketches now describe the delivered
proofs. Both experiments are first read on T2's lengths (owned file, section *The experiments on T2's
lengths*):
- `castImpl_snmImpl`: `snmImpl`, read along `snmDin`/`snmDout`, is the hybrid oracle
  `NMSim.rImpl … false … ρ ρ' none`.
- `snmView_realView`, `snmView_idealView`: the views as strings.
- `simImpl_eq_histImpl`.
- `accept_snmReal_eq`, `accept_snmIdeal_eq`: `accept (snmReal …) = NMSim.realAcc …` and
  `accept (snmIdeal …) = NMSim.idealAcc …`.

### SIM ⇒ IND (`nmSecure_of_simNMSecure`; bound `|adv_NM| ≤ 2·adv(D') + adv(D'')`)

- **Sampler.** `halfSamp S` takes the parameter `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`) and outputs
  `m_β` for its single coin `β`. The history is empty (`histLen = 0`).
- **SIM adversary.** `A'` is T2's machine of `simHandler S ℓ = copyHandler …`. This is
  `NMCCA2.fwdHandler` (imported), with seed `0` and `finCall = 0`, and its finalization returns `A`'s
  output (`r = ℓ`, `sl = 0`). `Sim` comes from `h M A' (q·perCall + finCall) ℓ 0`.
- **Distinguishers.**
  - `D' = tailDist S D` uses `D`'s coins and advice. It outputs `0` if `m₀ = m₁`, and otherwise
    `[D(entry tails) = 1] == [m = m₁]`. The tails drop the `COPY` flag, so a copy reads as
    `nmDecrypt`'s `⊥` (`nmOutput_eq_entryTails`).
  - `D'' = halfDist S` tests `m₀ ≠ m₁`.
- **Real** (`real_gap`): `2·Pr[D'] − Pr[D''] = Pr[D(NM_1)] − Pr[D(NM_0)]`.
  - With `β` fixed, `NM_β` is `A`'s run against the hybrid oracle (`accept_nmGame_eq_rImpl`,
    `castImpl_indImpl_abs`).
  - While `m₀ = m₁` the two coins agree (`expect_runB_good`, an equal-until-bad coupling).
  - `real_identity` holds pointwise; `realAcc_copyHandler` reduces `A'` to `A`.
- **Ideal** (`ideal_gap`): `2·Pr[D'] = Pr[D'']` for every simulator.
  - With `histLen = 0` the oracle ignores `β` (`histImpl_coins`), so `β` is drawn after the run.
  - `ideal_identity` holds pointwise.
- `abs_le_of_gap` combines the two: `ε = 2ε' + ε''`.

### IND ⇒ SIM under CPA (`simNMSecure_of_nmSecure_cpa`)

**The hybrids.** `H_b = NMSim.hybAcc … b …` runs `A` against `rImpl … b …`. On the first challenge `a`
that oracle answers `⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩`, and `Dec = ⊥` under CPA. The real experiment is
`H_false` (`realAcc_eq_hybAcc`).

**Ideal = `H_true`** (`exists_simulator`).
- The simulator is T2's machine of `chalHandler (simParams …)`, with `M`'s advice hard-wired
  (`NMCCA2.exists_withAdviceOn`).
- `Dec` gets `⊥` without a query. The first challenge `a` makes the only query `a` and answers
  `⟨Enc_pk(M(a; ρ̃); re), h⟩`. Repeated challenges replay the record.
- It outputs `r` entries `[flag ∧ c_i = ỹ] ‖ c_i`, then `σ`. A separate branch covers `ctLen(n) = 0`,
  where `chunkMap` cannot cut.
- **Budget.**
  - `finCall = 1`, so T2's budget is at least 1, even at `q = 0`.
  - `chalHandler_costBoundedBy`: the run asks at most one query (`simulate_costBoundedBy_once`).
  - The finalization asks none (`simFinish`).
  - So `toCompOn_budget_eq` (the generic budget reduction the brief asks for) gives the run at budget 1.
- **The run.** `simComp_abs` gives the composition with the history oracle. `idealView_simOut` matches
  the views. `expect_simulate_rImpl_eager` draws the encryption coins in advance.

**`NM_b = H_b` when `msgLen(n) > 0`** (`exists_nmAdversary`).
- `B` is T2's machine of `chalHandler (nmParams …)`, with `M`'s advice hard-wired.
- On `a` it asks `⟨M(a; ρ), M(a; ρ̃)⟩` and answers `⟨y, h(M(a; ρ))⟩`.
- **Output.** For each `c_i`: `c_i ‖ Enc(f^L) ‖ Enc((¬f)^L)`, with `f = [c_i = y]`. Then the same pair for
  each bit of `a`, `m` and `σ`, all with one tape. That is `nmLen = 3r + 2(pl + L + sl)` ciphertexts.
- **The run.** `nmComp_abs`: `NM_b`'s oracles composed with the handler are `rImpl … b … ρ ρ̃ none`
  (`ofFn_drawWith_half` picks `M(a; ρ_b)`).
- **Distinguisher.** `recDist` reads the view back with `entF`/`bitG` and `NMCCA2.guessBit`.
  - `guessBit_encPair`: by correctness the two ciphertexts of a pair differ, so at most one of them is
    the challenge.
  - `ctLen_pos`: `msgLen(n) > 0` forces `ctLen(n) > 0`.
- **Glue.** The SIM advantage is `B`'s NM advantage when `msgLen(n) > 0`. When `msgLen(n) = 0` it is 0,
  because `hybAcc_true_eq_false` follows from `rImpl_eq_of_msgLen_eq_zero`.

### Edge cases

| Case | How it is covered |
|---|---|
| Budget 0 | `finCall = 1`; every transport is an equality of whole runs. |
| `r = 0`, `sl = 0` | Generic in both directions. |
| `msgLen(n) = 0` | SIM ⇒ IND: `m₀ = m₁`, advantage 0. IND ⇒ SIM: the hybrids coincide, and the simulator is exact even at `ctLen = 0`. |
| No challenge | The state stays `none`, read as the parameter `0`; the abstractions map it to the initial states. |
| Repeated challenges | `rImpl_some`, `chalHandler_impl_some`. |
| `A` outputs the challenge | `COPY` through the flag, read as `⊥ = nmDecrypt_challenge` in SIM ⇒ IND. |
| Malformed or invalid ciphertexts | Decrypted as given. |
| Codec timeouts | Contained in the transported runs. |
| `m₀ = m₁` (SIM ⇒ IND) | `D'` and `D''` both give 0, and the coupling makes those runs equal. |

## Changed files

| File | Lines | Change |
|---|---|---|
| `NonMalleability/Simulation.lean` (owned) | 792 | see below |
| `Simulation/Generic.lean` | 452 | new: budget reduction, eager coins, equal until bad, chunk maps, output-length transport |
| `Simulation/Hybrid.lean` | 681 | new: `rImpl`, `histImpl`, views, block lemmas, `realAcc`/`idealAcc`/`hybAcc` |
| `Simulation/SimIND.lean` | 895 | new: sampler, SIM adversary, `D'`, `D''`, identities |
| `Simulation/SimINDGap.lean` | 332 | new: `real_gap`, `ideal_gap` |
| `Simulation/Rounds.lean` | 349 | new: round readers, one-call lemmas, one-shot cost bound, seeds |
| `Simulation/Challenge.lean` | 407 | new: the challenge handler shared by both machines |
| `Simulation/Simulator.lean` | 614 | new: the simulator, `exists_simulator` |
| `Simulation/Reduction.lean` | 634 | new: the NM adversary |
| `Simulation/Recover.lean` | 502 | new: the NM distinguisher, the read-back |
| `Simulation/IndSim.lean` | 281 | new: `NM_b = H_b`, `exists_nmAdversary` |

The owned file's change:
- both proof bodies;
- the new section *The experiments on T2's lengths* (9 lemmas, 2 of them private);
- the private `abs_le_of_gap`;
- the two sketches;
- the title, which drops "(statement phase)";
- `## Main results` and a new `## Contents`;
- the imports of the ten helpers (the facade check requires all of them).

Every file is below 1000 lines, and every helper is in namespace
`TCSlib.Cryptography.Composability.NMSim`.

**Sketch edits.**
- **SIM ⇒ IND.** The text now names the delivered objects (`halfSamp`, `simHandler`, `tailDist`,
  `halfDist`). It states the bound `2·adv(D') + adv(D'')`; the old text said "twice the sum".
- **IND ⇒ SIM.** The text now names the hybrids `H_b`, the simulator's budget-1 argument, `B`'s output
  layout and the `msgLen(n) = 0` case.
- The mathematical routes are unchanged.

## New declarations

`evidence/declarations.txt` lists every declaration per file: 302, of which 34 are private. The
statement-level results:
- the owned lemmas above;
- `NMSim.real_gap`, `ideal_gap`, `realAcc_copyHandler`;
- `exists_simulator`, `simRun_eq`, `simComp_abs`, `idealView_simOut`;
- `exists_nmAdversary`, `nmRun_eq`, `nmComp_abs`, `recView_nmOut`, `recView_nmOutL`;
- `guessBit_encPair`, `ctLen_pos`;
- `chalHandler_impl_dec/_some/_none`, `chalHandler_costBoundedBy`;
- `realAcc_eq_hybAcc`, `hybAcc_true_eq_false`.

Every public definition has an `_eq`/field lemma or a `simps` attribute. There is no `@[simp]`.

## Promotion requests

**`Games/Machines.lean`:**
- `buildComp_budget_eq`, `toCompOn_budget_eq`: the budget reduction asked for in the brief.
- `buildComp_of_ret`.

**`Games/Efficiency.lean`** (T2 helpers):
- `impl_of_ret`, `impl_of_query`, `finish_of_ret`, `padFin_append_split`.
- `chunkStep`/`chunkEmit`/`chunkMap`, `polyTimeComputable_chunkMap`, `chunkMap_flatten`.
- `seedEquiv`, `seedEquivPoly` (with their `_ofFn`), `length_ofFn_coins`.
- `expect_toCompOn_outLen`.

**`Games/Hopping.lean` / `Games/Probability.lean`:**
- `expect_congr_of_allOutputs`, `expect_expect_sample`, `bind_congr_of_allOutputs`.
- `expect_simulate_eager`, `expect_eq_until_bad`.
- `costBoundedBy_bind_of_allOutputs`, `simulate_costBoundedBy_once`.
- The private `lin_expect`, `lin_expect'`, `lin_sample` (`SimINDGap`) are generic real arithmetic of
  expectations.

**List facts** (`Hybrid`): `chunkAt`, `length_chunkAt`, `take_eq_flatten_chunkAt`,
`length_flatten_map_range`, `length_flatten_map_const`, `chunkAt_flatten_append`, `drop_flatten_append`,
`map_chunkAt_flatten`, `ofFn_block`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`.
- `ofFn_eq_map_range` duplicates the public `ofFn_eq_map_range` of `ZeroKnowledge/ThreeColoring/Machines`
  and `ZeroKnowledge/GraphIsomorphism/SoundnessRep`, which have the same statement.
- Both are outside this fill's import closure (importing a ZK file was not reasonable). Please
  consolidate them with mine.

**`PublicKey/OracleSecurity.lean`** (after its split): `ctLen_pos` (correctness forces
`ctLen(n) > 0` when `msgLen(n) > 0`).

**`Indistinguishability/Encrypt.lean`:** `polyTimeComputable_guessBit`, which is also a DL overlap
(next section).

## DL-30–36 overlaps

Each item is re-derived from published readers, in general form:
- **DL-30–36 overlap: `flatMap_range_drop`** (`Generic`, private). `Forward`'s private lemma, for an
  arbitrary list (used by `chunkMap_flatten`).
- **DL-30–36 overlap: the round-input readers** `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns` and
  `fields_input` (`Rounds`). `Forward`'s private readers, extended by `rdU`, `rdZ`, `rdW` (the context)
  and public.
- **DL-30–36 overlap: `ofFn_padFin_eq_padL`** (`Rounds`). `AdaptiveCPA/Handler`'s private lemma, from
  the public `ofFn_padFin_eq_take`.
- **DL-30–36 overlap: `polyTimeComputable_guessBit`** (`Recover`). The content of `Encrypt`'s private
  `polyTimeComputable_guessFun`, on the bare string.

**Imported, not copied:**
- `NMCCA2`: `fwdHandler`, `fwdHandler_*`, `simulate_fwdHandler_impl`, `fields_finInput`,
  `polyTimeComputable_finFields`, `finU/finZ/finW/finA`, `exists_withAdviceOn`, `guessBit`,
  `guessBit_eq/_valid/_refused`.
- `AdaptiveCPA`: `castImpl`, `castImpl_eq`, `castImpl_self`, `expect_simulate_castImpl_toCompOn`,
  `simulate_eq_of_abs`, `ofFn_cast`, `ofFn_splitHalf_*`, `padFin_ofFn_zeroBits`.
- `ChallengeSim`: `expect_sample_equiv/_prod/_comm`, `expect_sub`.
- The owned readers of `Indistinguishability.lean` and `OracleSecurity.lean`.

## Evidence

**Environment.**
- `logs/preflight.log`: 4 CPUs; cgroup v1 with no memory limit.
- `logs/packages-check.log`: 11 packages match, 0 mismatch, 4 absent.
- `.lake/packages` is a symlink to this session's earlier narrowed fetch for nm-cca2, with the same
  `lake-manifest.json` pins and roots.
- `logs/cache-probe.log`.

**Bootstrap.** `logs/bootstrap-upstream.tsv` and `logs/bootstrap/`: the 160 upstream modules of the order,
one module per `scripts/lean_check_tree.sh` call, all pass.

**Sweep.**
- `logs/sweep.tsv` and `logs/sweep/*.log`: the 252 modules of `order.txt`, with the 10 helpers inserted
  before `NonMalleability/Simulation` (`sweep-order.txt`, 262 modules), each in its own call. All pass.
- `Games/Hopping`, which `Generic` imports, is already in the order (line 166).
- The owned modules were rechecked first: `logs/dev/cp2-*.log`, then again in the sweep.

**`sorry` census** (`logs/sorry-census.log`): 24 against the base's 26. Removed vs base:
`Simulation`: `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`. Added: none.

**Axioms.**
- `logs/axioms-targets.log`: the two targets and `simNMSecure_cpa_iff_nmSecure_cpa`, each
  `[propext, Classical.choice, Quot.sound]`.
- `logs/axioms-all.log`: all **574** stored constants of the 11 changed and new files, auxiliary and
  private ones included. **0** have an axiom outside those three, and no `sorryAx`.

**Rule-10 seals.** In `seal/` and `logs/seal/`:
- **Scan.** For each changed or new file, a census module with exactly the file's imports lists every seal
  candidate of its full TCSlib import closure: semireducible, non-instance, non-projection, non-private
  definitions, between 1145 and 1365 per file (`scan-*.log`).
- **Seal A** (`PolyExpr.eval` exempt) and **seal B** (`PolyExpr.eval` included): a verbatim copy of the
  file with `attribute [local irreducible]` on all candidates. **All 11 files and the base control pass
  both** (`summary-A.txt`, `summary-B.txt`, `sealA-*.log`, `sealB-*.log`). The base control is the base
  owned file.
- **Paired controls** (`controls-*.log`, `summary-controls.txt`). There are 14 readings through
  definition bodies:
  - foreign `PolyExpr.eval`, `NMSecure`, `OracleComp.AllOutputs`, `NUPPT.ofPolyTime`;
  - one per helper (`snmDin`, `entryL`, `halfSamp`, `simHandler`, `rdState`, `chalHandler`, `finSt`,
    `nmLen`, `bitG`);
  - the owned `snmCodec`.
- **Control results.** Unsealed, all pass. Sealed A, 13 fail (all but `PolyExpr.eval`). Sealed B, all 14
  fail.
- **What the first seal run found.** It caught definitional readings in Generic, SimIND, Rounds,
  Challenge, Reduction and the owned file: `AllOutputs`/`CostBoundedBy` read as their bodies;
  `NMSecure` introduced through its body; `ofPolyTime`'s coins read by `rfl`; `rImpl` applied without
  `rImpl_some`; Simulator's `finSt` unfolded by Reduction. Commit 3 replaces them by published lemmas
  (`allOutputs_pure/_query`, `costBoundedBy_query`, `NMSecure_iff`, `coins_ofPolyTime`, `rImpl_some`,
  the new `polyTimeComputable_finSt`). The results above are for the final sources, rerun after the sweep.
- **Proof terms.** While writing the proofs I also avoided terms that are well typed only by unfolding a
  foreign definition, for example `padFin_ofFn` applied to `padFin pl ⟦x⟧` with
  `x : Fin (snmDin … 1) → Bool`.

**Explicit-unfold scan** (`logs/rwids*.{log,tsv}`, `seal/RwIds*.lean`):
- Every identifier the added lines pass to `rw`/`rwa`/`erw`/`simp`/`simp only`/`simpa`/`dsimp`/
  `unfold`/`delta`/`show … from` is resolved in its file's namespace with the file's own `open`s.
- 977 entries. **0 foreign definitions are passed.** The definitions that are passed are each passed by
  their own file: Rounds' readers and seeds, `copyHandler`, `tailDist`, `finSt`, `nmLen`, `nmSeed`,
  `recDist`.

**Lint** (`logs/lint.log`): `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey
--check8b` gives 0 FAIL and 6 WARN. All six are on files outside this fill and identical at the base
(`logs/lint-base.log`).

**Patch replay** (`logs/patch-replay.log`): `git am` of the three patches on the base gives tree
`a39affb95…`, identical to `fill/nm-sim`.

**Tools.** `tools/` holds the scripts that produced the above.

**Performance.** `Recover` first took about 100 s: two `congr 1` steps tried to unfold foreign
definitions. They became explicit `congrArg₂`, and the module now takes about 4 s. In the sweep every
changed or new module takes at most about 14 s (`Challenge`, 14.1 s; `Reduction`, 10.1 s).

**AGENTS.md.** The repository's `AGENTS.md` says not to run `lean`/`lake`. The brief and the addendum
require `scripts/lean_check_tree.sh`, and I followed the brief.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/fills/nm-sim/issued-r1/brief.md =====

# Claude fill · simulation-based and indistinguishability-based non-malleability (`nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`)

**Issue base** `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on `cryptography/pass-shelat-ch2-4` (the merge of #294).
**Unit** `nm-sim`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the two admitted theorems of [PS10, Theorem 174.8], in the form of [PSV07] (SIM-NME′ at one message), in
`TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean`. With them,
`simNMSecure_cpa_iff_nmSecure_cpa` (already proved from the two) becomes admission-free, and the non-malleability
chapter has no admissions left. The statements passed their Gate 06 audit (#232).

**This fill runs in parallel with the landing of the `dl-consolidation` job**, which moves the generic lemmas of
duplication-ledger rows DL-30 to DL-34. Read the duplication rule below.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/nm-sim` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/nm-sim/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed files;
  - `evidence/`;
  - `SHA256SUMS` over the whole payload.
- Commit as `fill nm-sim: checkpoint N` and `fill nm-sim: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## Targets (frozen; quoted from the issue base)

```lean
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  sorry

theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  sorry
```

They live in namespace `TCSlib.Cryptography.Composability.FixedLengthPKScheme`, with `S : FixedLengthPKScheme`.
- **`SimNMSecure atk`** (`SimNMSecure_iff`): for every sampler `M : MsgSampler`, adversary `A` and polynomials
  `q`, `r`, `sl`, there is a simulator `Sim` such that every distinguisher `D` has negligible advantage between
  `snmReal atk M A q r sl D` and `snmIdeal M Sim r sl D`.
  - In `snmIdeal` the simulator runs through `simCodec` **with query budget 1** (`Sim.toCompOn … n 1 …`).
- **`NMSecure atk`** (`NMSecure_iff`, `nmGame_eq`, in `NonMalleability/Indistinguishability.lean`): for all `A`,
  `q`, `ℓ` and `D`, negligible advantage between `nmGame atk A q ℓ D false` and `true`.

Each target's docstring sketch is the maintainer's route. You may edit a sketch to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `MsgSampler` and `draw_eq`, `histAt_eq`, `simSpec_eq`; `snmInLens_*`, `snmOutLens_*`, `snmSpec_eq`, `SnmState_eq`, `snmImpl_dec`, `snmImpl_challenge`, `snmImpl_dec_cpa`, `snmCodec_*`, `snmCt_eq`, `snmSigma_eq`, `snmEntry_eq`, `snmView_eq`, `snmReal_eq`, `simImpl_eq`, `simCodec_*`, `simEntry_fst/_snd`, `snmIdeal_eq`, `SimNMSecure_iff` | `NonMalleability/Simulation.lean` (owned; the statement-phase readers) |
| `nmCodec_*`, `nthCt_eq`, `nmDecrypt_eq`, `nmDecrypt_challenge`, `nmOutput_eq`, `nmGame_eq`, `NMSecure_iff`, and the proved Theorem 175.9 | `NonMalleability/Indistinguishability.lean` |
| Public helpers of Theorem 175.9: `fwdHandler`, `fwdHandler_impl`, `simulate_fwdHandler_impl`, the `fin*` readers, `logEmit` and its lemmas (`Forward`); `cntRead`, `ansRead`, `exists_withAdviceOn`, the decrypting finalization (`Decrypt`); `encHandler`, `guessBit`, `guessBit_valid`, `guessBit_refused`, `guessDist_nmOutput`, `indImpl_eq_of_msgLen_eq_zero` (`Encrypt`) | `NonMalleability/Indistinguishability/{Forward,Decrypt,Encrypt}.lean` (models and reusable lemmas; import them, do not copy) |
| `FixedLengthPKScheme` fields (`correct`, `enc_length`, `gen_uniform`, …), `inLens_*`, `outLens_*`, `indSpec_*` (incl. `indSpec_decRng`), `indImpl_dec_onSpec(_cast)`, `indImpl_challenge_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `FixedLengthScheme.decAnswer`, `decOpen_*` and their readers | `PrivateKey/OracleSecurity.lean` |
| T1 `Games.exists_handlerMachine`, T2 `Games.exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, T4 `exists_toOracleAdversary_of_bitCodec`, the `PolyHandler`/`InteractiveHandler` readers (`call`: **at most** `perCall(n)` outer queries per inner call) | `Games/Efficiency.lean` |
| `buildComp_*` (incl. `buildComp_costBoundedBy`), `CostBoundedBy` (`.mono`, `.bind`), `bitCodec_*`, `decodeBitMove`, `simulate` equations, `OracleComp` laws, `advantage_eq`, `accept_eq` | `Games/*` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice`, `exists_seq`, `exists_reparam`; `NUPPT` run/coin readers; `distinguisherL_eq`; `Negligible` closure (`Negligible.add`, scalar multiples) | `Complexity/Randomized/Closure.lean`, `Asymptotic/*`, `Foundations/Negligible.lean` |

## Proof route and checkpoints

1. **SIM ⇒ IND, every attack** (`nmSecure_of_simNMSecure`; the target's sketch). Given an NM adversary `A`
   (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`:
   - the sampler `M` with parameter `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`, the IND challenge layout) that
     outputs `m_β` for its first coin bit `β`, with a constant history (`histLen = 0`);
   - the SIM adversary `A'` forwards `A`'s `Dec` and challenge queries (a T2 handler with one outer call per
     inner query, like `fwdHandler`), outputs `A`'s `ℓ` ciphertexts, `r = ℓ`, `sl = 0`;
   - take `Sim` from `h M A' q ℓ 0`;
   - `D'` reads `a = ⟨m₀, m₁⟩` and `m` from the view, outputs `0` when `m₀ = m₁`, and otherwise whether `D`'s
     verdict on the entries (with `COPY` read as `nmDecrypt`'s `⊥`) equals the `β` with `m = m_β`; `D''` tests
     `m₀ ≠ m₁`.
   - **Real:** given `β`, `snmReal` is `NM_β` (the `Dec` and challenge oracles agree with `indImpl`, refusal and
     `⊥` included). So `NM`'s advantage is `2·(Pr_real[D' = 1] − ½·Pr_real[m₀ ≠ m₁])`.
   - **Ideal:** the simulator's view is independent of `β` (constant history; `β` is a coin of the sampler only),
     so `Pr_ideal[D' = 1] = ½·Pr_ideal[m₀ ≠ m₁]`.
   - Hence `NM`'s advantage is at most `2·adv(D') + adv(D'')`, both negligible (one `Sim` for all
     distinguishers).

   Send checkpoint 1.
2. **IND ⇒ SIM under CPA** (`simNMSecure_of_nmSecure_cpa`; the target's sketch). Fix `M`, `A`, `q`, `r`, `sl`.
   - **The simulator** runs `A` on `pk`, answering `Dec` with `⊥` (`snmImpl_dec_cpa`). On `A`'s first challenge `a`
     it makes its **only** outer query `a`, gets `h(m)`, draws `m̃ ← M(a)` with its own coins (it runs `M`, with
     `M`'s advice hard-wired as in `exists_withAdviceOn`), encrypts `ỹ ← Enc_pk(m̃)` and answers `⟨ỹ, h(m)⟩`;
     repeated challenges get the recorded answer without an outer query. It outputs `A`'s `r` ciphertexts, each
     flagged `COPY` iff it equals `ỹ`, and `σ`. If `A` never asks, it never queries.
   - **The query budget.** T2 gives the simulator's machine at budget `q·perCall + finCall`; `snmIdeal` runs it at
     budget 1. The handler makes at most one outer query on every path, so prove the generic budget reduction:
     a machine whose computation at budget `K ≥ j` is `CostBoundedBy` `j` has the same computation at budget `j`
     (induction on `buildComp` with `buildComp_succ_of_ret/_of_query`). Put it in a helper and list it as a
     promotion request for `Games/Machines.lean`.
   - **The NM adversary** `B`: on `a` it draws `m, m̃ ← M(a)`, asks its challenge on `⟨m, m̃⟩`, answers `A` with
     `⟨y, h(m)⟩`; it outputs `A`'s ciphertexts, then for each bit `x` of `a`, `m`, `σ` and the copy flags
     `[c_i = y]` the pair `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})` (reuse `guessBit`, `guessBit_valid`,
     `guessBit_refused` and the encryption lemmas of `Indistinguishability/Encrypt.lean`).
   - The NM distinguisher reconstructs `(a, m, (d_i)_i, σ)` and runs `D`: `NM_0` is the real experiment and `NM_1`
     the ideal one with the simulator above. So the SIM advantage equals `B`'s NM advantage at each `n` with
     `msgLen(n) > 0`.
   - At `msgLen(n) = 0`, `m = m̃` and the real and ideal experiments coincide, so the advantage is 0.
   - If `A` never asks, both experiments use `a = 0^{paramLen(n)}`.

   Send checkpoint 2.
3. **Final.** Both targets proved; `simNMSecure_cpa_iff_nmSecure_cpa` admission-free. Send the final delivery.

Check the edge cases:
- budget 0;
- `r = 0`, `sl = 0`;
- `msgLen(n) = 0`;
- no challenge asked;
- repeated challenges;
- `A` outputting the challenge itself, or a malformed or invalid ciphertext;
- the codecs' timeout outputs, in every direction;
- `m₀ = m₁` (SIM ⇒ IND).

If either sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation (a
checkpoint with the counterexample or the missing fact). Do not weaken a statement.

## Scope and proof discipline

- **Owned file.** You own `NonMalleability/Simulation.lean`: replace the two proof bodies, edit their sketches,
  and update the module title (drop "(statement phase)") and the `## Main results` status.
- **Helper modules.** Permitted under `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/`. The
  owned file imports them precisely and gets a `## Contents` list.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file. `PublicKey/OracleSecurity.lean` is at 999 lines and will be split at the
  consolidation's landing: request any reader for it in `REPORT.md`, with its exact statement. If a lemma belongs
  in an existing file, put it in your helper module and list it as a promotion request. If a reader of another
  file's definition is missing, escalate: record the exact obligation and the reader you need, and push a
  checkpoint.
- **Duplication (binding).**
  - Do not copy public lemmas: import them where they are at the issue base (including the Theorem 175.9 helpers
    above). The maintainer re-points them at landing if the consolidation has moved them.
  - Do not copy private lemmas from `AdaptiveCPA/`, `BitwiseCPA/`, `OracleFromPRF/` or
    `NonMalleability/Indistinguishability/`. If you need one, re-derive it from published readers in your helper
    module, disclose it in `REPORT.md` as **"DL-30–36 overlap: <item>"**, and keep its statement in the general
    form.
  - Any other generic probability, simulation, machine or list fact goes on your promotion list. Grep first.
- **Statements.** Preserve both target statements, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial (policy §3).
  No `@[simp]`; a new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (252 modules) and the narrow `roots.txt` (97) per the addendum. Check
  one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules
  before their consumers.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare the `sorry` warnings with
  `base-sorries.txt` (26): the only change must be the removal of the two targets.
- **Axioms.**
  - Print the axioms of both targets and of `simNMSecure_cpa_iff_nmSecure_cpa`. Expect only `propext`,
    `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls and
    paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
  - Report the seal both with `PolyExpr.eval` excluded as notation and with it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give:
  - the base and the targets' status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests, and every "DL-30–36 overlap" item;
  - the evidence.

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | Open (deferred) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | Open (deferred) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | Open (deferred) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | Open (deferred) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | Open (deferred) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | Open (deferred) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2 | Open (deferred) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; promote the accepted requests (review r1 table). |

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimINDGap
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation-based non-malleability

[PS10, Definition 173.7 and Theorem 174.8], in the form of [PSV07] (ruling of 2026-11-05: the
non-malleability notions of §7.1.5–7.1.6 follow Pass, shelat and Vaikuntanathan).

**Why not the source's form.** As written, Theorem 174.8 is false (inventory Thm-174.8).
- Definition 173.7's simulator `S(1^n, z)` gets no public key. An adversary that outputs a fresh
  `Enc_pk(0^n)` hits the relation `R(m) = {0^n}` with probability 1, while a simulator without
  `pk` produces a ciphertext that decrypts to `0^n` under a fresh key only with the probability
  of guessing one.
- The quantifiers of Definitions 172.6 and 173.7 do not line up: adaptive `m₀, m₁` in one, a
  fixed `m` in the other.

**The form taken: SIM-NME′ at one message** [PSV07, Definition 1, with `ℓ = 1`; "single-message
security" there].
- *Real.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← A₁^{O₁}(pk)`; `m ← M`; `y ← Enc_pk(m)`;
  `((c₁, …, c_r), σ) ← A₂^{O₂}(y, h(m), s)`; output `(M, m, (d₁, …, d_r), σ)` with
  `d_i = COPY` if `c_i = y` and `d_i = Dec_sk(c_i)` otherwise (possibly `⊥`: invalid ciphertexts
  are allowed, the "′" of [PSV07]).
- *Ideal.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← S₁(pk)`; `m ← M`; `((c₁, …, c_r), σ) ← S₂(h(m), s)`;
  output `(M, m, (d₁, …, d_r), σ)` with `d_i = COPY` if `c_i = COPY` and `Dec_sk(c_i)` otherwise.
- *Security.* For every history function `h`, every adversary `A` and all polynomials `r`, there
  is a simulator `S` whose experiment no distinguisher tells from `A`'s. [PSV07] replaces the
  relations `R` of [PS10] and [DDN00] by distinguishers ("any p.p.t. distinguisher can be
  described as a p.p.t. relation and vice versa", remarks after Definition 2).

**The encoding.**
- *Phases and oracles* are those of Definition 171.5: the challenge query separates `A₁` from
  `A₂`, and `Dec` answers per the attack (`decOpen`), refusing the challenge.
- *The sampler.* [PSV07]'s `A₁` outputs a machine `M`. Here a sampler `M` (a machine with a
  history function, `MsgSampler`) is quantified together with `A`, and `A₁` outputs a parameter
  `a`, with `m = M(a)` read at `msgLen(n)` bits. The output carries `a` in place of `M`'s
  description. With `M` a universal clocked machine this is [PSV07]'s form, and the fixed
  lengths make every sampler valid in [PSV07]'s sense.
- *The simulator* is one oracle machine on `pk`. Its single query `a` is answered by `h(m)`,
  where `m = M(a)` is drawn by the experiment: `S₁` is its run up to the query, `S₂` the rest. It
  has no `Dec` oracle under any attack, as in [PSV07]. Each of its `r` outputs is a `COPY` flag
  and a ciphertext.
- *No challenge.* If the machine never queries, its parameter is `0^{pl(n)}` and `m = M(0^{pl(n)})`
  (in both experiments).

**Theorem 174.8.** [PSV07] proves that SIM-NME′ and IND-NME′ (Definition 172.6 at many messages)
coincide **under CPA** (its Theorem 3), and that SIM-NME′ is **strictly stronger under CCA1 and
CCA2**, even at one message (its Theorem 4). It always implies IND-NME′ (its Corollary 1). So
Theorem 174.8 is stated under CPA, with the implication SIM ⇒ IND for every attack. [PSV07]
defers both proofs to its full version; the sketches below are the maintainer's.

## Main definitions

* `MsgSampler`: a message sampler with a history function.
* `FixedLengthPKScheme.snmReal`, `FixedLengthPKScheme.snmIdeal`: the two experiments.
* `FixedLengthPKScheme.SimNMSecure`: [PS10, Definition 173.7] as [PSV07, Definition 1].

## Main results

* `FixedLengthPKScheme.nmSecure_of_simNMSecure`: SIM ⇒ IND for every attack [PSV07, Corollary 1].
* `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa`: IND ⇒ SIM under CPA [PSV07, Theorem 3].
* `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa`: Theorem 174.8 under CPA, from the two.
* `FixedLengthPKScheme.accept_snmReal_eq`, `FixedLengthPKScheme.accept_snmIdeal_eq`: both
  experiments on T2's lengths (`NMSim.realAcc`, `NMSim.idealAcc`).

## Contents

The proofs use the helper modules under `NonMalleability/Simulation/` (namespace
`TCSlib.Cryptography.Composability.NMSim`):
* `Generic`: budget reduction, coins drawn in advance, equal until bad, chunk maps;
* `Hybrid`: the hybrid oracle `rImpl` (an encryption of `M(a; ρ)` or of an independent draw), the
  history oracle, the views as strings and the acceptance rates `realAcc`, `idealAcc`, `hybAcc`;
* `SimIND`, `SimINDGap`: SIM ⇒ IND (the sampler `⟨m₀, m₁⟩ ↦ m_β`, the SIM adversary, `D'`, `D''`,
  and the real and ideal gaps);
* `Rounds`, `Challenge`: rounds of T2's handlers and the challenge handler shared by the two
  machines of IND ⇒ SIM;
* `Simulator`: the simulator (the ideal experiment is the hybrid `H_true`);
* `Reduction`, `Recover`, `IndSim`: the NM adversary, the NM distinguisher, and `NM_b = H_b`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Definition 173.7 and Theorem 174.8 (book pp. 173–174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definitions 1–4, Theorems 3 and 4,
  Corollary 1.
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [DDN00] D. Dolev, C. Dwork, M. Naor, *Nonmalleable cryptography*, SIAM J. Comput. 30(2), 2000
  (cited through [PSV07]).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- **A message sampler with a history function** [PSV07, Definition 1]: a machine `M` activated
on a `paramLen(n)`-bit parameter, whose output is the message, and a polynomial-time history
function `h`, read at `histLen(n)` bits. -/
structure MsgSampler where
  /-- The sampler, activated on the adversary's parameter. -/
  samp : NUPPT
  /-- The length of the parameter. -/
  paramLen : PolyExpr
  /-- The history function `h`. -/
  hist : List Bool → List Bool
  /-- The length at which `h(m)` is read. -/
  histLen : PolyExpr
  /-- `h` is polynomial-time. -/
  hist_poly : PolyTimeComputable hist

namespace MsgSampler

variable (M : MsgSampler)

/-- The message `m = M(a)` with the sampler's coins `ρ`, read at `ℓ` bits. -/
def draw (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) : Fin ℓ → Bool :=
  padFin ℓ (M.samp.runAt n (List.ofFn a) ρ)

/-- Drawing a message pads the sampler's output on parameter `a` and coins `ρ` to `ℓ` bits. -/
theorem draw_eq (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) :
    M.draw ℓ n a ρ = padFin ℓ (M.samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)`, read at `histLen(n)` bits. -/
def histAt {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) : Fin (M.histLen.eval n) → Bool :=
  padFin _ (M.hist (List.ofFn m))

/-- The sampled message's history is `M.hist (List.ofFn m)`, padded to `histLen(n)` bits. -/
theorem histAt_eq {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) :
    M.histAt n m = padFin (M.histLen.eval n) (M.hist (List.ofFn m)) := rfl

/-- The simulator's oracle at parameter `n`: the parameter in, the history out. -/
abbrev simSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)

/-- The simulator's oracle is `bitSpec` with parameter-length queries and history-length
answers. -/
theorem simSpec_eq (n : ℕ) :
    M.simSpec n = bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n) := rfl

end MsgSampler

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-! ### The real experiment -/

/-- The query lengths of the real experiment's oracles `Dec` and `Challenge`. -/
def snmInLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => M.paramLen.eval n

/-- A real-experiment decryption query has `ctLen(n)` bits. -/
theorem snmInLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 0 = S.ctLen.eval n := rfl

/-- A real-experiment challenge query has `paramLen(n)` bits. -/
theorem snmInLens_one (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 1 = M.paramLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` the challenge
ciphertext and the history. -/
def snmOutLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n + M.histLen.eval n

/-- A real-experiment decryption answer has one validity bit followed by `msgLen(n)` bits. -/
theorem snmOutLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 0 = S.msgLen.eval n + 1 := rfl

/-- A real-experiment challenge answer has `ctLen(n) + histLen(n)` bits. -/
theorem snmOutLens_one (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 1 = S.ctLen.eval n + M.histLen.eval n := rfl

/-- The two oracles of the real experiment at parameter `n`. -/
abbrev snmSpec (M : MsgSampler) (n : ℕ) : OracleSpec (Fin 2) :=
  bitSpec (S.snmInLens M n) (S.snmOutLens M n)

/-- The real experiment's oracle specification is `bitSpec` at its published query and
answer lengths. -/
theorem snmSpec_eq (M : MsgSampler) (n : ℕ) :
    S.snmSpec M n = bitSpec (S.snmInLens M n) (S.snmOutLens M n) := rfl

/-- The state of the real experiment's oracles: the challenge, with the parameter it was asked
on, once asked. -/
abbrev SnmState (M : MsgSampler) (n : ℕ) : Type :=
  Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool))

/-- The real oracle state is an optional pair of a `ctLen(n)`-bit ciphertext and a
`paramLen(n)`-bit sampler parameter. -/
theorem SnmState_eq (M : MsgSampler) (n : ℕ) :
    S.SnmState M n =
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool)) := rfl

/-- **The oracles of the real experiment** at parameter `n`, for the keys `pk`, `sk` and the
sampler's coins `ρ`.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is
  not the challenge, and `⊥` (all `false`) otherwise.
- `Challenge` on the parameter `a`, the first time: `m = M(a; ρ)`, `y ← Enc_pk(m)`; it answers
  `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats the recorded answer. -/
noncomputable def snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) : QueryImpl (S.snmSpec M n) (S.SnmState M n) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, a, s =>
    match s with
    | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        let y : Fin (S.ctLen.eval n) → Bool :=
          padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
        .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a))

/-- A real-experiment decryption query returns the encoded decryption exactly when the oracle
is open and the ciphertext is not the recorded challenge; otherwise it returns all-false bits. -/
theorem snmImpl_dec (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits (S.msgLen.eval n + 1), s) := rfl

/-- A real-experiment challenge query repeats the recorded ciphertext and history when a
challenge exists; otherwise it encrypts the sampled message and records the ciphertext and
parameter [PSV07, Definition 1]. -/
theorem snmImpl_challenge (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (a : Fin (M.paramLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 1 a s =
      match s with
      | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
      | none =>
        (ProbComp.sample (S.enc.Coins n)).bind fun re =>
          let y : Fin (S.ctLen.eval n) → Bool :=
            padFin (S.ctLen.eval n)
              (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
          .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a)) := rfl

/-- Under CPA, `Dec` never answers. -/
theorem snmImpl_dec_cpa (M : MsgSampler) (n : ℕ) (pk sk : List Bool) (ρ : M.samp.Coins n)
    (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl .cpa M n pk sk ρ 0 c s = .pure (zeroBits _, s) := by
  simp [snmImpl, FixedLengthScheme.decOpen_cpa]

/-- The codec of the adversary: the two oracles, and a final output of `r` ciphertexts followed by
an `sl`-bit `σ`. -/
def snmCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (S.snmSpec M n) (Fin (r * S.ctLen.eval n + sl) → Bool) :=
  bitCodec (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The real-experiment codec uses `decodeBitMove` with `r * ctLen(n) + sl` output bits. -/
theorem snmCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.snmCodec M n r sl).decodeMove w =
      decodeBitMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w :=
  bitCodec_decodeMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w

/-- The real-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem snmCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (S.snmSpec M n).dom i × (S.snmSpec M n).rng i) :
    (S.snmCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) e

/-- When its query budget expires, the real-experiment codec returns
`zeroBits (r * ctLen(n) + sl)`. -/
theorem snmCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.snmCodec M n r sl).timeout = zeroBits (r * S.ctLen.eval n + sl) :=
  bitCodec_timeout (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The `i`-th of the `r` ciphertexts in an adversary's output. -/
def snmCt {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j)))

/-- Real output ciphertext `i` has bit `j` at `Fin.castAdd sl (finProdFinEquiv (i, j))`. -/
theorem snmCt_eq {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    S.snmCt w i = fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j))) := rfl

/-- The final `σ`: the last `sl` bits of an output. -/
def snmSigma {k sl : ℕ} (w : Fin (k + sl) → Bool) : Fin sl → Bool :=
  fun j => w (Fin.natAdd k j)

/-- The final output string's bit `j` is input bit `Fin.natAdd k j`. -/
theorem snmSigma_eq {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    snmSigma w = fun j => w (Fin.natAdd k j) := rfl

/-- **The entry `d_i`** [PSV07, Definition 1]: `COPY` if `copy`, and `Dec_sk(c)` otherwise.
Encoded as a `COPY` flag followed by `Dec`'s answer (a validity flag and the message; all `false`
for `⊥`). -/
def snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    Fin (S.msgLen.eval n + 1 + 1) → Bool :=
  if copy then Fin.cons (α := fun _ => Bool) true (zeroBits _)
  else Fin.cons (α := fun _ => Bool) false
    (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))))

/-- An entry begins with its COPY flag; a copy has an all-false payload, and every other entry
has the encoded decryption as payload [PSV07, Definition 1]. -/
theorem snmEntry_eq {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.snmEntry sk copy c =
      if copy then Fin.cons (α := fun _ => Bool) true (zeroBits (S.msgLen.eval n + 1))
      else Fin.cons (α := fun _ => Bool) false
        (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c))))) := rfl

/-- **The output `(M, m, (d₁, …, d_r), σ)`** handed to the distinguisher, with the parameter `a`
in place of `M`: the concatenation of its fixed-length parts. -/
def snmView {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) : List Bool :=
  List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ

/-- The distinguisher's view concatenates the parameter, sampled message, flattened entries,
and final `σ` [PSV07, Definition 1]. -/
theorem snmView_eq {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) :
    S.snmView a m d σ =
      List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ :=
  rfl

/-- **The real experiment** `SIM-NME′(Π, A, n)` [PSV07, Definition 1, `ℓ = 1`] for the attack
`atk`, the sampler `M`, query budget `q`, `r` output ciphertexts and an `sl`-bit `σ`, followed
by the distinguisher `D`: sample the keys and the coins, run `A` on `pk` against the oracles, and
output `D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a copy of the challenge. -/
noncomputable def snmReal (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (A.Coins n)).bind fun rA =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate
      (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
      (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
    fun res =>
      let a := (res.2.map Prod.snd).getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
            (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
          (snmSigma res.1)) rD)

/-- The real simulation experiment samples all coins, runs the adversary against its oracles,
and applies the distinguisher to the resulting parameter, message, entries, and final output
[PSV07, Definition 1]. -/
theorem snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) :
    S.snmReal atk M A q r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (A.Coins n)).bind fun rA =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate
          (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
          (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
        fun res =>
          let a := (res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
                (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
              (snmSigma res.1)) rD)) := rfl

/-! ### The ideal experiment -/

/-- **The oracle of the ideal experiment**: on the parameter `a` (the first one asked, recorded),
the history `h(m)` of `m = M(a; ρ)`. -/
noncomputable def simImpl (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    QueryImpl (M.simSpec n) (Option (Fin (M.paramLen.eval n) → Bool)) unifSpec :=
  fun _ a s => .pure (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a))

/-- The ideal oracle returns the history of the sampled message at the recorded parameter,
or at the current query if no parameter has been recorded, and records that parameter. -/
theorem simImpl_eq (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    S.simImpl M n ρ =
      fun _ a s => .pure
        (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a)) := rfl

/-- The codec of the simulator: its one oracle, and a final output of `r` entries, each a `COPY`
flag and a ciphertext, followed by an `sl`-bit `σ`. -/
def simCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (M.simSpec n) (Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) :=
  bitCodec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The ideal-experiment codec uses `decodeBitMove` with parameter and history lengths and
`r * (ctLen(n) + 1) + sl` output bits. -/
theorem simCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.simCodec M n r sl).decodeMove w =
      decodeBitMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
        (r * (S.ctLen.eval n + 1) + sl) w :=
  bitCodec_decodeMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) w

/-- The ideal-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem simCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (M.simSpec n).dom i × (M.simSpec n).rng i) :
    (S.simCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) e

/-- When its query budget expires, the ideal-experiment codec returns
`zeroBits (r * (ctLen(n) + 1) + sl)`. -/
theorem simCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.simCodec M n r sl).timeout = zeroBits (r * (S.ctLen.eval n + 1) + sl) :=
  bitCodec_timeout (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The `i`-th entry of the simulator's output: its `COPY` flag and its ciphertext. -/
def simEntry {n r sl : ℕ} (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) (i : Fin r) :
    Bool × (Fin (S.ctLen.eval n) → Bool) :=
  (w (Fin.castAdd sl (finProdFinEquiv (i, 0))),
    fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j.succ))))

attribute [simps (config := { isSimp := false }) fst snd] simEntry

/-- **The ideal experiment** `SIM-NME′‾(Π, S, n)` [PSV07, Definition 1, `ℓ = 1`] for the sampler
`M`, `r` output entries and an `sl`-bit `σ`, followed by the distinguisher `D`: sample the keys
and the coins, run the simulator on `pk` against the history oracle with one query, and output
`D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a flagged entry and `Dec_sk(c_i)`
otherwise. -/
noncomputable def snmIdeal (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (Sim.Coins n)).bind fun rS =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate (S.simImpl M n ρ)
      (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
    fun res =>
      let a := res.2.getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
            (S.simEntry res.1 i).2)
          (snmSigma res.1)) rD)

/-- The ideal simulation experiment samples all coins, runs the simulator against the history
oracle, and applies the distinguisher to the parameter, message, decoded entries, and final
output [PSV07, Definition 1]. -/
theorem snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    S.snmIdeal M Sim r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (Sim.Coins n)).bind fun rS =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate (S.simImpl M n ρ)
          (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
        fun res =>
          let a := res.2.getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
                (S.simEntry res.1 i).2)
              (snmSigma res.1)) rD)) := rfl

/-! ### The experiments on T2's lengths -/

section Transport

open NMSim
open AdaptiveCPA (castImpl castImpl_eq expect_simulate_castImpl_toCompOn padFin_ofFn_zeroBits)

/-- **The real experiment's oracles on T2's lengths are the hybrid oracle with `b = false`:**
read along `snmDin`, `snmDout`, `snmImpl` is `NMSim.rImpl … false … ρ ρ' none` (for every `ρ'`).

**Proof sketch.** Query by query (`snmImpl_dec`, `snmImpl_challenge`, `rImpl_dec`, `rImpl_some`,
`rImpl_none_lazy`, `rImpl_none_eager`): the casts keep the strings (`ofFn_padFin_of_length`), and
`M.draw`, `M.histAt` are `drawWith`, `histWith`. -/
theorem castImpl_snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ ρ' : M.samp.Coins n) :
    castImpl (ins := fun i => (snmDin S M.paramLen i).eval n)
        (outs := fun i => (snmDout S M.histLen i).eval n) (S.snmImpl atk M n pk sk ρ) =
      rImpl S atk false M.samp M.paramLen M.histLen M.hist n pk sk ρ ρ' none := by
  funext i x s
  rw [castImpl_eq]
  match i, s with
  | 0, s =>
    have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
      GGMRed.ofFn_padFin_of_length (by
        rw [List.length_ofFn]; show (snmDin S M.paramLen 0).eval n = _; rw [snmDin_zero])
    erw [S.snmImpl_dec atk M n pk sk ρ (padFin (S.ctLen.eval n) (List.ofFn x)) s]
    rw [rImpl_dec, hx]
    by_cases hc : (FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
    · rw [if_pos hc, if_pos hc, OracleComp.pure_bind]
    · rw [if_neg hc, if_neg hc, OracleComp.pure_bind]
      dsimp only
      erw [padFin_ofFn_zeroBits]
  | 1, some (y, a) =>
    erw [S.snmImpl_challenge atk M n pk sk ρ (padFin (M.paramLen.eval n) (List.ofFn x))
      (some (y, a))]
    dsimp only
    rw [OracleComp.pure_bind, rImpl_some]
    dsimp only
    erw [List.ofFn_fin_append]
    simp only [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]
  | 1, none =>
    erw [S.snmImpl_challenge atk M n pk sk ρ (padFin (M.paramLen.eval n) (List.ofFn x)) none]
    dsimp only
    rw [rImpl_none_lazy, OracleComp.bind_assoc]
    refine congrArg _ (funext fun re => ?_)
    rw [OracleComp.pure_bind, rImpl_none_eager, if_neg Bool.false_ne_true, encWith_eq]
    dsimp only
    erw [List.ofFn_fin_append]
    simp only [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]

/-- An entry as a string: `⟦snmEntry sk copy c⟧ = entryL S n sk copy ⟦c⟧`. -/
theorem ofFn_snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    List.ofFn (S.snmEntry sk copy c) = entryL S n sk copy (List.ofFn c) := by
  rw [snmEntry_eq, entryL_eq]
  cases copy
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  · rw [if_pos rfl, if_pos rfl, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ofFn_zeroBits]

/-- **The real experiment's view is `realView`:** for an output `w` and a final state `s`,
`snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = realView … ⟦w⟧ s`, with `a` the recorded parameter.

**Proof sketch.** Block by block: `ofFn_block` for the ciphertexts, `decide_map_ofFn` for the
copy test, `ofFn_snmEntry` for the entries and `ofFn_natAdd_eq_drop` for `σ`. -/
theorem snmView_realView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
    (w : Fin (r * S.ctLen.eval n + sl) → Bool) (s : S.SnmState M n) :
    S.snmView ((s.map Prod.snd).getD (zeroBits (M.paramLen.eval n)))
        (M.draw (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits (M.paramLen.eval n))) ρ)
        (fun i => S.snmEntry sk (decide (s.map Prod.fst = some (S.snmCt w i))) (S.snmCt w i))
        (snmSigma w) =
      realView S M.samp M.paramLen n r sk ρ (List.ofFn w) s := by
  rw [snmView_eq, realView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
  congr 3
  refine ofFn_eq_map_range _ _ fun i => ?_
  have hc : chunkAt (S.ctLen.eval n) i (List.ofFn w) = List.ofFn (S.snmCt w i) := by
    rw [snmCt_eq, ofFn_block]
  rw [hc, decide_map_ofFn, ofFn_snmEntry]

/-- **The ideal experiment's view is `idealView`:** for an output `w` and the oracle's final state
`sa`, `snmView a (M.draw … a ρ) (d_i)_i (snmSigma w) = idealView … ⟦w⟧ sa`.

**Proof sketch.** Entry `i` of `w` is the block `chunkAt (ctLen(n) + 1) i ⟦w⟧` (`ofFn_block`),
whose head is the `COPY` flag and whose tail is the ciphertext (`simEntry_fst`, `simEntry_snd`). -/
theorem snmView_idealView (M : MsgSampler) (n r sl : ℕ) (sk : List Bool) (ρ : M.samp.Coins n)
    (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool)
    (sa : Option (Fin (M.paramLen.eval n) → Bool)) :
    S.snmView (sa.getD (zeroBits (M.paramLen.eval n)))
        (M.draw (S.msgLen.eval n) n (sa.getD (zeroBits (M.paramLen.eval n))) ρ)
        (fun i => S.snmEntry sk (S.simEntry w i).1 (S.simEntry w i).2) (snmSigma w) =
      idealView S M.samp M.paramLen n r sk ρ (List.ofFn w) sa := by
  rw [snmView_eq, idealView_eq, M.draw_eq, drawWith_eq, snmSigma_eq, ofFn_natAdd_eq_drop]
  congr 3
  refine ofFn_eq_map_range _ _ fun i => ?_
  have hc : chunkAt (S.ctLen.eval n + 1) i (List.ofFn w) =
      (S.simEntry w i).1 :: List.ofFn (S.simEntry w i).2 := by
    rw [← ofFn_block, List.ofFn_succ, simEntry_fst]
    exact congrArg _ (congrArg List.ofFn (funext fun j => (simEntry_snd S w i j).symm))
  rw [hc, List.headD_cons, List.tail_cons, ofFn_snmEntry]

/-- The ideal experiment's oracle is `NMSim.histImpl` of the sampler. -/
theorem simImpl_eq_histImpl (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    S.simImpl M n ρ = histImpl S M.samp M.paramLen M.histLen M.hist n ρ := by
  funext i a s
  rw [simImpl_eq, histImpl_eq]
  dsimp only
  rw [M.histAt_eq, M.draw_eq, histWith_eq, drawWith_eq]

/-- `T2`'s query lengths at `pl = M.paramLen` are the real experiment's. -/
private theorem snmDin_eval (M : MsgSampler) (n : ℕ) :
    (fun i => (snmDin S M.paramLen i).eval n) = S.snmInLens M n := by
  funext i
  match i with
  | 0 => rw [snmDin_zero, snmInLens_zero]
  | 1 => rw [snmDin_one, snmInLens_one]

/-- `T2`'s answer lengths at `hl = M.histLen` are the real experiment's. -/
private theorem snmDout_eval (M : MsgSampler) (n : ℕ) :
    (fun i => (snmDout S M.histLen i).eval n) = S.snmOutLens M n := by
  funext i
  match i with
  | 0 => rw [snmDout_zero, snmOutLens_zero, PolyExpr.eval_add, PolyExpr.eval_const]
  | 1 => rw [snmDout_one, snmOutLens_one, PolyExpr.eval_add]

/-- **The real experiment's acceptance rate on T2's lengths:**
`accept (snmReal atk M A q r sl X n) =
NMSim.realAcc S atk M.samp M.paramLen M.histLen M.hist A q r sl X n`.

**Proof sketch.** Transport `A`'s run (`expect_simulate_castImpl_toCompOn`, `castImpl_snmImpl`)
and read the view (`snmView_realView`). -/
theorem accept_snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (X : NUPPT)
    (n : ℕ) :
    accept (S.snmReal atk M A q r sl X n) =
      realAcc S atk M.samp M.paramLen M.histLen M.hist A q r sl X n := by
  rw [accept_eq, snmReal_eq, realAcc_eq, ProbComp.prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rA => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rX => ?_)
  rw [ProbComp.prob_bind, ← castImpl_snmImpl S atk M n _ _ ρ ρ]
  have hG : (fun res : (Fin (r * S.ctLen.eval n + sl) → Bool) × S.SnmState M n =>
      ProbComp.prob (.pure (X.distinguisherL n
        (S.snmView ((res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n)))
          (M.draw (S.msgLen.eval n) n ((res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n))) ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
            (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
          (snmSigma res.1)) rX)) (· = true)) =
      fun res => (fun p : List Bool × S.SnmState M n =>
        if X.distinguisherL n (realView S M.samp M.paramLen n r (pairSndD (S.gen.runAt n [] rg)) ρ
          p.1 p.2) rX = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [ProbComp.prob_pure, snmView_realView]
  exact (congrArg (ProbComp.expect _) hG).trans
    (expect_simulate_castImpl_toCompOn (snmDin_eval S M n) (snmDout_eval S M n)
      (rfl : r * S.ctLen.eval n + sl = r * S.ctLen.eval n + sl)
      (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ) A n q
      (pairFstD (S.gen.runAt n [] rg)) rA none fun p : List Bool × S.SnmState M n =>
        if X.distinguisherL n (realView S M.samp M.paramLen n r (pairSndD (S.gen.runAt n [] rg)) ρ
          p.1 p.2) rX = true then (1 : ℝ) else 0).symm

/-- **The ideal experiment's acceptance rate on T2's lengths:**
`accept (snmIdeal M Sim r sl X n) =
NMSim.idealAcc S M.samp M.paramLen M.histLen M.hist Sim r sl X n`.

**Proof sketch.** `simImpl_eq_histImpl`, and read the view (`snmView_idealView`). -/
theorem accept_snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) :
    accept (S.snmIdeal M Sim r sl X n) =
      idealAcc S M.samp M.paramLen M.histLen M.hist Sim r sl X n := by
  rw [accept_eq, snmIdeal_eq, idealAcc_eq, ProbComp.prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rS => ?_)
  rw [ProbComp.prob_bind]
  refine congrArg _ (funext fun rX => ?_)
  rw [ProbComp.prob_bind, simImpl_eq_histImpl]
  refine congrArg (ProbComp.expect _) (funext fun res => ?_)
  rw [ProbComp.prob_pure]
  dsimp only
  rw [snmView_idealView]

end Transport

/-! ### Definition 173.7 and Theorem 174.8 -/

/-- **Simulation-based non-malleability** [PS10, Definition 173.7], in the form SIM-NME′ of
[PSV07, Definition 1] at one message, under the attack `atk`: for every sampler `M` (with its
history function), every non-uniform PPT adversary `A`, every polynomial query budget `q`,
number `r` of output ciphertexts and length `sl` of `σ`, there is a non-uniform PPT simulator
whose ideal experiment every non-uniform PPT distinguisher tells from `A`'s real one with
negligible advantage. -/
def SimNMSecure (atk : Attack) : Prop :=
  ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
        (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n

/-- Simulation-based non-malleability holds exactly when, for every sampler, adversary and
polynomial budgets, one simulator makes every distinguisher's real/ideal advantage negligible
[PS10, Definition 173.7; PSV07, Definition 1]. -/
theorem SimNMSecure_iff (atk : Attack) :
    S.SimNMSecure atk ↔
      ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
        ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
          advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
            (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n := Iff.rfl

/-- The bound of SIM ⇒ IND: if `2·R₁ − R₂ = a − b`, `2·I₁ = I₂`, `|R₁ − I₁| ≤ e₁` and
`|R₂ − I₂| ≤ e₂`, then `|b − a| ≤ 2·e₁ + e₂`. -/
private theorem abs_le_of_gap {a b R₁ I₁ R₂ I₂ e₁ e₂ : ℝ} (hr : 2 * R₁ - R₂ = a - b)
    (hi : 2 * I₁ = I₂) (h₁ : |R₁ - I₁| ≤ e₁) (h₂ : |R₂ - I₂| ≤ e₂) : |b - a| ≤ 2 * e₁ + e₂ := by
  have hab : b - a = -(2 * (R₁ - I₁) - (R₂ - I₂)) := by linarith
  rw [hab, abs_neg]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_two]
  linarith

/-- **Theorem 174.8, (relation-based ⇒ indistinguishability-based), for every attack**
[PSV07, Corollary 1, at one message]: SIM-NME′ implies Definition 172.6.

**Proof sketch** (the maintainer's route; [PSV07] defers its proof).
1. Fix an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`. Take the
   sampler `M = NMSim.halfSamp S`: its parameter is `⟨m₀, m₁⟩` (`paramLen = msgLen + msgLen`), it
   outputs `m_β` for its single coin `β`, and its history is empty (`histLen = 0`). The SIM
   adversary `A'` is T2's machine of `NMSim.simHandler S ℓ`: it forwards `A`'s `Dec` and challenge
   queries and outputs `A`'s ciphertexts (`r = ℓ`, `sl = 0`). Take `Sim` from `h M A' Q ℓ 0`, with
   `Q = q·perCall + finCall` T2's budget.
2. `D' = NMSim.tailDist S D` outputs `0` when `m₀ = m₁`, and otherwise whether `D`'s verdict on the
   entries without their `COPY` flags (so a copy reads as `nmDecrypt`'s `⊥`) equals `[m = m₁]`;
   `D'' = NMSim.halfDist S` tests `m₀ ≠ m₁`.
3. **Real** (`NMSim.real_gap`). With the coin `β` fixed, the real experiment's oracles are those of
   `NM_β` (`castImpl_snmImpl`, `NMSim.castImpl_indImpl_abs`), and the unflagged entries are
   `NM_β`'s output. While `m₀ = m₁` the two coins give the same run (`NMSim.expect_runB_good`). So
   `2·Pr_real[D' = 1] − Pr_real[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`.
4. **Ideal** (`NMSim.ideal_gap`). With the empty history the simulator's oracle ignores `β`
   (`NMSim.histImpl_coins`), and `m = m_β` makes exactly one coin satisfy `D'` when `m₀ ≠ m₁`:
   `2·Pr_ideal[D' = 1] = Pr_ideal[D'' = 1]`.
5. Hence `NM`'s advantage is at most `2·adv(D') + adv(D'')`, negligible (`accept_snmReal_eq`,
   `accept_snmIdeal_eq` read both experiments on T2's lengths). -/
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  rw [S.NMSecure_iff]
  intro A q ℓ D
  obtain ⟨A', hA'⟩ := exists_interactiveHandlerMachine A q (NMSim.snmDin S (S.msgLen.add S.msgLen))
    (NMSim.snmDout S (.const 0)) (NMSim.snmDin S (S.msgLen.add S.msgLen))
    (NMSim.snmDout S (.const 0)) (ℓ.mul S.ctLen) (NMSim.simHandler S ℓ)
  obtain ⟨Sim, hSim⟩ := h ⟨NMSim.halfSamp S, S.msgLen.add S.msgLen, fun _ => [], .const 0,
      polyTimeComputable_const []⟩ A'
    ((q.mul (NMSim.simHandler S ℓ).perCall).add (NMSim.simHandler S ℓ).finCall) ℓ (.const 0)
  obtain ⟨ε₁, hε₁, h₁⟩ := hSim (NMSim.tailDist S D)
  obtain ⟨ε₂, hε₂, h₂⟩ := hSim (NMSim.halfDist S)
  refine ⟨fun n => 2 * ε₁ n + ε₂ n, (hε₁.const_mul 2).add hε₂, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hA' n
  have hK : ((q.mul (NMSim.simHandler S ℓ).perCall).add (NMSim.simHandler S ℓ).finCall).eval n =
      q.eval n * (NMSim.simHandler S ℓ).perCall.eval n + (NMSim.simHandler S ℓ).finCall.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have e₁ := h₁ n
  have e₂ := h₂ n
  rw [advantage_eq, accept_snmReal_eq, accept_snmIdeal_eq] at e₁ e₂
  rw [advantage_eq]
  exact abs_le_of_gap (NMSim.real_gap S atk A A' q ℓ _ D n hK φ hφ)
    (NMSim.ideal_gap S Sim D (ℓ.eval n) n) e₁ e₂

/-- **Theorem 174.8, (indistinguishability-based ⇒ relation-based), under CPA** [PSV07,
Theorem 3, at one message]: Definition 172.6 implies SIM-NME′ under a chosen-plaintext attack.
(Under CCA1 and CCA2 it does not, [PSV07, Theorem 4].)

**Proof sketch** (the maintainer's route; [PSV07] defers its proof). Fix `M`, `A`, `q`, `r`, `sl`.
1. **The hybrids.** `H_b` (`NMSim.hybAcc`) runs `A` against the oracle `NMSim.rImpl … b …` (under
   CPA `Dec` answers `⊥`, `snmImpl_dec_cpa`): on the first challenge `a` it answers
   `⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩` for the sampler's coins `ρ₀ = ρ` and an independent `ρ₁`, and
   the view is `(a, M(a; ρ), (d_i)_i, σ)` with `d_i = COPY` iff `c_i` is the challenge. `H_false` is
   the real experiment (`castImpl_snmImpl`, `NMSim.realAcc_eq_hybAcc`).
2. **The simulator** (`NMSim.exists_simulator`) runs `A` on `pk`, answering `Dec` with `⊥`. On `A`'s
   first challenge `a` it makes its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own
   coins and `M`'s advice (hard-wired, `exists_withAdviceOn`), and answers `⟨Enc_pk(m̃), h(m)⟩`;
   repeated challenges get the recorded answer. It outputs `A`'s ciphertexts, each flagged `COPY`
   iff it equals its dummy challenge, and `σ`; if `A` never asks it never queries. Its run at
   budget `1` is its run at T2's budget (`NMSim.toCompOn_budget_eq`; it asks at most one query,
   `NMSim.chalHandler_costBoundedBy`), and against the history oracle it is `H_true`.
3. **The NM adversary** `B` (`NMSim.exists_nmAdversary`) runs `A`; on `a` it draws `m, m̃ ← M(a)`,
   asks its challenge on `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)` and answers `A` with `⟨y, h(m)⟩`. It
   outputs each of `A`'s ciphertexts followed by the pair
   `Enc_pk(f^{msgLen})`, `Enc_pk((¬f)^{msgLen})`
   for its copy flag `f = [c_i = y]`, then the same pair for each bit `x` of `a`, `m` and `σ`. By
   correctness the two plaintexts of a pair differ, so at most one of the pair is the challenge,
   and the distinguisher `NMSim.recDist` reads `x` back (`NMCCA2.guessBit`) and runs `D` on the
   view. When `msgLen(n) > 0`, `NM_b` accepts with the probability of `H_b`.
4. Hence at every `n` the SIM advantage is `B`'s NM advantage, or `0` when `msgLen(n) = 0` (the two
   hybrids coincide, `NMSim.hybAcc_true_eq_false`): it is negligible. -/
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  intro M A q r sl
  obtain ⟨Sim, hSim⟩ := NMSim.exists_simulator S M.samp M.paramLen M.histLen M.hist A q r sl
  obtain ⟨B, qB, hB⟩ := NMSim.exists_nmAdversary S M.samp M.paramLen M.histLen M.hist
    M.hist_poly r sl A q
  refine ⟨Sim, fun D => ?_⟩
  obtain ⟨ε, hε, hεn⟩ := (S.NMSecure_iff .cpa).1 h B qB (NMSim.nmLen S M.paramLen r sl)
    (NMSim.recDist S M.paramLen r D)
  refine ⟨ε, hε, fun n => ?_⟩
  have h₀ := hεn n
  rw [advantage_eq] at h₀
  rw [advantage_eq, accept_snmReal_eq, accept_snmIdeal_eq, hSim, NMSim.realAcc_eq_hybAcc]
  by_cases hL : S.msgLen.eval n = 0
  · rw [NMSim.hybAcc_true_eq_false S .cpa M.samp M.paramLen M.histLen M.hist A (q.eval n) (r.eval n)
      (sl.eval n) D n hL, sub_self, abs_zero]
    exact (abs_nonneg _).trans h₀
  · rwa [← hB D n false (Nat.pos_of_ne_zero hL), ← hB D n true (Nat.pos_of_ne_zero hL)]

/-- **Theorem 174.8 under CPA** [PS10, Theorem 174.8; PSV07, Theorem 3, at one message]:
non-malleability (Definition 172.6) and simulation-based non-malleability (Definition 173.7, as
SIM-NME′) coincide under a chosen-plaintext attack. -/
theorem simNMSecure_cpa_iff_nmSecure_cpa : S.SimNMSecure .cpa ↔ S.NMSecure .cpa :=
  ⟨S.nmSecure_of_simNMSecure .cpa, S.simNMSecure_of_nmSecure_cpa⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Generic.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic tools for Theorem 174.8

Three generic facts used by both directions of [PS10, Theorem 174.8]. None of them is specific
to encryption.

* **Budget reduction** (`buildComp_budget_eq`, `toCompOn_budget_eq`). A machine's computation at
  budget `K ≥ j` that makes at most `j` queries on every path is its computation at budget `j`.
  The simulator of the ideal experiment runs at budget `1`, while T2 builds it at a polynomial
  budget.
* **One-shot coins drawn in advance** (`expect_simulate_eager`). An implementation that samples
  coins `t` at most once, on the call that leaves the "unused" states, has the law of the
  implementations with `t` fixed in advance, averaged over `t`.
* **Chunk maps** (`chunkMap`). A polynomial-time map applied to the consecutive fixed-length
  chunks of a string, concatenated (`polyTimeComputable_chunkMap`, `chunkMap_flatten`). The
  machines of both reductions read and write their tuples of ciphertexts and entries this way.

## Main definitions

* `NMSim.chunkStep`, `NMSim.chunkEmit`, `NMSim.chunkMap`.

## Main results

* `NMSim.buildComp_budget_eq`, `NMSim.toCompOn_budget_eq`.
* `NMSim.expect_toCompOn_outLen`: a machine's output length may be changed along an equality.
* `NMSim.expect_congr_of_allOutputs`, `NMSim.expect_expect_sample`,
  `NMSim.bind_congr_of_allOutputs`.
* `NMSim.expect_simulate_eager`.
* `NMSim.expect_eq_until_bad`: equal until bad, for functions of the final state.
* `NMSim.polyTimeComputable_chunkMap`, `NMSim.chunkMap_flatten`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Budget reduction -/

section Budget

variable {ι α : Type} {spec : OracleSpec ι}

/-- **Budget reduction for `buildComp`.** If the computation of `next` at budget `K` from the log
`hist` makes at most `j ≤ K` queries on every path, it is the computation at budget `j`:
`buildComp next t j hist = buildComp next t K hist`.

**Proof sketch.** Induction on `j`. A final output is the same at every budget. A query at budget
`K` costs `1 ≤ j`, so `j = j' + 1` and `K = K' + 1`; both computations ask the same query and
continue with the same log, at budgets `j'` and `K' ≥ j'`, and the continuation makes at most `j'`
queries. At `j = 0` a query is impossible unless `K = 0`, where both give `timeout`. -/
theorem buildComp_budget_eq (next : QueryLog spec → Move spec α) (t : α) :
    ∀ (j K : ℕ) (hist : QueryLog spec), j ≤ K →
      (buildComp next t K hist).CostBoundedBy (fun _ => 1) j →
      buildComp next t j hist = buildComp next t K hist := by
  intro j
  induction j with
  | zero =>
    intro K hist _ hc
    cases h : next hist with
    | ret a =>
      cases K with
      | zero => rfl
      | succ K => rw [buildComp_zero_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      cases K with
      | zero => rfl
      | succ K =>
        rw [buildComp_succ_of_query h, OracleComp.costBoundedBy_query] at hc
        exact absurd hc.1 (by omega)
  | succ j ih =>
    intro K hist hK hc
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    cases h : next hist with
    | ret a => rw [buildComp_succ_of_ret h, buildComp_succ_of_ret h]
    | query i x =>
      rw [buildComp_succ_of_query h] at hc ⊢
      rw [buildComp_succ_of_query h]
      rw [OracleComp.costBoundedBy_query] at hc
      congr 1
      funext y
      exact ih K _ (by omega) (by simpa using hc.2 y)

/-- **Budget reduction for a machine:** if `D`'s computation on `x` at budget `K ≥ j` makes at
most `j` queries on every path, it is `D`'s computation at budget `j`. -/
theorem toCompOn_budget_eq (D : NUPPT) {β : Type} (codec : MachineCodec spec β) (n j K : ℕ)
    (x : List Bool) (r : D.Coins n) (hjK : j ≤ K)
    (hc : (D.toCompOn codec n K x r).CostBoundedBy (fun _ => 1) j) :
    D.toCompOn codec n j x r = D.toCompOn codec n K x r := by
  rw [NUPPT.toCompOn_eq] at hc ⊢
  rw [NUPPT.toCompOn_eq]
  exact buildComp_budget_eq _ _ j K [] hjK hc

end Budget

/-! ### Expectations on the possible outputs -/

section Expect

variable {α β : Type}

/-- Two functions that agree on every possible output have the same expectation. -/
theorem expect_congr_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a = g a) : ProbComp.expect c f = ProbComp.expect c g :=
  le_antisymm (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).le)
    (ProbComp.expect_mono_of_allOutputs hc fun a ha => (h a ha).ge)

/-- **Fubini for a uniform sample:** `𝔼_c[𝔼_{t ← T}[h a t]] = 𝔼_{t ← T}[𝔼_c[h a t]]`. -/
theorem expect_expect_sample (c : ProbComp α) (T : Type) [Fintype T] [Nonempty T]
    (h : α → T → ℝ) :
    ProbComp.expect c (fun a => ProbComp.expect (ProbComp.sample T) (h a)) =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect c fun a => h a t := by
  simp only [ProbComp.expect_sample]
  rw [ProbComp.expect_const_mul, ProbComp.expect_sum]

/-- Two continuations that agree on every possible output give the same computation:
`c.bind f = c.bind g` when `f a = g a` whenever `P a`, and `c.AllOutputs P`. -/
theorem bind_congr_of_allOutputs {ι : Type} {spec : OracleSpec ι} {c : OracleComp spec α}
    {P : α → Prop} (hc : c.AllOutputs P) {f g : α → OracleComp spec β}
    (h : ∀ a, P a → f a = g a) : c.bind f = c.bind g := by
  induction c with
  | pure a =>
    rw [OracleComp.pure_bind, OracleComp.pure_bind]
    exact h a (OracleComp.allOutputs_pure.1 hc)
  | query i x k ih =>
    rw [OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    exact ih y (OracleComp.allOutputs_query.1 hc y)

end Expect

/-- **Changing a machine's output length along `d = d'`** keeps the law of its output read as a
list: `𝔼[G (⟦p.1⟧, p.2)]` over the runs through `bitCodec ins outs d` and `bitCodec ins outs d'`
agree. -/
theorem expect_toCompOn_outLen {k : ℕ} {ins outs : Fin k → ℕ} {σ : Type}
    (O : QueryImpl (bitSpec ins outs) σ unifSpec) (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (s : σ) {d d' : ℕ} (hd : d = d') (G : List Bool × σ → ℝ) :
    ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d) n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) =
      ProbComp.expect (simulate O (A.toCompOn (bitCodec ins outs d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  subst hd
  rfl

/-! ### One-shot coins drawn in advance -/

section Eager

variable {ι σ α T : Type} {spec : OracleSpec ι} [Fintype T] [Nonempty T]

/-- From a used state, an implementation that agrees with `O` there simulates like `O`. -/
private theorem simulate_eq_of_used (O O' : QueryImpl spec σ unifSpec) (used : σ → Prop)
    (hused : ∀ i x s, used s → O' i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (c : OracleComp spec α) {s : σ} (hs : used s) : simulate O' c s = simulate O c s := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, hused i x s hs]
    exact bind_congr_of_allOutputs (hstick i x s hs) fun p hp => ih p.1 hp

/-- **One-shot coins drawn in advance.** Let `O` be an implementation and `OE t` its variants with
coins `t ∈ T` fixed in advance, and let `used` mark the states after the coins are spent:
- from a used state, `OE t` is `O`, and `O` keeps the state used;
- from an unused state, a call either does not use the coins (`OE t` is `O` for every `t`, and the
  state stays unused), or it is the one that spends them (`O` samples `t` and runs `OE t`, and
  every successor is used).

Then from an unused state, `O`'s simulation has the law of `OE t`'s, averaged over `t`:
`𝔼[G(simulate O c s)] = 𝔼_{t ← T} 𝔼[G(simulate (OE t) c s)]`.

**Proof sketch.** Induction on `c`. From used states the two simulations coincide
(`simulate_eq_of_used`). At a query from an unused state: in the first case, rewrite the call,
apply the induction hypothesis at the (unused) successors and exchange the expectations
(`expect_expect_sample`); in the second, expand `O`'s sample and conclude from the coincidence at
the (used) successors. -/
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, ProbComp.expect_pure]
    exact (ProbComp.expect_const _ _).symm
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    rcases hfresh i x s hs with h | ⟨h, hu⟩
    · have hO : ∀ t, OE t i x s = O i x s := fun t => (h t).1
      have hun : (O i x s).AllOutputs fun p => ¬ used p.2 :=
        (h (Classical.arbitrary T)).2
      simp only [hO]
      rw [expect_congr_of_allOutputs hun fun p hp => ih p.1 hp, expect_expect_sample]
    · rw [h, ProbComp.expect_bind]
      refine congrArg _ (funext fun t => ?_)
      refine expect_congr_of_allOutputs (hu t) fun p hp => ?_
      rw [simulate_eq_of_used O (OE t) used (hused t) hstick _ hp]

end Eager

/-! ### Equal until bad, for functions of the final state -/

section UntilBad

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- **Equal until bad, in expectation, for functions of the output and the final state.** Let two
implementations give, from every good state, the same law to good successors, and let each keep
bad states bad. Then from a good state, for every function `G` of the output and the final state,
`𝔼[G · 1_{good}]` is the same under both simulations. This generalizes `prob_eq_until_bad`
(`Games/Hopping.lean`), whose events read only the output.

**Proof sketch.** Induction on the computation. From a bad successor the continuation's value is
`0` on both sides (`simulate_allOutputs_bad`); from a good one the two values agree by induction;
so both expectations only see the values at good successors, which `hagree` equates. -/
theorem expect_eq_until_bad {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
    [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ bad s) :
    ProbComp.expect (simulate impl₀ c s) (fun r => if bad r.2 then 0 else G r) =
      ProbComp.expect (simulate impl₁ c s) (fun r => if bad r.2 then 0 else G r) := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    simp only [simulate_query, ProbComp.expect_bind]
    have hz : ∀ (impl : QueryImpl spec σ unifSpec),
        (∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2) →
        ∀ ys : spec.rng i × σ, bad ys.2 →
          ProbComp.expect (simulate impl (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
            0 := by
      intro impl hst ys hb
      rw [expect_congr_of_allOutputs (simulate_allOutputs_bad bad hst _ hb)
        (g := fun _ => 0) fun r hr => if_pos hr, ProbComp.expect_const]
    have h0 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₀ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₀ hstick₀ ys hb]
      · rw [if_neg hb, ih ys.1 hb]
    have h1 : ∀ ys : spec.rng i × σ,
        ProbComp.expect (simulate impl₁ (k ys.1) ys.2) (fun r => if bad r.2 then 0 else G r) =
          if bad ys.2 then 0 else
            ProbComp.expect (simulate impl₁ (k ys.1) ys.2)
              (fun r => if bad r.2 then 0 else G r) := by
      intro ys
      by_cases hb : bad ys.2
      · rw [if_pos hb, hz impl₁ hstick₁ ys hb]
      · rw [if_neg hb]
    rw [funext h0, hagree i x s hs, ← funext h1]

end UntilBad

/-! ### Chunk maps -/

section Chunks

/-- One step of a chunk map on `⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: drop the first `c(n)` bits of `w`:
`chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
def chunkStep (c : PolyExpr) (x : List Bool) : List Bool :=
  pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkStep c x = ⟨fst x, (snd x).drop c(|fst (fst x)|)⟩`. -/
theorem chunkStep_eq (c : PolyExpr) (x : List Bool) :
    chunkStep c x =
      pairEncode (pairFstD x) ((pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- The emission of a chunk map on `⟨ctx, w⟩`: nothing on `w = []`, and `f ctx` of the first
`c(n)` bits of `w` otherwise. -/
def chunkEmit (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    List Bool :=
  if decide (pairSndD x = []) then []
  else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length))

/-- `chunkEmit c f x = if snd x = [] then [] else f (fst x) ((snd x).take c(|fst (fst x)|))`. -/
theorem chunkEmit_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkEmit c f x = if decide (pairSndD x = []) then []
      else f (pairFstD x) ((pairSndD x).take (c.eval (pairFstD (pairFstD x)).length)) :=
  rfl

/-- **The chunk map** of `f` with chunk length `c`, on `x = ⟨ctx, w⟩` with `ctx = ⟨1^n, _⟩`: the
concatenation of `f ctx` over the consecutive `c(n)`-bit chunks of `w`, computed by `|x| + 1`
rounds of `chunkStep`: `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i =>
chunkEmit c f (chunkStep c)^[i] x`. -/
def chunkMap (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x)

/-- `chunkMap c f x = (List.range (|x| + 1)).flatMap fun i => chunkEmit c f (chunkStep c)^[i] x`. -/
theorem chunkMap_eq (c : PolyExpr) (f : List Bool → List Bool → List Bool) (x : List Bool) :
    chunkMap c f x =
      (List.range (x.length + 1)).flatMap fun i => chunkEmit c f ((chunkStep c)^[i] x) :=
  rfl

/-- One step never makes a word longer than `max |x| 2` (a malformed word becomes `⟨[], []⟩`). -/
private theorem length_chunkStep_le (c : PolyExpr) (x : List Bool) :
    (chunkStep c x).length ≤ max x.length 2 := by
  rw [chunkStep_eq, length_pairEncode, List.length_drop]
  by_cases h : pairDecode x = none
  · rw [pairFstD_of_pairDecode_eq_none h, pairSndD_of_pairDecode_eq_none h]
    simp only [List.length_nil]
    omega
  · obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists'.1 h
    rw [eq_pairEncode_of_pairDecode x a b hab, pairFstD_pairEncode, pairSndD_pairEncode,
      length_pairEncode]
    omega

/-- The iterated step keeps words within `|x| + 2` bits. -/
private theorem length_iterate_chunkStep_le (c : PolyExpr) (x : List Bool) (i : ℕ) :
    ((chunkStep c)^[i] x).length ≤ x.length + 2 := by
  suffices h : ((chunkStep c)^[i] x).length ≤ max x.length 2 by omega
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_chunkStep_le c _).trans (max_le ih (le_max_right _ _))

/-- **Chunk maps are polynomial-time** when `f` is, read as a function of `⟨ctx, chunk⟩`
(`Complexity.polyTimeComputable_iterateEmit` with the step `chunkStep`, which never lengthens a
word, and `|x|` rounds).

**Proof sketch.** The step (keep `ctx`, drop `c(n)` bits) and the emission (`[]` on an empty
rest, else `f ctx` of the next `c(n)` bits) are polynomial-time by the pair readers,
`pairTakePoly`/`pairDropPoly` and `polyTimeComputable_ite`. The iterates stay within `|x| + 2`
bits (`length_iterate_chunkStep_le`), so `polyTimeComputable_iterateEmit` gives `chunkMap_eq`. -/
theorem polyTimeComputable_chunkMap (c : PolyExpr) {f : List Bool → List Bool → List Bool}
    (hf : PolyTimeComputable fun z => f (pairFstD z) (pairSndD z)) :
    PolyTimeComputable (chunkMap c f) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun x : List Bool =>
      pairEncode (pairFstD (pairFstD x)) (pairSndD x) := (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).drop (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairDropPoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun x : List Bool =>
      (pairSndD x).take (c.eval (pairFstD (pairFstD x)).length) :=
    ((polyTimeComputable_pairTakePoly c).comp hcut).congr fun x => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hstep : PolyTimeComputable (chunkStep c) := hF.pairEncode hdrop
  have hemit : PolyTimeComputable (chunkEmit c f) :=
    polyTimeComputable_ite (polyTimeComputable_isNil.comp hD) (polyTimeComputable_const [])
      ((hf.comp (hF.pairEncode htake)).congr fun x => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
  exact (polyTimeComputable_iterateEmit hstep hemit .var (.add .var (.const 2))
    (fun x i _ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      exact length_iterate_chunkStep_le c x i)).congr
    fun x => by rw [PolyExpr.eval_var, chunkMap_eq]

/-- Reading the suffixes of a list within at least its length many steps (DL-30–36 overlap: the
general form of `Forward`'s private `flatMap_range_drop`, with the reading of a nonempty suffix
assumed only for the list's members). -/
private theorem flatMap_range_drop {β : Type} (F : List β → List Bool) (g : β → List Bool)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

/-- **The chunk map of a concatenation of chunks:** if every chunk has `c(n) > 0` bits, the chunk
map of `⟨⟨1^n, e⟩, chunks.flatten⟩` is the concatenation of `f ⟨1^n, e⟩` over the chunks.

**Proof sketch.** The `i`-th step leaves `(chunks.drop i).flatten` (dropping a first chunk of
`c(n)` bits), whose emission is `f` of the `i`-th chunk while chunks remain and `[]` afterwards;
there are at most `|x| + 1` chunks since each has a bit. -/
theorem chunkMap_flatten (c : PolyExpr) (f : List Bool → List Bool → List Bool) (n : ℕ)
    (e : List Bool) (chunks : List (List Bool)) (hlen : ∀ ch ∈ chunks, ch.length = c.eval n)
    (hpos : 0 < c.eval n) :
    chunkMap c f (pairEncode (pairEncode (List.replicate n true) e) chunks.flatten) =
      (chunks.map (f (pairEncode (List.replicate n true) e))).flatten := by
  set ctx := pairEncode (List.replicate n true) e
  have hit : ∀ i, (chunkStep c)^[i] (pairEncode ctx chunks.flatten) =
      pairEncode ctx (chunks.drop i).flatten := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, chunkStep_eq, pairFstD_pairEncode,
        pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, ← List.tail_drop]
      cases h : chunks.drop i with
      | nil => rw [List.flatten_nil, List.drop_nil, List.tail_nil, List.flatten_nil]
      | cons ch rest =>
        have hch : ch.length = c.eval n :=
          hlen ch (List.mem_of_mem_drop (h ▸ List.mem_cons_self))
        rw [List.flatten_cons, List.tail_cons, ← hch, List.drop_left]
  have hlen' : chunks.length ≤ (pairEncode ctx chunks.flatten).length + 1 := by
    have : chunks.length ≤ chunks.flatten.length := by
      rw [List.length_flatten]
      clear hit
      induction chunks with
      | nil => exact le_rfl
      | cons ch rest ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons]
        have := hlen ch List.mem_cons_self
        have := ih fun ch' h' => hlen ch' (List.mem_cons_of_mem _ h')
        omega
    rw [length_pairEncode]
    omega
  rw [chunkMap_eq]
  simp only [hit]
  rw [flatMap_range_drop (fun l => chunkEmit c f (pairEncode ctx l.flatten)) (f ctx)
    (by
      show chunkEmit c f (pairEncode ctx ([] : List (List Bool)).flatten) = []
      rw [List.flatten_nil, chunkEmit_eq, pairSndD_pairEncode, if_pos (decide_eq_true rfl)])
    chunks (fun ch hch t => ?_) _ hlen', List.flatMap_def]
  have hl := hlen ch hch
  have hne : ch ++ t.flatten ≠ [] := fun h => by
    rw [List.append_eq_nil_iff] at h
    rw [h.1, List.length_nil] at hl
    omega
  show chunkEmit c f (pairEncode ctx (ch :: t).flatten) = f ctx ch
  rw [chunkEmit_eq, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
    List.length_replicate, List.flatten_cons, if_neg (by simpa using hne), ← hl, List.take_left]

end Chunks

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid oracle of Theorem 174.8

The real experiment of SIM-NME′ [PSV07, Definition 1] (`Simulation.lean`) runs the adversary
against two oracles: `Dec` (per the attack) and a challenge that, on the sampler's parameter `a`,
draws `m = M(a; ρ)`, encrypts it and answers `⟨Enc_pk(m), h(m)⟩`. Both directions of
[PS10, Theorem 174.8] compare runs against variants of these oracles. This file states them
once, generically in the sampler (a machine `samp`, the parameter length `pl`, the history
function `hist` and its length `hl`), on the lengths that T2 machines use (`snmDin`, `snmDout`):

* `rImpl … b … ρ ρ' ce` encrypts `M(a; ρ)` for `b = false` and `M(a; ρ')` for `b = true`, always
  answering the history of `m = M(a; ρ)`. With `b = false` it is the real experiment's oracle; with
  `b = true` it is the hybrid in which the adversary sees an encryption of an independent draw. The
  encryption coins are sampled (`ce = none`) or given in advance (`ce = some re`).
* `histImpl` is the ideal experiment's history oracle on the same lengths.
* `realView` and `idealView` are the experiments' outputs `(a, m, (d_i)_i, σ)` as strings, read
  from the adversary's (respectively the simulator's) output string and the final state.
* `realAcc`, `idealAcc` and `hybAcc` are the acceptance rates of the real experiment, the ideal
  experiment and the hybrid `H_b`, on these lengths.

## Main definitions

* `NMSim.snmDin`, `NMSim.snmDout`: the oracle lengths as polynomials.
* `NMSim.drawWith`, `NMSim.histWith`, `NMSim.encWith`: `M(a; ρ)`, `h(m)` and `Enc_pk(m; re)`.
* `NMSim.rImpl`: the hybrid oracle; `NMSim.histImpl`: the history oracle.
* `NMSim.chunkAt`, `NMSim.entryL`, `NMSim.realView`, `NMSim.idealView`.
* `NMSim.realAcc`, `NMSim.idealAcc`, `NMSim.hybAcc`.

## Main results

* `NMSim.snmDin_eval_inLens`, `NMSim.snmDout_eval_outLens`: with `pl = 2·msgLen` and `hl = 0` the
  lengths are those of Definition 171.5.
* `NMSim.rImpl_dec`, `_some`, `_none_lazy`, `_none_eager`, `_dec_cpa`: the oracle's answers.
* `NMSim.rImpl_eq_of_msgLen_eq_zero`: with empty messages the two hybrids coincide.
* `NMSim.expect_simulate_rImpl_eager`: the encryption coins may be drawn in advance.
* `NMSim.rImpl_false_coins`, `NMSim.histImpl_coins`: coins that are not read.
* Blocks of strings: `NMSim.ofFn_block`, `ofFn_natAdd_eq_drop`, `take_eq_flatten_chunkAt`,
  `chunkAt_flatten_append`, `map_chunkAt_flatten`, and their lengths.
* `NMSim.realAcc_eq_hybAcc`, `NMSim.hybAcc_true_eq_false`: `H_false` is the real experiment, and
  the hybrids coincide when `msgLen(n) = 0`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-! ### Lengths -/

/-- The query lengths of the real experiment's oracles as polynomials: ciphertexts for `Dec`, the
sampler's parameter (`pl(n)` bits) for the challenge. -/
def snmDin (pl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.ctLen
  | 1 => pl

/-- `Dec` queries are ciphertexts: `snmDin S pl 0 = S.ctLen`. -/
theorem snmDin_zero (pl : PolyExpr) : snmDin S pl 0 = S.ctLen := rfl

/-- Challenge queries are parameters: `snmDin S pl 1 = pl`. -/
theorem snmDin_one (pl : PolyExpr) : snmDin S pl 1 = pl := rfl

/-- The answer lengths as polynomials: a flag and a message for `Dec`, a ciphertext and the
history (`hl(n)` bits) for the challenge. -/
def snmDout (hl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.msgLen.add (.const 1)
  | 1 => S.ctLen.add hl

/-- `Dec` answers a flag and a message: `snmDout S hl 0 = msgLen + 1`. -/
theorem snmDout_zero (hl : PolyExpr) : snmDout S hl 0 = S.msgLen.add (.const 1) := rfl

/-- The challenge answers a ciphertext and the history: `snmDout S hl 1 = ctLen + hl`. -/
theorem snmDout_one (hl : PolyExpr) : snmDout S hl 1 = S.ctLen.add hl := rfl

/-- With the parameter `⟨m₀, m₁⟩` (`pl = msgLen + msgLen`) the query lengths are those of
Definition 171.5: `(snmDin S (msgLen + msgLen) ·).eval n = S.inLens n`. -/
theorem snmDin_eval_inLens (n : ℕ) :
    (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) = S.inLens n := by
  funext i
  match i with
  | 0 => rw [snmDin_zero, S.inLens_zero]
  | 1 => rw [snmDin_one, PolyExpr.eval_add, S.inLens_one]

/-- With an empty history (`hl = 0`) the answer lengths are those of Definition 171.5:
`(snmDout S 0 ·).eval n = S.outLens n`. -/
theorem snmDout_eval_outLens (n : ℕ) :
    (fun i => (snmDout S (.const 0) i).eval n) = S.outLens n := by
  funext i
  match i with
  | 0 => rw [snmDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
  | 1 => rw [snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const, Nat.add_zero, S.outLens_one]

/-! ### Draws, histories and encryptions -/

/-- The message `M(a; ρ)` drawn by the sampler `samp` on the parameter `a` with coins `ρ`, read at
`ℓ` bits: `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
def drawWith (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    Fin ℓ → Bool :=
  padFin ℓ (samp.runAt n (List.ofFn a) ρ)

/-- `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
theorem drawWith_eq (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)` read at `hl` bits: `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
def histWith (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) : Fin hl → Bool :=
  padFin hl (hist (List.ofFn m))

/-- `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
theorem histWith_eq (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) :
    histWith hist hl m = padFin hl (hist (List.ofFn m)) := rfl

/-- The encryption `Enc_pk(m; re)` read at `ctLen(n)` bits:
`encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
def encWith (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re)

/-- `encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
theorem encWith_eq (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    encWith S n pk m re = padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re) := rfl

/-! ### The hybrid oracle -/

/-- **The hybrid oracle** at parameter `n`, for the keys `pk`, `sk`, the sampler `samp` (parameter
length `pl`, history `hist` of length `hl`) and its coins `ρ`, `ρ'`, on T2's lengths
(`snmDin`, `snmDout`); the state is the challenge with its parameter, once asked.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not
  the challenge, and `⊥` (all `false`) otherwise.
- The challenge on the parameter `a`, the first time: `m = M(a; ρ)`; it encrypts `M(a; ρ)` for
  `b = false` and `M(a; ρ')` for `b = true`, with coins sampled (`ce = none`) or given (`ce = some
  re`), answers `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats `⟨y, h(M(a₀; ρ))⟩` for the
  recorded `(y, a₀)`. -/
noncomputable def rImpl (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n)
      (Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
      .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
    else .pure (zeroBits _, s)
  | 1, _, some (y, a) =>
    .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
      (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a))
  | 1, x, none =>
    match ce with
    | some re =>
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x)))
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
            List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
              (padFin (pl.eval n) (List.ofFn x)) ρ))),
          some (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re,
            padFin (pl.eval n) (List.ofFn x)))

section Readers

variable (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
  (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
  (ce : Option (S.enc.Coins n))

/-- **Decryption** as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when open and not the recorded
challenge, `⊥` otherwise; the state is kept. -/
theorem rImpl_dec (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome &&
          !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
        .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
      else .pure (zeroBits _, s) := rfl

/-- **Under CPA, `Dec` answers `⊥`** and keeps the state. -/
theorem rImpl_dec_cpa (b : Bool) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S .cpa b samp pl hl hist n pk sk ρ ρ' ce 0 c s = .pure (zeroBits _, s) := by
  rw [rImpl_dec, FixedLengthScheme.decOpen_cpa, Bool.false_and, if_neg Bool.false_ne_true]

/-- **A repeated challenge** answers `⟨y, h(M(a₀; ρ))⟩` for the recorded `(y, a₀)` and keeps the
state. -/
theorem rImpl_some (x : Fin ((snmDin S pl 1).eval n) → Bool) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
        (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a)) := rfl

/-- **A first challenge with coins drawn in advance:** on `x` (read as the parameter `a`) it
answers `⟨Enc_pk(M(a; ρ_b); re), h(M(a; ρ))⟩` and records the ciphertext with `a`. -/
theorem rImpl_none_eager (x : Fin ((snmDin S pl 1).eval n) → Bool) (re : S.enc.Coins n) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none =
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x))) := rfl

/-- **A first challenge with sampled coins** samples `re` and answers as with `re` in advance. -/
theorem rImpl_none_lazy (x : Fin ((snmDin S pl 1).eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' none 1 x none =
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none := rfl

/-- Decryption does not read the encryption coins. -/
theorem rImpl_dec_ce (ce' : Option (S.enc.Coins n)) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 0 c s := rfl

/-- A repeated challenge does not read the encryption coins. -/
theorem rImpl_some_ce (ce' : Option (S.enc.Coins n)) (x : Fin ((snmDin S pl 1).eval n) → Bool)
    (y : Fin (S.ctLen.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 1 x (some (y, a)) := rfl

end Readers

/-- Every call keeps a recorded state recorded: from `some _`, every successor is `some _`. -/
theorem rImpl_allOutputs_isSome (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (i : Fin 2) (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (hs : s.isSome) :
    (rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce i x s).AllOutputs fun p => p.2.isSome := by
  obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
  match i with
  | 0 =>
    rw [rImpl_dec]
    split <;> exact OracleComp.allOutputs_pure.2 rfl
  | 1 => exact OracleComp.allOutputs_pure.2 rfl

/-- **The encryption coins may be drawn in advance:** for every computation `c` and function `G`,
the run against the hybrid oracle with sampled coins has the law of the runs with coins `re`
drawn in advance, averaged over `re` (`expect_simulate_eager`; the coins are spent at the first
challenge). -/
theorem expect_simulate_rImpl_eager (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (G : α × Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) → ℝ) :
    ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' none) c none) G =
      ProbComp.expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re)) c none)
          G := by
  refine expect_simulate_eager _ _ (fun s => s.isSome = true) (fun re i x s hs => ?_)
    (fun i x s hs => rImpl_allOutputs_isSome S atk b samp pl hl hist n pk sk ρ ρ' none i x s hs)
    (fun i x s hs => ?_) c G (by simp)
  · obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
    match i with
    | 0 => exact rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x _
    | 1 => exact rImpl_some_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x y a
  · have hs' : s = none := by simpa using hs
    subst hs'
    match i with
    | 0 =>
      refine Or.inl fun re => ⟨rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' _ _ x none, ?_⟩
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 (by simp)
    | 1 =>
      refine Or.inr ⟨rImpl_none_lazy S atk b samp pl hl hist n pk sk ρ ρ' x, fun re => ?_⟩
      rw [rImpl_none_eager]
      exact OracleComp.allOutputs_pure.2 rfl

/-- **With empty messages the two hybrids coincide:** if `msgLen(n) = 0`, then the oracle encrypting
`M(a; ρ')` is the one encrypting `M(a; ρ)` (both draws are the empty message). -/
theorem rImpl_eq_of_msgLen_eq_zero (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (h : S.msgLen.eval n = 0) :
    rImpl S atk true samp pl hl hist n pk sk ρ ρ' ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ' ce := by
  have hsub : ∀ {k : ℕ} (a : Fin k → Bool),
      drawWith samp (S.msgLen.eval n) n a ρ' = drawWith samp (S.msgLen.eval n) n a ρ := by
    intro k a
    funext j
    have := j.isLt
    omega
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none =>
    cases ce with
    | some re => rw [rImpl_none_eager, rImpl_none_eager, if_pos rfl, if_neg Bool.false_ne_true,
        hsub]
    | none =>
      rw [rImpl_none_lazy, rImpl_none_lazy]
      simp only [rImpl_none_eager, Bool.false_eq_true, ↓reduceIte, hsub]

/-- **With `b = false` the hybrid does not read `ρ'`:** the oracles for `ρ₁` and `ρ₂` coincide. -/
theorem rImpl_false_coins (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ₁ ρ₂ : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    rImpl S atk false samp pl hl hist n pk sk ρ ρ₁ ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ₂ ce := by
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none => cases ce <;> rfl

/-! ### The history oracle -/

/-- **The ideal experiment's oracle** on T2's lengths (`pl(n)`-bit queries, `hl(n)`-bit answers):
on the parameter `a` (the first one asked, recorded) it answers `h(M(a; ρ))`. -/
noncomputable def histImpl (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (n : ℕ) (ρ : samp.Coins n) :
    QueryImpl (bitSpecAt (fun _ : Fin 1 => pl) (fun _ => hl) n) (Option (Fin (pl.eval n) → Bool))
      unifSpec :=
  fun _ a s => .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
    some (s.getD a))

/-- `histImpl … ρ i a s = pure (h(M(s.getD a; ρ)), some (s.getD a))`. -/
theorem histImpl_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ : samp.Coins n) (i : Fin 1) (a : Fin (pl.eval n) → Bool)
    (s : Option (Fin (pl.eval n) → Bool)) :
    histImpl S samp pl hl hist n ρ i a s =
      .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
        some (s.getD a)) := rfl

/-- **With an empty history the oracle ignores the sampler's coins:** if `hl(n) = 0`, then
`histImpl … ρ = histImpl … ρ'`. -/
theorem histImpl_coins (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ ρ' : samp.Coins n) (h : hl.eval n = 0) :
    histImpl S samp pl hl hist n ρ = histImpl S samp pl hl hist n ρ' := by
  funext i a s
  rw [histImpl_eq, histImpl_eq]
  have hv : histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ) =
      histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ') := by
    funext j
    have := j.isLt
    omega
  rw [hv]

/-! ### Blocks of fixed-length strings -/

/-- Block `i` of `k` bits of a string: `chunkAt k i w = (w.drop (i·k)).take k`. -/
def chunkAt (k i : ℕ) (w : List Bool) : List Bool := (w.drop (i * k)).take k

/-- `chunkAt k i w = (w.drop (i·k)).take k`. -/
theorem chunkAt_eq (k i : ℕ) (w : List Bool) : chunkAt k i w = (w.drop (i * k)).take k := rfl

/-- A block inside the string has `k` bits: `|chunkAt k i w| = k` when `(i + 1)·k ≤ |w|`. -/
theorem length_chunkAt (k i : ℕ) (w : List Bool) (h : (i + 1) * k ≤ w.length) :
    (chunkAt k i w).length = k := by
  rw [chunkAt_eq, List.length_take, List.length_drop, Nat.succ_mul] at *
  omega

/-- **The first `r` blocks:** `w.take (r·k) = (chunkAt k 0 w ++ ⋯ ++ chunkAt k (r-1) w)`. -/
theorem take_eq_flatten_chunkAt (k r : ℕ) (w : List Bool) :
    w.take (r * k) = ((List.range r).map fun i => chunkAt k i w).flatten := by
  induction r with
  | zero => rw [Nat.zero_mul, List.take_zero, List.range_zero, List.map_nil, List.flatten_nil]
  | succ r ih =>
    rw [Nat.succ_mul, List.take_add, ih, List.range_succ, List.map_append, List.flatten_append,
      List.map_singleton, List.flatten_singleton, chunkAt_eq]

/-- `r` blocks of `k` bits have `r·k` bits. -/
theorem length_flatten_map_range (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k) :
    ((List.range r).map g).flatten.length = r * k := by
  induction r with
  | zero => rw [List.range_zero, List.map_nil, List.flatten_nil, List.length_nil, Nat.zero_mul]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      ih fun i hi => hg i (by omega), List.map_singleton, List.flatten_singleton,
      hg r (by omega), Nat.succ_mul]

/-- Blocks of `k` bits, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` bits. -/
theorem length_flatten_map_const {α β : Type} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  induction l with
  | nil => rw [List.map_nil, List.flatten_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | cons x t ih => rw [List.map_cons, List.flatten_cons, List.length_append, ih, hg,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- **Reading back the blocks:** if `g 0, …, g (r-1)` have `k` bits each, block `i < r` of
`g 0 ++ ⋯ ++ g (r-1) ++ t` is `g i`. -/
theorem chunkAt_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) (i : ℕ) (hi : i < r) :
    chunkAt k i (((List.range r).map g).flatten ++ t) = g i := by
  induction r generalizing t with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.append_assoc]
    by_cases h : i < r
    · exact ih (fun j hj => hg j (by omega)) _ h
    · have hir : i = r := by omega
      subst hir
      rw [chunkAt_eq, List.drop_append_of_le_length (by
          rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.drop_of_length_le (by rw [length_flatten_map_range k i g fun j hj => hg j (by omega)]),
        List.nil_append, List.take_left' (hg i (by omega))]

/-- The tail after `r` blocks of `k` bits: `(g 0 ++ ⋯ ++ g (r-1) ++ t).drop (r·k) = t`. -/
theorem drop_flatten_append (k r : ℕ) (g : ℕ → List Bool) (hg : ∀ i < r, (g i).length = k)
    (t : List Bool) : (((List.range r).map g).flatten ++ t).drop (r * k) = t :=
  List.drop_left' (length_flatten_map_range k r g hg)

/-- **The blocks of a concatenation of `k`-bit blocks:** if every block of `cs` has `k` bits,
mapping `F` over `chunkAt k i cs.flatten` for `i < |cs|` is mapping `F` over `cs`. -/
theorem map_chunkAt_flatten {α : Type} (k : ℕ) (F : List Bool → α) :
    ∀ cs : List (List Bool), (∀ c ∈ cs, c.length = k) →
      (List.range cs.length).map (fun i => F (chunkAt k i cs.flatten)) = cs.map F := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c t ih =>
    intro hc
    have hck : c.length = k := hc c List.mem_cons_self
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons,
      List.flatten_cons, ← ih fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')]
    congr 1
    · rw [chunkAt_eq, Nat.zero_mul, List.drop_zero, List.take_left' hck]
    · refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, chunkAt_eq, chunkAt_eq, Nat.succ_mul, Nat.add_comm,
        ← List.drop_drop, List.drop_left' hck]

/-- **Block `i` of a string of `r` blocks of `k` bits and a tail:**
`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = chunkAt k i ⟦w⟧`. -/
theorem ofFn_block {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      chunkAt k i (List.ofFn w) := by
  have hle : (i : ℕ) * k + k ≤ r * k := by
    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  rw [chunkAt_eq]
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [Fin.coe_castAdd, finProdFinEquiv_apply_val]
    show j + k * i = i * k + j
    rw [Nat.mul_comm]
    omega

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k`. -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for `i < r`, then
`List.ofFn f = (List.range r).map g`. -/
theorem ofFn_eq_map_range {α : Type} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)`. -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-! ### The experiments' outputs as strings -/

/-- **An entry `d_i` as a string:** `COPY` (`true` followed by `msgLen(n) + 1` falses) if `copy`,
and `false` followed by `Dec`'s answer on the ciphertext `c` otherwise. -/
def entryL (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) : List Bool :=
  if copy then true :: List.replicate (S.msgLen.eval n + 1) false
  else false :: List.ofFn (FixedLengthScheme.decAnswer
    (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c))))

/-- `entryL S n sk copy c =
if copy then true :: 0^{msgLen + 1} else false :: ⟦decAnswer (Dec_sk c)⟧`. -/
theorem entryL_eq (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    entryL S n sk copy c = if copy then true :: List.replicate (S.msgLen.eval n + 1) false
      else false :: List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := rfl

/-- An entry has `msgLen(n) + 2` bits. -/
theorem length_entryL (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    (entryL S n sk copy c).length = S.msgLen.eval n + 2 := by
  rw [entryL_eq]
  cases copy
  · rw [if_neg Bool.false_ne_true, List.length_cons, List.length_ofFn]
  · rw [if_pos rfl, List.length_cons, List.length_replicate]

/-- **The real experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the adversary's output
string `w` (`r` ciphertexts, then `σ`) and the final state `s`: `a` is the recorded parameter
(`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when ciphertext `i` is the recorded
challenge. -/
def realView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    List Bool :=
  List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
      (chunkAt (S.ctLen.eval n) i w)).flatten ++
    w.drop (r * S.ctLen.eval n)

/-- `realView … w s = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem realView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    realView S samp pl n r sk ρ w s =
      List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
          (chunkAt (S.ctLen.eval n) i w)).flatten ++
        w.drop (r * S.ctLen.eval n) := rfl

/-- **The ideal experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the simulator's output
string `w` (`r` entries of a flag and a ciphertext, then `σ`) and the history oracle's state `sa`:
`a` is the recorded parameter (`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when entry
`i` is flagged. -/
def idealView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) : List Bool :=
  List.ofFn (sa.getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
      (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
    w.drop (r * (S.ctLen.eval n + 1))

/-- `idealView … w sa = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem idealView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) :
    idealView S samp pl n r sk ρ w sa =
      List.ofFn (sa.getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
          (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
        w.drop (r * (S.ctLen.eval n + 1)) := rfl

/-! ### The acceptance rates of the experiments -/

/-- **The real experiment's acceptance rate** for the sampler `samp` (parameter length `pl`,
history `hist` of length `hl`), the adversary `A` (budget `q`, `r` ciphertexts and an `sl`-bit `σ`)
and the distinguisher `X`, on T2's lengths: over the keys and the coins of the sampler, `A` and
`X`, the probability that `X` accepts `realView` of `A`'s run against `rImpl … false … ρ ρ none`. -/
noncomputable def realAcc (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
    (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
      (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `realAcc … = 𝔼_{rg, ρ, rA, rX} 𝔼[1{X accepts realView}]` over `A`'s run against `rImpl`. -/
theorem realAcc_eq (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    realAcc S atk samp pl hl hist A q r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n
          (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The ideal experiment's acceptance rate** for the sampler `samp` (as in `realAcc`), the
simulator `Sim` (budget `1`, `r` entries and an `sl`-bit `σ`) and the distinguisher `X`: over the
keys and the coins of the sampler, `Sim` and `X`, the probability that `X` accepts `idealView` of
`Sim`'s run against `histImpl … ρ`. -/
noncomputable def idealAcc (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
    (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
      (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
    if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `idealAcc … = 𝔼_{rg, ρ, rS, rX} 𝔼[1{X accepts idealView}]` over `Sim`'s run against
`histImpl`. -/
theorem idealAcc_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) :
    idealAcc S samp pl hl hist Sim r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
        if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The hybrid experiments' acceptance rate** `H_b` for the sampler `samp` (as in `realAcc`), the
adversary `A` (budget `q`, `r` ciphertexts and an `sl`-bit `σ`) and the distinguisher `X`: over the
keys, the sampler's coins `ρ`, `ρ'` and the coins of `A` and `X`, the probability that `X` accepts
`realView` of `A`'s run against `rImpl … b … ρ ρ' none`. `H_false` is the real experiment
(`realAcc_eq_hybAcc`). -/
noncomputable def hybAcc (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ' =>
  ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
    (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
      (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `hybAcc … b … = 𝔼_{rg, ρ, ρ', rA, rX} 𝔼[1{X accepts realView}]` over `A`'s run against
`rImpl … b … ρ ρ' none`. -/
theorem hybAcc_eq (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    hybAcc S atk b samp pl hl hist A q r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ' =>
      ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The real experiment is the hybrid `H_false`:** `realAcc … = hybAcc … false …` (with
`b = false` the oracle does not read `ρ'`, `rImpl_false_coins`). -/
theorem realAcc_eq_hybAcc (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    realAcc S atk samp pl hl hist A q r sl X n =
      hybAcc S atk false samp pl hl hist A q r sl X n := by
  rw [realAcc_eq, hybAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  refine (ProbComp.expect_const (ProbComp.sample (samp.Coins n)) _).symm.trans
    (congrArg _ (funext fun ρ' => ?_))
  rw [rImpl_false_coins S atk samp pl hl hist n _ _ ρ ρ ρ']

/-- **With empty messages the two hybrids coincide:** if `msgLen(n) = 0`, then
`hybAcc … true … = hybAcc … false …` (`rImpl_eq_of_msgLen_eq_zero`). -/
theorem hybAcc_true_eq_false (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ)
    (h : S.msgLen.eval n = 0) :
    hybAcc S atk true samp pl hl hist A q r sl X n =
      hybAcc S atk false samp pl hl hist A q r sl X n := by
  simp only [hybAcc_eq, rImpl_eq_of_msgLen_eq_zero S atk samp pl hl hist n _ _ _ _ none h]

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIM-NME′ implies non-malleability: the sampler and the games

Direction SIM ⇒ IND of [PS10, Theorem 174.8] ([PSV07, Corollary 1], at one message). An NM
adversary `A` asks a challenge `⟨m₀, m₁⟩` and outputs ciphertexts. The SIM adversary forwards
`A`'s queries, with the sampler `halfSamp S` whose parameter is `⟨m₀, m₁⟩` and which outputs `m_β`
for its single coin `β` (with the empty history). With the coin `β` fixed, the real experiment's
oracles are those of `Ind_β` (`castImpl_indImpl_abs`), so the experiment `NM_β` is the hybrid
oracle's run with the coin `β` (`accept_nmGame_eq_rImpl`).

## Main definitions

* `NMSim.halfSamp`: the sampler `⟨m₀, m₁⟩ ↦ m_β`; `NMSim.halfCoins`: its coins are one bit.
* `NMSim.copyHandler`: the SIM adversary's handler (forwarding, output `A`'s output).
* `NMSim.halfDist` (`D''`), `NMSim.entryTails`, `NMSim.tailDist` (`D'`): the distinguishers.
* `NMSim.runB`: `A`'s run against the hybrid oracle with coin `β`.

## Main results

* `NMSim.halfSamp_runAt`, `NMSim.ofFn_drawWith_half`, `NMSim.expect_sample_halfCoins`.
* `NMSim.castImpl_indImpl_abs`: the CCA oracles of `Ind_β` are the hybrid oracle with coin `β`.
* `NMSim.accept_nmGame_eq_rImpl`: `NM_β` as a run against the hybrid oracle.
* `NMSim.simulate_copyHandler_machine`: the SIM adversary's run is `A`'s.
* `NMSim.tailDist_blocks`, `NMSim.halfDist_blocks`, `NMSim.nmOutput_eq_entryTails`: the
  distinguishers on the views.
* `NMSim.real_identity`, `NMSim.ideal_identity`: the identities behind the two gaps.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1 and Corollary 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim
open AdaptiveCPA (castImpl castImpl_eq ofFn_cast ofFn_splitHalf_fst ofFn_splitHalf_snd
  padFin_ofFn_zeroBits expect_simulate_castImpl_toCompOn simulate_eq_of_abs)

variable (S : FixedLengthPKScheme)

/-! ### The sampler `⟨m₀, m₁⟩ ↦ m_β` -/

/-- The sampler's raw function on `⟨⟨⟨1^n, a⟩, α⟩, ρ⟩`: the second half of `a` (from position
`msgLen(n)`) if the first coin is `1`, the first `msgLen(n)` bits otherwise. -/
private def halfFun (z : List Bool) : List Bool :=
  if (NUPPT.inCoins z).headD false then
    (NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)
  else (NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length)

/-- The sampler's raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFun : PolyTimeComputable (halfFun S) := by
  have hpa := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp NUPPT.polyTimeComputable_inCoins)
    (((polyTimeComputable_pairDropPoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    (((polyTimeComputable_pairTakePoly S.msgLen).comp hpa).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The sampler `⟨m₀, m₁⟩ ↦ m_β`**: the uniform machine with one coin `β` that outputs, on the
parameter `a = m₀ ‖ m₁`, its first `msgLen(n)` bits for `β = 0` and the rest for `β = 1`. -/
noncomputable def halfSamp : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1)

/-- The sampler on `y` with coins `ρ` outputs `y.drop msgLen(n)` if `ρ`'s first bit is `1` and
`y.take msgLen(n)` otherwise. -/
theorem halfSamp_runAt (n : ℕ) (y : List Bool) (ρ : (halfSamp S).Coins n) :
    (halfSamp S).runAt n y ρ =
      if (List.ofFn ρ).headD false then y.drop (S.msgLen.eval n) else y.take (S.msgLen.eval n) := by
  have hrun : ∀ y r, (halfSamp S).runAtL n y r =
      halfFun S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n y r
  rw [NUPPT.runAt_eq, hrun, halfFun, NUPPT.inCoins_eq, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- A one-bit string is constant: for `k = 1`, `v = fun _ => ⟦v⟧.headD false`. -/
private theorem eq_const_headD {k : ℕ} (hk : k = 1) (v : Fin k → Bool) :
    v = fun _ => (List.ofFn v).headD false := by
  subst hk
  funext j
  rw [List.ofFn_succ, List.headD_cons, Subsingleton.elim j 0]

/-- **The sampler's coins are one bit:** `(halfSamp S).Coins n ≃ Bool`, reading the first bit. -/
noncomputable def halfCoins (n : ℕ) : (halfSamp S).Coins n ≃ Bool where
  toFun ρ := (List.ofFn ρ).headD false
  invFun β := (NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n).symm
    fun _ => β
  left_inv ρ := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    have hρ : (List.ofFn ρ).headD false = (List.ofFn (e ρ)).headD false := by
      rw [NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    show e.symm (fun _ => (List.ofFn ρ).headD false) = ρ
    rw [hρ, ← eq_const_headD h1 (e ρ), Equiv.symm_apply_apply]
  right_inv β := by
    set e := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_halfFun S) (.const 1) n
    have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
    show (List.ofFn (e.symm fun _ => β)).headD false = β
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn (polyTimeComputable_halfFun S) (.const 1) n,
      Equiv.apply_symm_apply, List.ofFn_const, h1, List.replicate_one, List.headD_cons]

/-- The bijection reads the first coin bit: `halfCoins S n ρ = ⟦ρ⟧.headD false`. -/
theorem halfCoins_apply (n : ℕ) (ρ : (halfSamp S).Coins n) :
    halfCoins S n ρ = (List.ofFn ρ).headD false := rfl

/-- The coin of `β` has first bit `β`: `⟦(halfCoins S n).symm β⟧.headD false = β`. -/
theorem headD_ofFn_halfCoins_symm (n : ℕ) (β : Bool) :
    (List.ofFn ((halfCoins S n).symm β)).headD false = β :=
  (halfCoins S n).apply_symm_apply β

/-- **The sampler's draw with coin `β`:** for a parameter of `2 · msgLen(n)` bits,
`⟦M(a; β)⟧ = if β then ⟦a⟧.drop msgLen(n) else ⟦a⟧.take msgLen(n)`. -/
theorem ofFn_drawWith_half (n : ℕ) {k : ℕ} (a : Fin k → Bool)
    (hk : k = S.msgLen.eval n + S.msgLen.eval n) (β : Bool) :
    List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n a ((halfCoins S n).symm β)) =
      if β then (List.ofFn a).drop (S.msgLen.eval n) else (List.ofFn a).take (S.msgLen.eval n) := by
  rw [drawWith_eq, halfSamp_runAt, headD_ofFn_halfCoins_symm]
  refine GGMRed.ofFn_padFin_of_length ?_
  cases β <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_take, List.length_drop,
    List.length_ofFn] <;> omega

/-- **Averaging over the sampler's coins** is averaging over `β`:
`𝔼_ρ[g ρ] = (g (coin 0) + g (coin 1)) / 2`. -/
theorem expect_sample_halfCoins (n : ℕ) (g : (halfSamp S).Coins n → ℝ) :
    expect (sample ((halfSamp S).Coins n)) g =
      (g ((halfCoins S n).symm false) + g ((halfCoins S n).symm true)) / 2 := by
  rw [← expect_sample_equiv (halfCoins S n).symm, expect_sample, Fintype.sum_bool,
    Fintype.card_bool]
  ring

/-! ### `Ind_β` is the hybrid oracle with coin `β` -/

/-- **The CCA oracles of `Ind_β` are the hybrid oracle with the sampler's coin `β`** (on T2's
lengths
with `pl = 2 · msgLen`, `hl = 0`), once the hybrid's state forgets the recorded parameter:
`castImpl (Ind_β) i x (s.map fst) =
(rImpl … (coin β) … i x s).bind fun p => pure (p.1, p.2.map fst)`.

**Proof sketch.** `Dec`: the same availability, refusal and decryption (`indImpl_dec_onSpec_cast`,
`rImpl_dec`), the casts keeping the strings (`ofFn_cast`). A repeated challenge repeats the record
with the empty history. A first challenge encrypts `m_β`, which is the sampler's draw with coin `β`
(`ofFn_drawWith_half`, `ofFn_splitHalf_fst/_snd`). -/
theorem castImpl_indImpl_abs (atk : Attack) (β : Bool) (n : ℕ) (pk sk : List Bool)
    (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
      (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :
    castImpl (ins := fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
        (outs := fun i => (snmDout S (.const 0) i).eval n) (S.indImpl atk β n pk sk) i x
        (s.map Prod.fst) =
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).bind fun p => .pure (p.1, p.2.map Prod.fst) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hd0 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 0 = S.ctLen.eval n := by
    show (snmDin S _ 0).eval n = _
    rw [snmDin_zero]
  have hd1 : (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) 1 =
      (S.msgLen.add S.msgLen).eval n := by
    show (snmDin S _ 1).eval n = _
    rw [snmDin_one]
  match i, x with
  | 0, x =>
    have hc : cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)) =
        padFin (S.ctLen.eval n) (List.ofFn x) := by
      apply List.ofFn_injective
      rw [ofFn_cast (S.inLens_zero n),
        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0, S.inLens_zero]),
        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])]
    have hx : List.ofFn (padFin (S.ctLen.eval n) (List.ofFn x)) = List.ofFn x :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd0])
    rw [castImpl_eq, S.indImpl_dec_onSpec_cast, rImpl_dec, hc, Option.isSome_map, hx]
    by_cases hcond : (FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin (S.ctLen.eval n) (List.ofFn x)))) = true
    · rw [if_pos hcond, if_pos hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_zero n).symm]
    · rw [if_neg hcond, if_neg hcond, OracleComp.pure_bind, OracleComp.pure_bind]
      dsimp only
      rw [padFin_ofFn_zeroBits]
  | 1, x =>
    have hh : ∀ {ℓ : ℕ} (m : Fin ℓ → Bool),
        List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
    cases s with
    | some ya =>
      obtain ⟨y, a⟩ := ya
      rw [Option.map_some, castImpl_eq, S.indImpl_challenge_repeat_onSpec, OracleComp.pure_bind,
        rImpl_some, OracleComp.pure_bind]
      dsimp only
      rw [ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]
    | none =>
      rw [Option.map_none, castImpl_eq, S.indImpl_challenge_none_onSpec, rImpl_none_lazy,
        OracleComp.bind_assoc, OracleComp.bind_assoc]
      refine congrArg _ (funext fun re => ?_)
      rw [OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind]
      dsimp only
      have hdraw : List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm β)) =
          List.ofFn (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
              (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1) := by
        have hx : List.ofFn (cast (S.indSpec_challengeDom n)
            (padFin (S.inLens n 1) (List.ofFn x))) =
            List.ofFn (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) := by
          rw [ofFn_cast (S.inLens_one n),
            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1, hpl, S.inLens_one]),
            GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hd1])]
        rw [ofFn_drawWith_half S n _ hpl]
        cases β
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx]
        · rw [if_pos rfl, if_pos rfl, ofFn_splitHalf_snd, hx]
      have he : encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x))
          (if false = true then ρ' else (halfCoins S n).symm β)) re =
          padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
            (if β then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n)
              (padFin (S.inLens n 1) (List.ofFn x)))).2 else (FixedLengthScheme.splitHalf
                (cast (S.indSpec_challengeDom n)
                  (padFin (S.inLens n 1) (List.ofFn x)))).1))) re) := by
        rw [if_neg Bool.false_ne_true, encWith_eq, hdraw]
      rw [he, ofFn_cast (S.outLens_one n).symm, hh, List.append_nil, Option.map_some]

/-- **`NM_β` is the hybrid run with the sampler's coin `β`:** the experiment of Definition 172.6
for `A` (budget `q`, `ℓ` ciphertexts) and `D` accepts with the expectation, over the keys, `A`'s
coins and `D`'s coins, of `D`'s verdict on `nmOutput sk (s.map fst) ⟦a⟧` for the run of `A` (on
T2's lengths) against the hybrid oracle with coin `β`, its output `a` and final state `s`.

**Proof sketch.** Transport `A`'s run to T2's lengths (`nmCodec_eq_bitCodec`,
`expect_simulate_castImpl_toCompOn` with `snmDin_eval_inLens`, `snmDout_eval_outLens`) and pass to
the hybrid oracle through the state abstraction `s ↦ s.map fst` (`simulate_eq_of_abs`,
`castImpl_indImpl_abs`). -/
theorem accept_nmGame_eq_rImpl (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (β : Bool)
    (n : ℕ) (hist : List Bool → List Bool) (ρ' : (halfSamp S).Coins n) :
    accept (S.nmGame atk A q ℓ D β n) =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (A.Coins n)) fun r =>
      expect (sample (D.Coins n)) fun rD =>
        expect (simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n
            (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
            ((halfCoins S n).symm β) ρ' none)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
            (pairFstD (S.gen.runAt n [] rg)) r) none)
          fun p => if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
            (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true
            then 1 else 0 := by
  rw [accept_eq, S.nmGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun rD => ?_)
  have h2 : (fun res : (Fin (ℓ * S.ctLen.eval n) → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) rD)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, S.nmCodec_eq_bitCodec, h2]
  refine (expect_simulate_castImpl_toCompOn (snmDin_eval_inLens S n) (snmDout_eval_outLens S n)
    rfl (S.indImpl atk β n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))) A n q
    _ r none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ * S.ctLen.eval n) p.1)) rD = true then (1 : ℝ) else 0)).symm.trans ?_
  have habs := simulate_eq_of_abs _ _ (Option.map Prod.fst)
    (fun i x s => castImpl_indImpl_abs S atk β n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) hist ρ' i x s)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none
  rw [Option.map_none] at habs
  rw [habs, expect_bind]
  simp only [expect_pure]

/-! ### The SIM adversary -/

open NMCCA2 (fwdHandler fwdHandler_finRun fwdHandler_finCall fwdHandler_advIn
  simulate_fwdHandler_impl fields_finInput polyTimeComputable_finFields finA)

/-- The SIM adversary's finalization round: output the adversary's output, `⟨[true], a⟩`. -/
private def copyFin (w : List Bool) : List Bool := pairEncode [true] (finA w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_copyFin : PolyTimeComputable copyFin :=
  (polyTimeComputable_const [true]).pairEncode polyTimeComputable_finFields.2.2.2.1

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_copyAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The SIM adversary's handler** (on the real experiment's oracles with parameter length `pl`
and history length `hl`): it forwards every query (`NMCCA2.fwdHandler`), runs the adversary on the
reduction input, asks nothing in finalization, and outputs the adversary's `outLen(n)`-bit
output. -/
def copyHandler (pl hl outLen : PolyExpr) :
    InteractiveHandler 2 (snmDin S pl) (snmDout S hl) 2 (snmDin S pl) (snmDout S hl) :=
  fwdHandler (snmDin S pl) (snmDout S hl) (.const 0) (fun ctx => pairFstD (pairSndD ctx))
    polyTimeComputable_copyAdvIn outLen (.const 0) copyFin polyTimeComputable_copyFin

/-- The adversary runs on the reduction input: `(copyHandler S pl hl outLen).advInput n z ω = z`. -/
theorem copyHandler_advInput (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) :
    (copyHandler S pl hl outLen).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [copyHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The SIM adversary outputs `outLen(n)` bits: `(copyHandler S pl hl outLen).outLen = outLen`. -/
theorem copyHandler_outLen (pl hl outLen : PolyExpr) :
    (copyHandler S pl hl outLen).outLen = outLen := by
  rw [copyHandler, NMCCA2.fwdHandler_outLen]

/-- **The handler forwards** (`simulate_fwdHandler_impl`). -/
theorem simulate_copyHandler_impl (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) :
    simulate ((copyHandler S pl hl outLen).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (snmDin S pl) (snmDout S hl) (.const 0) _ polyTimeComputable_copyAdvIn
    outLen (.const 0) copyFin polyTimeComputable_copyFin n z ω c s

/-- **The finalization outputs the adversary's output** (of `outLen(n)` bits), asking nothing:
`H.finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem copyHandler_finish (pl hl outLen : PolyExpr) (n : ℕ) (z : List Bool)
    (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (s : Fin ((copyHandler S pl hl outLen).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (hd : d = outLen.eval n) :
    (copyHandler S pl hl outLen).finish n z ω s a =
      .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) := by
  have hfin : (copyHandler S pl hl outLen).finRun = copyFin := by
    funext w
    rw [copyHandler, fwdHandler_finRun]
  have hfc : (copyHandler S pl hl outLen).finCall = .const 0 := by
    rw [copyHandler, fwdHandler_finCall]
  have hol := copyHandler_outLen S pl hl outLen
  rw [InteractiveHandler.finish_eq, hfc, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ ((copyHandler S pl hl outLen).finRun _) = _
  rw [hfin, copyFin, (fields_finInput _ _ _ _ _ _).2.2.2.1]
  have hw : List.ofFn (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn a)) =
      List.ofFn a := GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hol, hd])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-- **The SIM adversary's run is the adversary's run.** Let `B` be T2's machine for
`copyHandler S pl hl outLen` (coin bijection `φ`). Against any oracle `O` and from any state `s₀`,
`B`'s run on `pk` with coins `φ (ω, r)` is `A`'s run on `pk` with coins `r`, its output read at
`outLen(n)` bits. -/
theorem simulate_copyHandler_machine (A B : NUPPT) (q dα pl hl outLen : PolyExpr) (n : ℕ)
    (hd : dα.eval n = outLen.eval n)
    (φ : (Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((copyHandler S pl hl outLen).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (dα.eval n)) n (q.eval n) ((copyHandler S pl hl outLen).advInput n z ω) r)
          ((copyHandler S pl hl outLen).init n)).bind
          (fun res => (copyHandler S pl hl outLen).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n) (fun j => (snmDout S hl j).eval n)
          ((copyHandler S pl hl outLen).outLen.eval n)) n
          (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
            (copyHandler S pl hl outLen).finCall.eval n) z (φ (ω, r)))
    {σ : Type} (O : QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n) σ unifSpec) (s₀ : σ)
    (pk : List Bool) (ω : Fin ((copyHandler S pl hl outLen).seedLen.eval n) → Bool)
    (r : A.Coins n) :
    simulate O (B.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n)
        (fun j => (snmDout S hl j).eval n) ((copyHandler S pl hl outLen).outLen.eval n)) n
        (q.eval n * (copyHandler S pl hl outLen).perCall.eval n +
          (copyHandler S pl hl outLen).finCall.eval n) pk (φ (ω, r))) s₀ =
      (simulate O (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n)
          (fun i => (snmDout S hl i).eval n) (dα.eval n)) n (q.eval n) pk r) s₀).bind fun p =>
        .pure (padFin ((copyHandler S pl hl outLen).outLen.eval n) (List.ofFn p.1), p.2) := by
  rw [← hφ, copyHandler_advInput, simulate_copyHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, copyHandler_finish S pl hl outLen n pk ω _ _ hd]
  rw [simulate_bind]
  simp only [simulate_pure]

/-! ### The distinguishers -/

/-- `z ↦ (g z).take msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_takeMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).take (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairTakePoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `z ↦ (g z).drop msgLen(|1^n|)` for the parameter slot `1^n` of a machine input. -/
private theorem polyTimeComputable_dropMsg {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => (g z).drop (S.msgLen.eval (NUPPT.inParam z).length) :=
  ((polyTimeComputable_pairDropPoly S.msgLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `D''`'s raw function: on the view `y`, whether its first two `msgLen(n)`-bit blocks differ. -/
private def halfFunD (z : List Bool) : List Bool :=
  [!decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
    ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
      (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D''`'s raw function is polynomial-time. -/
private theorem polyTimeComputable_halfFunD : PolyTimeComputable (halfFunD S) :=
  polyTimeComputable_not ((polyTimeComputable_pairEq.comp
    ((polyTimeComputable_takeMsg S NUPPT.polyTimeComputable_inArg).pairEncode
      (polyTimeComputable_takeMsg S (polyTimeComputable_dropMsg S
        NUPPT.polyTimeComputable_inArg)))).congr fun z => by
          simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])

/-- **The distinguisher `D''`:** the uniform machine without coins accepting a view whose
parameter `⟨m₀, m₁⟩` (its first `2 · msgLen(n)` bits) has `m₀ ≠ m₁`. -/
noncomputable def halfDist : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0)

/-- `D''` accepts `y` iff its first two `msgLen(n)`-bit blocks differ:
`(halfDist S).distinguisherL n y ρ = !decide (y.take L = (y.drop L).take L)`. -/
theorem halfDist_distinguisherL (n : ℕ) (y : List Bool) (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n y ρ =
      !decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) := by
  have hrun : ∀ y r, (halfDist S).runAtL n y r =
      halfFunD S (pairEncode (pairEncode (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform (polyTimeComputable_halfFunD S) (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, halfFunD, NUPPT.inArg_eq, NUPPT.inParam_eq,
    NUPPT.advInput_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  cases decide (y.take (S.msgLen.eval n) = (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) <;>
    decide

/-- The tails of the entries: each `msgLen(n) + 2`-bit chunk without its first bit (the `COPY`
flag), on `⟨⟨1^n, []⟩, entries⟩`. -/
def entryTails : List Bool → List Bool :=
  chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1

/-- `entryTails S = chunkMap (msgLen + 2) (fun _ ch => ch.drop 1)`. -/
theorem entryTails_eq : entryTails S = chunkMap (S.msgLen.add (.const 2)) fun _ ch => ch.drop 1 :=
  rfl

/-- The tails of the entries are polynomial-time. -/
theorem polyTimeComputable_entryTails : PolyTimeComputable (entryTails S) :=
  polyTimeComputable_chunkMap _ (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

variable (D : NUPPT)

/-- `D'`'s raw function on `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with the view `y = a₀ ‖ a₁ ‖ m ‖ entries`
(`msgLen(n)` bits each for `a₀`, `a₁`, `m`): `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict
(advice `α`, coins `ρ`) on the entries' tails equals `[m = a₁]`. -/
private def tailFun (z : List Bool) : List Bool :=
  if decide ((NUPPT.inArg z).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length)) then [false]
  else [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (entryTails S (pairEncode (pairEncode (NUPPT.inParam z) [])
        ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
          (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)) = [true]) ==
    decide ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).take (S.msgLen.eval (NUPPT.inParam z).length) =
      ((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).take
        (S.msgLen.eval (NUPPT.inParam z).length))]

/-- `D'`'s raw function is polynomial-time.

**Proof sketch.** `a₀`, `a₁`, `m` and the entries are `take`/`drop`s of `msgLen(n)` bits of the
view (`polyTimeComputable_takeMsg`, `polyTimeComputable_dropMsg`), the tails are
`polyTimeComputable_entryTails`, `D`'s verdict is `D.output` on `layout`, and the equality tests
use `polyTimeComputable_pairEq`. The outer test is `polyTimeComputable_ite`, and `[v == w]` is
the `ite` on `v` of `[w]` and `[!w]`. -/
private theorem polyTimeComputable_tailFun : PolyTimeComputable (tailFun S D) := by
  have hy := NUPPT.polyTimeComputable_inArg
  have hu := NUPPT.polyTimeComputable_inParam
  have hd1 := polyTimeComputable_dropMsg S hy
  have hd2 := polyTimeComputable_dropMsg S hd1
  have hd3 := polyTimeComputable_dropMsg S hd2
  have ha0 := polyTimeComputable_takeMsg S hy
  have ha1 := polyTimeComputable_takeMsg S hd1
  have hm := polyTimeComputable_takeMsg S hd2
  have heq : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable fun z => [decide (f z = g z)] := fun hf hg =>
    (polyTimeComputable_pairEq.comp (hf.pairEncode hg)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hconv : PolyTimeComputable fun z => entryTails S (pairEncode (pairEncode
      (NUPPT.inParam z) []) ((((NUPPT.inArg z).drop (S.msgLen.eval (NUPPT.inParam z).length)).drop
        (S.msgLen.eval (NUPPT.inParam z).length)).drop (S.msgLen.eval (NUPPT.inParam z).length))) :=
    (polyTimeComputable_entryTails S).comp ((hu.pairEncode (polyTimeComputable_const [])).pairEncode
      hd3)
  have hv := heq (D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu hconv
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    (polyTimeComputable_const [true])
  have hw := heq hm ha1
  refine polyTimeComputable_ite (heq ha0 ha1) (polyTimeComputable_const [false]) ?_
  have key : ∀ v w : Bool, (if v = true then [w] else [!w]) = [v == w] := by decide
  exact (polyTimeComputable_ite hv hw (polyTimeComputable_not hw)).congr fun z => by
    rw [Function.comp_apply]
    exact key _ _

/-- **The distinguisher `D'`** built from `D`, with `D`'s coins and advice: on a view
`a₀ ‖ a₁ ‖ m ‖ entries` it outputs `0` if `a₀ = a₁`, and otherwise whether `D`'s verdict on the
entries' tails (the `COPY` flags dropped, so a copy reads as `⊥`) equals `[m = a₁]`. -/
noncomputable def tailDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_tailFun S D) D.coins D.adv D.advice D.advice_length

/-- `D'` has `D`'s coins. -/
theorem tailDist_coins : (tailDist S D).coins = D.coins := by
  rw [tailDist, NUPPT.coins_ofPolyTime]

/-- **`D'`'s verdict** on a view `y`, with `D`'s coins `rD` carried over: with `L = msgLen(n)`,
`0` if `y`'s first two `L`-bit blocks are equal, and otherwise `[D(entryTails (y.drop 3L)) =
[true]] == [third block = second block]`. -/
theorem tailDist_distinguisherL (n : ℕ) (y : List Bool) (rD : D.Coins n) :
    (tailDist S D).distinguisherL n y (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (y.take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
          (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).drop (S.msgLen.eval n)))) rD ==
        decide (((y.drop (S.msgLen.eval n)).drop (S.msgLen.eval n)).take (S.msgLen.eval n) =
          (y.drop (S.msgLen.eval n)).take (S.msgLen.eval n))) := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n y) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) y (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, tailDist, NUPPT.runAtL_ofPolyTime, tailFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout, List.length_replicate]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]
  split
  · rfl
  · generalize D.distinguisherL n _ rD = v
    cases v <;> simp

/-! ### The distinguishers on the views -/

/-- The four blocks of a view `A ‖ M ‖ E` with `|A| = 2L`, `|M| = L`. -/
private theorem blocks_append (L : ℕ) (A M E : List Bool) (hA : A.length = L + L)
    (hM : M.length = L) :
    (A ++ M ++ E).take L = A.take L ∧ ((A ++ M ++ E).drop L).take L = A.drop L ∧
      (((A ++ M ++ E).drop L).drop L).take L = M ∧ (((A ++ M ++ E).drop L).drop L).drop L = E := by
  have hd : (A.drop L).length = L := by rw [List.length_drop]; omega
  rw [List.append_assoc]
  refine ⟨List.take_append_of_le_length (by omega), ?_, ?_, ?_⟩
  · rw [List.drop_append_of_le_length (by omega), List.take_left' hd]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.take_left' hM]
  · rw [List.drop_append_of_le_length (by omega), List.drop_left' hd, List.drop_left' hM]

/-- **`D'` on a view `A ‖ M ‖ E`** (`|A| = 2·msgLen(n)`, `|M| = msgLen(n)`): `0` if the halves of
`A` are equal, and otherwise `[D(entryTails E) = 1] == [M = second half of A]`. -/
theorem tailDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (rD : D.Coins n) :
    (tailDist S D).distinguisherL n (A ++ M ++ E)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) =
      if decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) then false
      else (D.distinguisherL n (entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        E)) rD == decide (M = A.drop (S.msgLen.eval n))) := by
  obtain ⟨h1, h2, h3, h4⟩ := blocks_append _ A M E hA hM
  rw [tailDist_distinguisherL, h1, h2, h3, h4]

/-- **`D''` on a view `A ‖ M ‖ E`:** whether the halves of `A` differ. -/
theorem halfDist_blocks (n : ℕ) (A M E : List Bool)
    (hA : A.length = S.msgLen.eval n + S.msgLen.eval n) (hM : M.length = S.msgLen.eval n)
    (ρ : (halfDist S).Coins n) :
    (halfDist S).distinguisherL n (A ++ M ++ E) ρ =
      !decide (A.take (S.msgLen.eval n) = A.drop (S.msgLen.eval n)) := by
  obtain ⟨h1, h2, -, -⟩ := blocks_append _ A M E hA hM
  rw [halfDist_distinguisherL, h1, h2]

/-- An entry without its `COPY` flag: `⊥ = 0` for a copy, `Dec`'s answer otherwise. -/
theorem entryL_drop_one (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    (entryL S n sk copy c).drop 1 =
      if copy then List.replicate (S.msgLen.eval n + 1) false
      else List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := by
  rw [entryL_eq]
  cases copy <;> rfl

/-- **The entries' tails are the decrypted entries** (`chunkMap_flatten`; every entry has
`msgLen(n) + 2` bits). -/
theorem entryTails_entries (n : ℕ) (sk : List Bool) (es : List (Bool × List Bool)) :
    entryTails S (pairEncode (pairEncode (List.replicate n true) [])
        (es.map fun e => entryL S n sk e.1 e.2).flatten) =
      (es.map fun e => (entryL S n sk e.1 e.2).drop 1).flatten := by
  have hlen : (S.msgLen.add (.const 2)).eval n = S.msgLen.eval n + 2 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  rw [entryTails_eq, chunkMap_flatten _ _ n [] _ (fun ch hch => ?_) (by rw [hlen]; omega),
    List.map_map]
  · rfl
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hch
    rw [hlen, entryL_eq]
    cases e.1 <;> simp

/-- **The experiment's output is the entries' tails:** for an output string `w` of `ℓ` ciphertexts,
`nmOutput sk s' w` is the concatenation of the tails of the entries `entryL … [ciphertext i is
the challenge] (ciphertext i)`. -/
theorem nmOutput_eq_entryTails (n ℓ : ℕ) (sk : List Bool)
    (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (w : List Bool) (hw : w.length = ℓ * S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) w) =
      ((List.range ℓ).map fun i => (entryL S n sk
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
        (chunkAt (S.ctLen.eval n) i w)).drop 1).flatten := by
  rw [S.nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, entryL_drop_one, S.nmDecrypt_eq]
  have hc : List.ofFn (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩) = chunkAt (S.ctLen.eval n) i w := by
    rw [S.ofFn_nthCt, GGMRed.ofFn_padFin_of_length hw, chunkAt_eq]
  have hcopy : (s' = some (S.nthCt (padFin (ℓ * S.ctLen.eval n) w) ⟨i, by
      rw [List.length_ofFn] at h₁; exact h₁⟩)) ↔
      s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w) := by
    rw [← hc]
    cases s' with
    | none => simp
    | some c => simp [List.ofFn_inj]
  by_cases h : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)
  · rw [if_pos (hcopy.2 h), decide_eq_true h, if_pos rfl, ofFn_zeroBits]
  · rw [if_neg (fun h' => h (hcopy.1 h')), decide_eq_false h, if_neg Bool.false_ne_true, hc]

/-! ### The real experiment against `NM_0`, `NM_1` -/

/-- `D'`'s indicator on a view with parameter `A` and message `m_β`, as a function of `D`'s verdict
`t`: `[m₀ ≠ m₁] · [t = β]`. -/
private theorem tail_indicator (A : List Bool) (L : ℕ) (t β : Bool) :
    (if (if decide (A.take L = A.drop L) then false
      else (t == decide ((if β then A.drop L else A.take L) = A.drop L))) = true then (1 : ℝ)
      else 0) =
      if A.take L ≠ A.drop L then (if β then (if t then 1 else 0) else 1 - (if t then 1 else 0))
      else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases β <;> cases t <;> simp [hb]

/-- `D''`'s indicator on a view with parameter `A`: `[m₀ ≠ m₁]`. -/
private theorem half_indicator (A : List Bool) (L : ℕ) :
    (if (!decide (A.take L = A.drop L)) = true then (1 : ℝ) else 0) =
      if A.take L ≠ A.drop L then 1 else 0 := by
  by_cases hb : A.take L = A.drop L <;> simp [hb]

section RealIdentity

variable (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (n : ℕ) (hist : List Bool → List Bool)
  (pk sk : List Bool) (r : A.Coins n) (ρ' : (halfSamp S).Coins n)

/-- **The run of `A` against the hybrid oracle with the sampler's coin `β`** (the real experiment of
the SIM adversary, and `NM_β`): `simulate (rImpl … false … (coin β) ρ' none) (A's run) none`. -/
noncomputable abbrev runB (β : Bool) :
    ProbComp ((Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) :=
  simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
      ((halfCoins S n).symm β) ρ' none)
    (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
      (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none

/-- `runB … β = simulate (rImpl … false … (coin β) ρ' none) (A.toCompOn … n q pk r) none`. -/
theorem runB_eq (β : Bool) :
    runB S atk A q ℓ n hist pk sk r ρ' β =
      simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
          ((halfCoins S n).symm β) ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
          (fun i => (snmDout S (.const 0) i).eval n) (ℓ * S.ctLen.eval n)) n q pk r) none := rfl

/-- The bad event of the coupling: the recorded parameter `⟨m₀, m₁⟩` has `m₀ ≠ m₁` (never for the
empty state, whose parameter reads `0`). -/
private def badHalves (s : Option ((Fin (S.ctLen.eval n) → Bool) ×
    (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))) : Prop :=
  (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).take (S.msgLen.eval n) ≠
    (List.ofFn ((s.map Prod.snd).getD (zeroBits _))).drop (S.msgLen.eval n)

private instance : DecidablePred (badHalves S n) := fun _ => instDecidableNot

/-- **The coupling of the two coins:** `𝔼[G · 1_{m₀ = m₁}]` is the same with the sampler's coin
`0` and `1` (`expect_eq_until_bad`): the oracles agree while the recorded parameter has equal
halves, and a bad parameter stays recorded.

**Proof sketch.** `expect_eq_until_bad` with the bad event `badHalves`. The empty state is good
(its parameter reads `0`, `ofFn_zeroBits`), and a recorded state stays recorded (`rImpl_dec`,
`rImpl_some`), so bad is sticky. From a good state the two oracles agree: `Dec` and repeated
challenges do not read the coin (the history is empty), and on a first challenge, after the same
encryption coins, the new state is bad on both sides or `m₀ = m₁` and the two draws coincide
(`ofFn_drawWith_half`). -/
private theorem expect_runB_good (G : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) → ℝ) :
    expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else G p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true)
        (fun p => if badHalves S n p.2 then 0 else G p) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hh : ∀ {ℓ' : ℕ} (m : Fin ℓ' → Bool),
      List.ofFn (histWith hist ((PolyExpr.const 0).eval n) m) = [] := fun m =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
  have hnone : ¬ badHalves S n none := by
    unfold badHalves
    intro h
    apply h
    rw [Option.map_none, Option.getD_none, ofFn_zeroBits, hpl, List.take_replicate,
      List.drop_replicate]
    congr 1
    omega
  have hkeep : ∀ (β : Bool) i x y a,
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x (some (y, a))).AllOutputs
        fun ys => ys.2 = some (y, a) := by
    intro β i x y a
    match i with
    | 0 =>
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 rfl
    | 1 =>
      rw [rImpl_some]
      exact OracleComp.allOutputs_pure.2 rfl
  have hstick : ∀ (β : Bool) i x s, badHalves S n s →
      (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) hist n pk sk
        ((halfCoins S n).symm β) ρ' none i x s).AllOutputs fun ys => badHalves S n ys.2 := by
    intro β i x s hs
    cases s with
    | none => exact absurd hs hnone
    | some ya => exact (hkeep β i x ya.1 ya.2).mono fun ys h => h ▸ hs
  refine expect_eq_until_bad (badHalves S n) (fun i x s hs g => ?_) (hstick false) (hstick true) _
    G hnone
  match i, s with
  | 0, s => rw [rImpl_dec, rImpl_dec]
  | 1, some (y, a) => rw [rImpl_some, rImpl_some, hh, hh]
  | 1, none =>
    rw [rImpl_none_lazy, rImpl_none_lazy, expect_bind, expect_bind]
    refine congrArg _ (funext fun re => ?_)
    rw [rImpl_none_eager, rImpl_none_eager, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      expect_pure, expect_pure]
    by_cases hb : badHalves S n (some (default, padFin ((S.msgLen.add S.msgLen).eval n)
      (List.ofFn x)))
    · have hb' : ∀ y, badHalves S n (some (y, padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x))) := fun y => hb
      dsimp only
      rw [if_pos (hb' _), if_pos (hb' _)]
    · have heq : drawWith (halfSamp S) (S.msgLen.eval n) n (padFin ((S.msgLen.add S.msgLen).eval n)
          (List.ofFn x)) ((halfCoins S n).symm false) = drawWith (halfSamp S) (S.msgLen.eval n) n
          (padFin ((S.msgLen.add S.msgLen).eval n) (List.ofFn x)) ((halfCoins S n).symm true) := by
        apply List.ofFn_injective
        rw [ofFn_drawWith_half S n _ hpl, ofFn_drawWith_half S n _ hpl, if_neg Bool.false_ne_true,
          if_pos rfl]
        simpa [badHalves] using hb
      rw [heq]

/-- **The real identity** at fixed keys and coins: for the views of the SIM adversary's real
experiment with coin `β`, `2 · avg_β 𝔼[D'] − avg_β 𝔼[D''] = 𝔼_1[D(NM)] − 𝔼_0[D(NM)]`, where the
last two are `NM_1` and `NM_0`.

**Proof sketch.** On the views, `D'` is `[m₀ ≠ m₁] · [D(NM) = β]` and `D''` is `[m₀ ≠ m₁]`
(`tailDist_blocks`, `halfDist_blocks`, `ofFn_drawWith_half`, `entryTails_entries`,
`nmOutput_eq_entryTails`). By the coupling (`expect_runB_good`) the good parts of `D(NM)` and of `1`
have the same expectation under both coins; the identity is then linear algebra. -/
theorem real_identity (D : NUPPT) (rD : D.Coins n) (ρ'' : (halfDist S).Coins n) :
    (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm false) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0) +
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
          ((halfCoins S n).symm true) (List.ofFn p.1) p.2)
          (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then 1 else 0)) -
      (expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm false) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0) +
        expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
          if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
            ((halfCoins S n).symm true) (List.ofFn p.1) p.2) ρ'' = true then 1 else 0)) / 2 =
      expect (runB S atk A q ℓ n hist pk sk r ρ' true) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p =>
        if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
          (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0) := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  set v : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ := fun p => if D.distinguisherL n (S.nmOutput sk (p.2.map Prod.fst)
        (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1))) rD = true then 1 else 0 with hv
  -- The views, block by block.
  have hview : ∀ (β : Bool) (p : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))),
      ((if (tailDist S D).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2)
        (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then (if β then v p else 1 - v p) else 0) ∧
      ((if (halfDist S).distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm β) (List.ofFn p.1) p.2) ρ'' = true then (1 : ℝ) else 0) =
        if badHalves S n p.2 then 1 else 0) := by
    intro β p
    have hw : (List.ofFn p.1).drop (ℓ * S.ctLen.eval n) = [] := by
      rw [List.drop_eq_nil_iff, List.length_ofFn]
    have hA : (List.ofFn ((p.2.map Prod.snd).getD (zeroBits _))).length =
        S.msgLen.eval n + S.msgLen.eval n := by rw [List.length_ofFn, hpl]
    have hM : (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n
        ((p.2.map Prod.snd).getD (zeroBits _)) ((halfCoins S n).symm β))).length =
        S.msgLen.eval n := List.length_ofFn
    have hes : ((List.range ℓ).map fun i => entryL S n sk
        (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
        (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))) =
        (((List.range ℓ).map fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))).map
          fun e : Bool × List Bool => entryL S n sk e.1 e.2) := by
      rw [List.map_map]
      rfl
    rw [realView_eq, hw, List.append_nil, tailDist_blocks S D n _ _ _ hA hM,
      halfDist_blocks S n _ _ _ hA hM, ofFn_drawWith_half S n _ hpl, hes, entryTails_entries,
      List.map_map]
    have hnm : ((List.range ℓ).map ((fun e : Bool × List Bool => (entryL S n sk e.1 e.2).drop 1) ∘
        fun i => Prod.mk (decide ((p.2.map Prod.fst).map List.ofFn =
          some (chunkAt (S.ctLen.eval n) i (List.ofFn p.1))))
          (chunkAt (S.ctLen.eval n) i (List.ofFn p.1)))).flatten =
        S.nmOutput sk (p.2.map Prod.fst) (padFin (ℓ * S.ctLen.eval n) (List.ofFn p.1)) := by
      rw [nmOutput_eq_entryTails S n ℓ sk _ _ List.length_ofFn, Option.map_map]
      rfl
    rw [hnm]
    exact ⟨tail_indicator _ _ _ _, half_indicator _ _⟩
  -- The coupling, for `D(NM)` and for `1`.
  have hgv := expect_runB_good S atk A q ℓ n hist pk sk r ρ' v
  have hg1 := expect_runB_good S atk A q ℓ n hist pk sk r ρ' (fun _ => 1)
  have hsplit : ∀ (β : Bool) (f : (Fin (ℓ * S.ctLen.eval n) → Bool) ×
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) →
      ℝ), expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then f p
        else 0) = expect (runB S atk A q ℓ n hist pk sk r ρ' β) f -
          expect (runB S atk A q ℓ n hist pk sk r ρ' β) (fun p => if badHalves S n p.2 then 0
            else f p) := by
    intro β f
    rw [← expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  simp only [fun β p => (hview β p).1, fun β p => (hview β p).2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsub0 : expect (runB S atk A q ℓ n hist pk sk r ρ' false) (fun p => 1 - v p) =
      1 - expect (runB S atk A q ℓ n hist pk sk r ρ' false) v := by
    rw [expect_sub, expect_const]
  have hsub0' : expect (runB S atk A q ℓ n hist pk sk r ρ' false)
      (fun p => if badHalves S n p.2 then 0 else 1 - v p) =
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else 1) -
      expect (runB S atk A q ℓ n hist pk sk r ρ' false)
        (fun p => if badHalves S n p.2 then 0 else v p) := by
    rw [← expect_sub]
    refine congrArg _ (funext fun p => ?_)
    split <;> ring
  rw [hsplit false (fun p => 1 - v p), hsplit true v, hsplit false (fun _ => 1),
    hsplit true (fun _ => 1), hsub0, hsub0', expect_const, expect_const, hgv, hg1]
  ring

end RealIdentity

/-- The ideal identity on an abstract parameter `A` and verdict `t`. -/
private theorem ideal_key (A : List Bool) (L : ℕ) (t : Bool) :
    ((if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if false = true then A.drop L else A.take L) = A.drop L))) = true
        then (1 : ℝ) else 0) +
      if (if decide (A.take L = A.drop L) then false
        else (t == decide ((if true = true then A.drop L else A.take L) = A.drop L))) = true
        then 1 else 0) =
      if (!decide (A.take L = A.drop L)) = true then 1 else 0 := by
  by_cases hb : A.take L = A.drop L
  · simp [hb]
  · cases t <;> simp [hb]

/-- **The ideal identity, pointwise:** on the ideal experiment's views with the two coins, `D'`
accepts with indicator sum equal to `D''`'s (whatever the simulator's output and state): when
`m₀ ≠ m₁`, exactly one coin makes `[D(…) = 1] == [m = m₁]` hold, since `m = m_β`. -/
theorem ideal_identity (n ℓ : ℕ) (sk : List Bool) (w : List Bool)
    (sa : Option (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) (rD : D.Coins n)
    (ρ'' : (halfDist S).Coins n) (hw : w.length = ℓ * (S.ctLen.eval n + 1)) :
    ((if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0 : ℝ) +
      if (tailDist S D).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm true) w sa) (NUPPT.coinsCongr (tailDist_coins S D).symm n rD) = true
        then 1 else 0) =
      if (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n ℓ sk
        ((halfCoins S n).symm false) w sa) ρ'' = true then 1 else 0 := by
  have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
    PolyExpr.eval_add _ _ _
  have hA : (List.ofFn (sa.getD (zeroBits _))).length = S.msgLen.eval n + S.msgLen.eval n := by
    rw [List.length_ofFn, hpl]
  have hM : ∀ β, (List.ofFn (drawWith (halfSamp S) (S.msgLen.eval n) n (sa.getD (zeroBits _))
      ((halfCoins S n).symm β))).length = S.msgLen.eval n := fun _ => List.length_ofFn
  have hdrop : w.drop (ℓ * (S.ctLen.eval n + 1)) = [] := by rw [List.drop_eq_nil_iff, hw]
  rw [idealView_eq, idealView_eq, hdrop, List.append_nil, List.append_nil,
    tailDist_blocks S D n _ _ _ hA (hM false), tailDist_blocks S D n _ _ _ hA (hM true),
    halfDist_blocks S n _ _ _ hA (hM false), ofFn_drawWith_half S n _ hpl,
    ofFn_drawWith_half S n _ hpl]
  exact ideal_key _ _ _

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/SimINDGap.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIM-NME′ implies non-malleability: the advantage

Direction SIM ⇒ IND of [PS10, Theorem 174.8] ([PSV07, Corollary 1], at one message). With the
sampler `halfSamp S` (parameter `⟨m₀, m₁⟩`, output `m_β`), the SIM adversary `A'` of T2's handler
`copyHandler` and any simulator, the distinguishers `D' = tailDist S D` and `D'' = halfDist S`
satisfy, at every `n`,
* in the real experiment, `2·Pr[D' = 1] − Pr[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`
  (`real_gap`);
* in the ideal experiment, `2·Pr[D' = 1] = Pr[D'' = 1]` (`ideal_gap`).

So `NM`'s advantage is at most `2·adv(D') + adv(D'')`.

## Main definitions

* `NMSim.simHandler`: the SIM adversary's handler, `copyHandler` on the real experiment's
  oracles with the parameter `⟨m₀, m₁⟩` and the empty history.

## Main results

* `NMSim.realAcc_copyHandler`: the SIM adversary's real experiment is `A`'s.
* `NMSim.real_gap`, `NMSim.ideal_gap`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Corollary 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

variable (S : FixedLengthPKScheme)

/-! ### Linear algebra of expectations -/

/-- The pointwise identity `2·((A₀ + A₁)/2) − (B₀ + B₁)/2 = C₁ − C₀` passes to expectations. -/
private theorem lin_expect {α : Type} (c : ProbComp α) (A₀ A₁ B₀ B₁ C₀ C₁ : α → ℝ)
    (h : ∀ x, 2 * ((A₀ x + A₁ x) / 2) - (B₀ x + B₁ x) / 2 = C₁ x - C₀ x) :
    2 * ((expect c A₀ + expect c A₁) / 2) - (expect c B₀ + expect c B₁) / 2 =
      expect c C₁ - expect c C₀ := by
  have hC : expect c (fun x => C₁ x - C₀ x) =
      expect c (fun x => (A₀ x + A₁ x) - 2⁻¹ * (B₀ x + B₁ x)) :=
    congrArg _ (funext fun x => by linarith [h x])
  rw [← expect_sub, hC, expect_sub, expect_const_mul, expect_add, expect_add]
  ring

/-- `2·f − g = h₁ − h₀` pointwise passes to expectations. -/
private theorem lin_expect' {α : Type} (c : ProbComp α) (f g h₀ h₁ : α → ℝ)
    (h : ∀ x, 2 * f x - g x = h₁ x - h₀ x) :
    2 * expect c f - expect c g = expect c h₁ - expect c h₀ := by
  rw [← expect_const_mul, ← expect_sub, ← expect_sub]
  exact congrArg _ (funext h)

/-- **The coupling in expectation:** if `T₀(e c) + T₁(e c) − (H₀ b + H₁ b)/2 = V₁ c − V₀ c` for all
`c`, `b`, then `2·((𝔼T₀ + 𝔼T₁)/2) − (𝔼H₀ + 𝔼H₁)/2 = 𝔼V₁ − 𝔼V₀` (uniform samples; `e` a
bijection). -/
private theorem lin_sample {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype γ] [Nonempty γ] (T₀ T₁ : α → ℝ) (H₀ H₁ : β → ℝ) (V₀ V₁ : γ → ℝ) (e : γ ≃ α)
    (h : ∀ c b, T₀ (e c) + T₁ (e c) - (H₀ b + H₁ b) / 2 = V₁ c - V₀ c) :
    2 * ((expect (sample α) T₀ + expect (sample α) T₁) / 2) -
        (expect (sample β) H₀ + expect (sample β) H₁) / 2 =
      expect (sample γ) V₁ - expect (sample γ) V₀ := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty γ)
  obtain ⟨b₀⟩ := (inferInstance : Nonempty β)
  have hH : expect (sample β) (fun b => H₀ b + H₁ b) =
      expect (sample β) (fun _ => 2 * (T₀ (e c₀) + T₁ (e c₀) - (V₁ c₀ - V₀ c₀))) :=
    congrArg _ (funext fun b => by linarith [h c₀ b])
  have hT : expect (sample γ) (fun c => T₀ (e c) + T₁ (e c) - (V₁ c - V₀ c)) =
      expect (sample γ) (fun _ => (H₀ b₀ + H₁ b₀) / 2) :=
    congrArg _ (funext fun c => by linarith [h c b₀])
  rw [expect_sub, expect_add, expect_sub, expect_const,
    expect_sample_equiv e T₀, expect_sample_equiv e T₁] at hT
  rw [expect_add, expect_const] at hH
  linarith [h c₀ b₀]

/-! ### The real experiment -/

/-- **The SIM adversary's real experiment is `A`'s:** for T2's machine `A'` of
`copyHandler S pl hl outL` (coin bijection `φ`, budget `K`), with `A`'s output length `dα(n) =
outL(n) = r·ctLen(n) + sl`, the real acceptance rate of `A'` is that of `A`'s run (on T2's
lengths) against the same oracle.

**Proof sketch.** Reindex `A'`'s coins by `φ` (`expect_sample_equiv`, `expect_sample_prod`), replace
`A'`'s run by `A`'s (`simulate_copyHandler_machine`), and drop the unread seed (`expect_const`). -/
theorem realAcc_copyHandler (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A A' : NUPPT) (q dα outL : PolyExpr) (K r sl : ℕ) (X : NUPPT)
    (n : ℕ) (hd : dα.eval n = outL.eval n) (hr : outL.eval n = r * S.ctLen.eval n + sl)
    (hK : K = q.eval n * (copyHandler S pl hl outL).perCall.eval n +
      (copyHandler S pl hl outL).finCall.eval n)
    (φ : (Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((copyHandler S pl hl outL).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (dα.eval n)) n (q.eval n) ((copyHandler S pl hl outL).advInput n z ω) r)
          ((copyHandler S pl hl outL).init n)).bind
          (fun res => (copyHandler S pl hl outL).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S pl j).eval n) (fun j => (snmDout S hl j).eval n)
          ((copyHandler S pl hl outL).outLen.eval n)) n
          (q.eval n * (copyHandler S pl hl outL).perCall.eval n +
            (copyHandler S pl hl outL).finCall.eval n) z (φ (ω, r))) :
    realAcc S atk samp pl hl hist A' K r sl X n =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (samp.Coins n)) fun ρ =>
      expect (sample (A.Coins n)) fun rA =>
      expect (sample (X.Coins n)) fun rX =>
      expect (simulate (rImpl S atk false samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (dα.eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := by
  subst hK
  rw [realAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  rw [← expect_sample_equiv φ, expect_sample_prod]
  refine Eq.trans ?_
    (expect_const (sample (Fin ((copyHandler S pl hl outL).seedLen.eval n) → Bool)) _)
  refine congrArg _ (funext fun ω => congrArg _ (funext fun rA => congrArg _ (funext fun rX => ?_)))
  have hout : r * S.ctLen.eval n + sl = (copyHandler S pl hl outL).outLen.eval n := by
    rw [copyHandler_outLen, hr]
  refine (expect_toCompOn_outLen _ A' n _ _ _ none hout fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ p.1 p.2) rX =
      true then (1 : ℝ) else 0).trans ?_
  rw [simulate_copyHandler_machine S A A' q dα pl hl outL n hd φ hφ, expect_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [expect_pure]
  dsimp only
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, copyHandler_outLen, hd])]

/-- **The SIM adversary's handler** for an NM adversary with `ℓ` output ciphertexts:
`copyHandler` on
the real experiment's oracles with the parameter `⟨m₀, m₁⟩` (`pl = msgLen + msgLen`), the empty
history and `ℓ·ctLen + 0` output bits (`r = ℓ`, `sl = 0`). -/
def simHandler (ℓ : PolyExpr) :
    InteractiveHandler 2 (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) 2
      (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) :=
  copyHandler S (S.msgLen.add S.msgLen) (.const 0) ((ℓ.mul S.ctLen).add (.const 0))

/-- `simHandler S ℓ = copyHandler S (msgLen + msgLen) 0 (ℓ·ctLen + 0)`. -/
theorem simHandler_eq (ℓ : PolyExpr) :
    simHandler S ℓ =
      copyHandler S (S.msgLen.add S.msgLen) (.const 0) ((ℓ.mul S.ctLen).add (.const 0)) :=
  rfl

/-- **The real experiment with the sampler `⟨m₀, m₁⟩ ↦ m_β`** is the average over `β` of `A`'s runs
`runB … β` (with any `ρ'`), the views read with the coin `β`.

**Proof sketch.** `realAcc_copyHandler` makes the experiment `A`'s run against the hybrid oracle
whose sampler coins `ρ` also stand in its `ρ'` slot, and `expect_sample_halfCoins` splits the
average over `ρ` into the two coins `β`. For each `β`, the oracle with `b = false` does not read
`ρ'` (`rImpl_false_coins`), so the run is `runB … β`, after transporting the output length
(`expect_toCompOn_outLen`). -/
private theorem realAcc_half (atk : Attack) (A A' : NUPPT) (q ℓ : PolyExpr) (K : ℕ) (X : NUPPT)
    (n : ℕ) (ρ' : (halfSamp S).Coins n)
    (hK : K = q.eval n * (simHandler S ℓ).perCall.eval n + (simHandler S ℓ).finCall.eval n)
    (φ : (Fin ((simHandler S ℓ).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((simHandler S ℓ).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((simHandler S ℓ).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            ((simHandler S ℓ).advInput n z ω) r)
          ((simHandler S ℓ).init n)).bind
          (fun res => (simHandler S ℓ).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((simHandler S ℓ).outLen.eval n)) n
          (q.eval n * (simHandler S ℓ).perCall.eval n +
            (simHandler S ℓ).finCall.eval n) z (φ (ω, r))) :
    realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) X n =
      expect (sample (S.gen.Coins n)) fun rg =>
        ((expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
          expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => [])
            (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) r ρ' false) fun p =>
            if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
              (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm false) (List.ofFn p.1)
              p.2) rX =
              true then 1 else 0) +
        (expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
          expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => [])
            (pairFstD (S.gen.runAt n [] rg))
            (pairSndD (S.gen.runAt n [] rg)) r ρ' true) fun p =>
            if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
              (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm true) (List.ofFn p.1) p.2) rX =
              true then 1 else 0)) / 2 := by
  have hd : (ℓ.mul S.ctLen).eval n = ((ℓ.mul S.ctLen).add (.const 0)).eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const, Nat.add_zero]
  have hr : ((ℓ.mul S.ctLen).add (.const 0)).eval n =
      ℓ.eval n * S.ctLen.eval n + (PolyExpr.const 0).eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hlen : (ℓ.mul S.ctLen).eval n = ℓ.eval n * S.ctLen.eval n := PolyExpr.eval_mul _ _ _
  rw [realAcc_copyHandler S atk _ _ _ _ A A' q (ℓ.mul S.ctLen) _ K _ _ X n hd hr hK φ hφ]
  refine congrArg _ (funext fun rg => ?_)
  rw [expect_sample_halfCoins]
  have hβ : ∀ β : Bool,
      (expect (sample (A.Coins n)) fun rA => expect (sample (X.Coins n)) fun rX =>
        expect (simulate (rImpl S atk false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0)
            (fun _ => []) n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
            ((halfCoins S n).symm β) ((halfCoins S n).symm β) none)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
          if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) (List.ofFn p.1) p.2) rX =
            true then 1 else 0) =
      expect (sample (A.Coins n)) fun r => expect (sample (X.Coins n)) fun rX =>
        expect (runB S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) r ρ' β) fun p =>
          if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) (List.ofFn p.1) p.2) rX =
            true then 1 else 0 := by
    intro β
    refine congrArg _ (funext fun rA => congrArg _ (funext fun rX => ?_))
    rw [runB_eq, rImpl_false_coins S atk _ _ _ _ n _ _ _ _ ρ']
    exact expect_toCompOn_outLen _ A n _ _ rA none hlen fun p =>
      if X.distinguisherL n (realView S (halfSamp S) (S.msgLen.add S.msgLen) n (ℓ.eval n)
        (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm β) p.1 p.2) rX = true
        then (1 : ℝ) else 0
  rw [← hβ false, ← hβ true]

/-- **The real experiment, `D'` against `D''`:** for the SIM adversary `A'` (T2's machine of
`simHandler S ℓ`, budget `K`),
`2·Pr_real[D' = 1] − Pr_real[D'' = 1] = Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1]`.

**Proof sketch.** Both acceptance rates are averages over `β` of `A`'s runs `runB … β`
(`realAcc_half`), and `NM_β` is the run with coin `β` (`accept_nmGame_eq_rImpl`). Pointwise in
the keys, `A`'s coins and the distinguishers' coins this is `real_identity`; it passes to the
expectations (`lin_expect'`, `lin_expect`, `lin_sample`, with `D`'s coins carried to `D'`'s). -/
theorem real_gap (atk : Attack) (A A' : NUPPT) (q ℓ : PolyExpr) (K : ℕ) (D : NUPPT) (n : ℕ)
    (hK : K = q.eval n * (simHandler S ℓ).perCall.eval n + (simHandler S ℓ).finCall.eval n)
    (φ : (Fin ((simHandler S ℓ).seedLen.eval n) → Bool) × A.Coins n ≃ A'.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((simHandler S ℓ).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((simHandler S ℓ).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n)
            (fun i => (snmDout S (.const 0) i).eval n) ((ℓ.mul S.ctLen).eval n)) n (q.eval n)
            ((simHandler S ℓ).advInput n z ω) r)
          ((simHandler S ℓ).init n)).bind
          (fun res => (simHandler S ℓ).finish n z ω res.2 res.1) =
        A'.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((simHandler S ℓ).outLen.eval n)) n
          (q.eval n * (simHandler S ℓ).perCall.eval n +
            (simHandler S ℓ).finCall.eval n) z (φ (ω, r))) :
    2 * realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) (tailDist S D) n -
      realAcc S atk (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) A' K (ℓ.eval n)
        ((PolyExpr.const 0).eval n) (halfDist S) n =
      accept (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) -
        accept (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n) := by
  rw [realAcc_half S atk A A' q ℓ K _ n ((halfCoins S n).symm false) hK φ hφ,
    realAcc_half S atk A A' q ℓ K _ n ((halfCoins S n).symm false) hK φ hφ,
    accept_nmGame_eq_rImpl S atk A (q.eval n) (ℓ.eval n) D true n (fun _ => [])
      ((halfCoins S n).symm false),
    accept_nmGame_eq_rImpl S atk A (q.eval n) (ℓ.eval n) D false n (fun _ => [])
      ((halfCoins S n).symm false)]
  refine lin_expect' _ _ _ _ _ fun rg => ?_
  refine lin_expect _ _ _ _ _ _ _ fun r => ?_
  refine lin_sample _ _ _ _ _ _ (NUPPT.coinsCongr (tailDist_coins S D).symm n) fun rD ρ'' => ?_
  exact real_identity S atk A (q.eval n) (ℓ.eval n) n (fun _ => []) _ _ r _ D rD ρ''

/-! ### The ideal experiment -/

/-- `D''` reads only the parameter: on the ideal experiment's views it ignores the sampler's
coin. -/
private theorem halfDist_idealView_coin (n r : ℕ) (sk w : List Bool)
    (sa : Option (Fin ((S.msgLen.add S.msgLen).eval n) → Bool)) (ρ'' : (halfDist S).Coins n)
    (β : Bool) :
    (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r sk
        ((halfCoins S n).symm β) w sa) ρ'' =
      (halfDist S).distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r sk
        ((halfCoins S n).symm false) w sa) ρ'' := by
  have hA : (List.ofFn (sa.getD (zeroBits _))).length = S.msgLen.eval n + S.msgLen.eval n := by
    rw [List.length_ofFn, PolyExpr.eval_add]
  rw [idealView_eq, idealView_eq, List.append_assoc (List.ofFn _ ++ List.ofFn _),
    List.append_assoc (List.ofFn _ ++ List.ofFn _), halfDist_blocks S n _ _ _ hA List.length_ofFn,
    halfDist_blocks S n _ _ _ hA List.length_ofFn]

/-- **The ideal experiment, `D'` against `D''`:** for every simulator,
`2·Pr_ideal[D' = 1] = Pr_ideal[D'' = 1]`.

**Proof sketch.** With the empty history the oracle ignores the sampler's coin (`histImpl_coins`),
so the coin `β` can be drawn after the simulator's run (`expect_sample_comm`,
`expect_sample_halfCoins`). Pointwise, `D'(β = 0) + D'(β = 1) = D''` (`ideal_identity`), and `D''`
ignores `β` (`halfDist_idealView_coin`). -/
theorem ideal_gap (Sim D : NUPPT) (r n : ℕ) :
    2 * idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) Sim r
        ((PolyExpr.const 0).eval n) (tailDist S D) n =
      idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) Sim r
        ((PolyExpr.const 0).eval n) (halfDist S) n := by
  have hhl : (PolyExpr.const 0).eval n = 0 := PolyExpr.eval_const _ _
  have hI : ∀ X : NUPPT, idealAcc S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => [])
      Sim r ((PolyExpr.const 0).eval n) X n =
      expect (sample (S.gen.Coins n)) fun rg =>
      expect (sample (Sim.Coins n)) fun rS =>
      expect (sample (X.Coins n)) fun rX =>
      expect (simulate (histImpl S (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) n
          ((halfCoins S n).symm false))
        (Sim.toCompOn (bitCodec (fun _ => (S.msgLen.add S.msgLen).eval n)
          (fun _ => (PolyExpr.const 0).eval n)
          (r * (S.ctLen.eval n + 1) + (PolyExpr.const 0).eval n))
          n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
        2⁻¹ * ((if X.distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm false) (List.ofFn p.1) p.2) rX =
            true then 1 else 0) +
          (if X.distinguisherL n (idealView S (halfSamp S) (S.msgLen.add S.msgLen) n r
            (pairSndD (S.gen.runAt n [] rg)) ((halfCoins S n).symm true) (List.ofFn p.1) p.2) rX =
            true then 1 else 0)) := by
    intro X
    rw [idealAcc_eq]
    refine congrArg _ (funext fun rg => ?_)
    rw [expect_sample_comm]
    refine congrArg _ (funext fun rS => ?_)
    rw [expect_sample_comm]
    refine congrArg _ (funext fun rX => ?_)
    rw [expect_sample_halfCoins, histImpl_coins S _ _ _ _ n ((halfCoins S n).symm true)
      ((halfCoins S n).symm false) hhl, ← expect_add, div_eq_inv_mul, ← expect_const_mul]
  rw [hI, hI, ← expect_const_mul]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_const_mul]
  refine congrArg _ (funext fun rS => ?_)
  symm
  refine Eq.trans (congrArg _ (funext fun ρ'' => ?_)) (expect_const (sample _) _)
  rw [← expect_sample_equiv (NUPPT.coinsCongr (tailDist_coins S D).symm n), ← expect_const_mul]
  symm
  refine Eq.trans (congrArg _ (funext fun rD => ?_)) (expect_const (sample _) _)
  rw [← expect_const_mul]
  refine congrArg _ (funext fun p => ?_)
  have hw : (List.ofFn p.1).length = r * (S.ctLen.eval n + 1) := by
    rw [List.length_ofFn, hhl, Nat.add_zero]
  have hid := ideal_identity S D n r (pairSndD (S.gen.runAt n [] rg)) (List.ofFn p.1) p.2 rD ρ'' hw
  rw [halfDist_idealView_coin S n r _ _ _ ρ'' true]
  linarith

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rounds of interactive handlers

Generic facts about T2's interactive handlers (`Games.InteractiveHandler`), used by the two
machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the simulator and the NM adversary).

* **Readers of a round input** `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`rdU`, `rdZ`, `rdW`,
  `rdState`,
  `rdIdx`, `rdQuery`, `rdLog`, `rdAns`), with their values (`fields_input`) and their
  polynomial-time bounds.
* **One call** whose first round returns (`impl_of_ret`), or asks one outer query and returns in its
  second round (`impl_of_query`); a finalization whose first round returns (`finish_of_ret`).
* **Costs with a one-shot oracle** (`simulate_costBoundedBy_once`): if the calls are free except one
  call, of cost at most one, that marks the state as used, the whole simulation costs at most one.

## Main definitions

* `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog`, `rdAns`.
* `NMSim.seedEquiv`, `NMSim.seedEquivPoly`: seeds made of coins.

## Main results

* `NMSim.fields_input`, `NMSim.rdAns_input`, `NMSim.polyTimeComputable_rd`.
* `NMSim.buildComp_of_ret`, `NMSim.impl_of_ret`, `NMSim.impl_of_query`, `NMSim.finish_of_ret`.
* `NMSim.seedEquiv_ofFn`, `NMSim.seedEquivPoly_ofFn`, `NMSim.ofFn_padFin_eq_padL`.
* `NMSim.costBoundedBy_bind_of_allOutputs`, `NMSim.simulate_costBoundedBy_once`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Readers of a round input -/

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
def rdU (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- `rdU w = pairFstD (pairFstD w)`. -/
theorem rdU_eq (w : List Bool) : rdU w = pairFstD (pairFstD w) := rfl

/-- The reduction input `z` of a round input. -/
def rdZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))

/-- `rdZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem rdZ_eq (w : List Bool) : rdZ w = pairFstD (pairSndD (pairFstD w)) := rfl

/-- The seed `ω` of a round input. -/
def rdW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))

/-- `rdW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem rdW_eq (w : List Bool) : rdW w = pairSndD (pairSndD (pairFstD w)) := rfl

/-- The state `s` of a round input. -/
def rdState (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- `rdState w = pairFstD (pairSndD w)`. -/
theorem rdState_eq (w : List Bool) : rdState w = pairFstD (pairSndD w) := rfl

/-- The oracle index `1^i` of a round input. -/
def rdIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))

/-- `rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w)))`. -/
theorem rdIdx_eq (w : List Bool) : rdIdx w = pairFstD (pairFstD (pairSndD (pairSndD w))) := rfl

/-- The query `x` of a round input. -/
def rdQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))

/-- `rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w)))`. -/
theorem rdQuery_eq (w : List Bool) : rdQuery w = pairSndD (pairFstD (pairSndD (pairSndD w))) :=
  rfl

/-- The outer log `L` of the call so far. -/
def rdLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- `rdLog w = pairSndD (pairSndD (pairSndD w))`. -/
theorem rdLog_eq (w : List Bool) : rdLog w = pairSndD (pairSndD (pairSndD w)) := rfl

/-- The outer answer `y` of the first entry `⟨1^j, ⟨x, y⟩⟩` of the outer log. -/
def rdAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rdLog w)))

/-- `rdAns w = pairSndD (pairSndD (pairFstD (rdLog w)))`. -/
theorem rdAns_eq (w : List Bool) : rdAns w = pairSndD (pairSndD (pairFstD (rdLog w))) := rfl

section Fields

variable {k : ℕ}

/-- **The fields of a round input** (DL-30–36 overlap: the round-input readers of
`Indistinguishability/Forward.lean`, here with the context): on
`input n z ω s i x L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` the readers return `1^n`, `z`, `ω`,
`s`, `1^i`, `x` and `L`. -/
theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rdU (InteractiveHandler.input n z ω s i x L) = List.replicate n true ∧
      rdZ (InteractiveHandler.input n z ω s i x L) = z ∧
      rdW (InteractiveHandler.input n z ω s i x L) = ω ∧
      rdState (InteractiveHandler.input n z ω s i x L) = s ∧
      rdIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
      rdQuery (InteractiveHandler.input n z ω s i x L) = x ∧
      rdLog (InteractiveHandler.input n z ω s i x L) = L := by
  simp only [InteractiveHandler.input_eq, rdU, rdZ, rdW, rdState, rdIdx, rdQuery, rdLog,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The answer of a one-entry outer log: `rdAns` of a round input with the log
`⟨⟨1^j, ⟨x', y⟩⟩, t⟩` is `y`. -/
theorem rdAns_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) (j : ℕ)
    (x' y t : List Bool) :
    rdAns (InteractiveHandler.input n z ω s i x
      (pairEncode (pairEncode (List.replicate j true) (pairEncode x' y)) t)) = y := by
  rw [rdAns, (fields_input n z ω s i x _).2.2.2.2.2.2, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

end Fields

/-- The round-input readers are polynomial-time: `rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`,
`rdQuery`, `rdLog` and `rdAns`. -/
theorem polyTimeComputable_rd :
    PolyTimeComputable rdU ∧ PolyTimeComputable rdZ ∧ PolyTimeComputable rdW ∧
      PolyTimeComputable rdState ∧ PolyTimeComputable rdIdx ∧ PolyTimeComputable rdQuery ∧
      PolyTimeComputable rdLog ∧ PolyTimeComputable rdAns := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hL : PolyTimeComputable rdLog := hD.comp (hD.comp hD)
  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp hD,
    hF.comp (hF.comp (hD.comp hD)), hD.comp (hF.comp (hD.comp hD)), hL,
    hD.comp (hD.comp (hF.comp hL))⟩

/-! ### Calls and finalizations -/

/-- A final output is the computation at every budget: if `next hist = ret a`, then
`buildComp next t q hist = pure a`. -/
theorem buildComp_of_ret {ι α : Type} {spec : OracleSpec ι} {next : QueryLog spec → Move spec α}
    {t : α} {q : ℕ} {hist : QueryLog spec} {a : α} (h : next hist = .ret a) :
    buildComp next t q hist = .pure a := by
  cases q with
  | zero => exact buildComp_zero_of_ret h
  | succ q => exact buildComp_succ_of_ret h

/-- The two parts of a padded concatenation: if `|u| = d₁`, the first `d₁` bits of
`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v`. -/
theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

section Calls

variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin (H.seedLen.eval n) → Bool)

/-- **A call that returns at once:** if the first round on the inner query `x` to oracle `i` in
state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call answers
`padFin _ u` with the new state `padFin _ v`, asking nothing. -/
theorem impl_of_ret (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
    (hv : v.length = H.stateLen.eval n)
    (hrun : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (u ++ v)) :
    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) := by
  have hw : u ++ v = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) :=
    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq,
    buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u ++ v)) (by
      rw [MachineCodec.encodeLog_nil, hrun]
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) u v hu
  rw [h₁, h₂]

/-- **A call with one outer query:** if the first round asks the outer query `x'` to oracle `j`,
and the second round, with the answer `y` in the outer log, returns `⟨[true], u y ‖ v y⟩`, then
(with `perCall ≥ 1`) the call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))`.

**Proof sketch.** Unfold the call (`impl_apply`, `call_eq`) at the budget `perCall = p + 1`. The
first round decodes to the query (`decodeBitMove_query`), which `buildComp_succ_of_query` asks.
After the answer `y` the log encodes as in `hrun₁` (`bitCodec_encodeEntry`), the second round
decodes to the return of `padFin _ (u y ‖ v y)` (`buildComp_of_ret`, `decodeBitMove_ret`), and
`padFin_append_split` splits it into the answer and the state. -/
theorem impl_of_query (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
    (hpc : 1 ≤ H.perCall.eval n)
    (hrun₀ : H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.run (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
        [])) = pairEncode [true] (u y ++ v y)) :
    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) := by
  obtain ⟨p, hp⟩ : ∃ p, H.perCall.eval n = p + 1 := ⟨H.perCall.eval n - 1, by omega⟩
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, hp,
    buildComp_succ_of_query (i := j) (x := x') (by
      rw [MachineCodec.encodeLog_nil, hrun₀]
      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x'),
    OracleComp.query_bind]
  congr 1
  funext y
  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      bitCodec_encodeEntry]
  have hw : u y ++ v y = List.ofFn (padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) :=
    (GGMRed.ofFn_padFin_of_length (by rw [List.length_append, hu, hv])).symm
  rw [buildComp_of_ret (a := padFin ((dout i).eval n + H.stateLen.eval n) (u y ++ v y)) (by
      rw [hlog, hrun₁]
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).trans
        (decodeBitMove_ret _ _ _ _)), OracleComp.pure_bind]
  obtain ⟨h₁, h₂⟩ := padFin_append_split (d₂ := H.stateLen.eval n) (u y) (v y) (hu y)
  rw [h₁, h₂]

/-- **A finalization that returns at once:** if its first round returns `⟨[true], b⟩` with
`|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing. -/
theorem finish_of_ret (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (b : List Bool) (hb : b.length = H.outLen.eval n)
    (hrun : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
      []) = pairEncode [true] b) :
    H.finish n z ω s a = .pure (padFin _ b) := by
  rw [InteractiveHandler.finish_eq]
  refine buildComp_of_ret ?_
  rw [MachineCodec.encodeLog_nil, hrun]
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w))
    (GGMRed.ofFn_padFin_of_length hb).symm).trans (decodeBitMove_ret _ _ _ _)

end Calls

/-! ### Seeds and padding -/

/-- **A seed of two machines' coins:** for `L = A.coins + B.coins`,
`A.Coins n × B.Coins n ≃ {0,1}^{L(n)}`, concatenating the two coin strings (`seedEquiv_ofFn`). -/
def seedEquiv {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ) :
    A.Coins n × B.Coins n ≃ (Fin (L.eval n) → Bool) :=
  ((NUPPT.coinsEquivPoly rfl n).prodCongr (NUPPT.coinsEquivPoly rfl n)).trans
    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))

/-- The seed is the concatenation of the coins: `⟦seedEquiv h n (r₁, r₂)⟧ = ⟦r₁⟧ ++ ⟦r₂⟧`. -/
theorem seedEquiv_ofFn {A B : NUPPT} {L : PolyExpr} (h : L = A.coins.add B.coins) (n : ℕ)
    (c : A.Coins n × B.Coins n) :
    List.ofFn (seedEquiv h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [seedEquiv, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, NUPPT.coinsEquivPoly_ofFn]

/-- **A seed of a machine's coins and a string:** for `L = A.coins + L₂`,
`A.Coins n × {0,1}^{L₂(n)} ≃ {0,1}^{L(n)}`, concatenating (`seedEquivPoly_ofFn`). -/
def seedEquivPoly {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ) :
    A.Coins n × (Fin (L₂.eval n) → Bool) ≃ (Fin (L.eval n) → Bool) :=
  ((NUPPT.coinsEquivPoly rfl n).prodCongr (Equiv.refl _)).trans
    (EnsembleLemmas.coinsEquiv (by rw [h, PolyExpr.eval_add]))

/-- The seed is the concatenation: `⟦seedEquivPoly h n (r, w)⟧ = ⟦r⟧ ++ ⟦w⟧`. -/
theorem seedEquivPoly_ofFn {A : NUPPT} {L L₂ : PolyExpr} (h : L = A.coins.add L₂) (n : ℕ)
    (c : A.Coins n × (Fin (L₂.eval n) → Bool)) :
    List.ofFn (seedEquivPoly h n c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [seedEquivPoly, Equiv.trans_apply, EnsembleLemmas.ofFn_coinsEquiv, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn, Equiv.refl_apply]

/-- A machine's coins have `coins(n)` bits: `|⟦r⟧| = A.coins.eval n`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

/-- `⟦padFin k a⟧ = padL k a` (DL-30–36 overlap: the private `ofFn_padFin_eq_padL` of
`AdaptiveCPA/Handler.lean`, from the public `ofFn_padFin_eq_take`). -/
theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-! ### Costs with a one-shot oracle -/

section Cost

variable {ι ι' σ α β : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- **Costs add under sequencing, on the possible outputs:** if `c` fits in `q₁`, every possible
output of `c` satisfies `P`, and `f a` fits in `q₂` for every `a` with `P a`, then `c` followed by
`f` fits in `q₁ + q₂`. -/
theorem costBoundedBy_bind_of_allOutputs {cost : ι → ℕ} {c : OracleComp spec α}
    {f : α → OracleComp spec β} {P : α → Prop} {q₁ q₂ : ℕ} (hc : c.CostBoundedBy cost q₁)
    (hP : c.AllOutputs P) (hf : ∀ a, P a → (f a).CostBoundedBy cost q₂) :
    (c.bind f).CostBoundedBy cost (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a =>
    rw [OracleComp.pure_bind]
    exact (hf a (OracleComp.allOutputs_pure.1 hP)).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    rw [OracleComp.query_bind]
    refine (OracleComp.costBoundedBy_query _ _ _ _ _).2
      ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y) (OracleComp.allOutputs_query.1 hP y)

/-- **A one-shot oracle costs at most one query in total.** Let `good` be an invariant of the
states and `used` mark the states after the costly call. If from a good used state every call is
free and keeps the state good and used, and from a good unused state every call is either free and
keeps the state good and unused, or costs at most `1` and leaves it good and used, then the
simulation of any computation from a good state costs at most `0` (used) or `1` (unused).

**Proof sketch.** Induction on the computation; at a query, `costBoundedBy_bind_of_allOutputs`
with the call's cost and the continuation's (`0 + 0`, `0 + 1` or `1 + 0`). -/
theorem simulate_costBoundedBy_once (impl : QueryImpl spec σ spec') (cost : ι' → ℕ)
    (good used : σ → Prop) [DecidablePred used]
    (hused : ∀ i x s, good s → used s →
      (impl i x s).CostBoundedBy cost 0 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2)
    (hfresh : ∀ i x s, good s → ¬ used s →
      ((impl i x s).CostBoundedBy cost 0 ∧
          (impl i x s).AllOutputs fun p => good p.2 ∧ ¬ used p.2) ∨
        ((impl i x s).CostBoundedBy cost 1 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2))
    (c : OracleComp spec α) :
    ∀ s, good s → (simulate impl c s).CostBoundedBy cost (if used s then 0 else 1) := by
  induction c with
  | pure a =>
    intro s _
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    intro s hs
    rw [simulate_query]
    by_cases hu : used s
    · obtain ⟨h₀, hP⟩ := hused i x s hs hu
      have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
        have h := ih p.1 p.2 hp.1
        rwa [if_pos hp.2] at h
      rwa [if_pos hu]
    · rw [if_neg hu]
      rcases hfresh i x s hs hu with ⟨h₀, hP⟩ | ⟨h₁, hP⟩
      · have := costBoundedBy_bind_of_allOutputs h₀ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_neg hp.2] at h
        rwa [Nat.zero_add] at this
      · exact costBoundedBy_bind_of_allOutputs h₁ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_pos hp.2] at h

end Cost

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Challenge.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The challenge handler

Both machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] run the SIM adversary `A` against
the real experiment's oracles under CPA, answered in the same way:
* `Dec` answers `⊥` (all `false`), as under CPA (`snmImpl_dec_cpa`), without an outer query;
* the first challenge on the parameter `a` asks one outer query, computed from `a`, and answers
  `⟨Y, H⟩` (a ciphertext and a history) computed from `a` and the outer answer; it records
  `⟨Y, H, a⟩`;
* a repeated challenge answers the recorded `⟨Y, H⟩`, without an outer query.

The simulator asks the history oracle and computes `Y` itself; the NM adversary asks its challenge
oracle and computes `H` itself. This file builds the handler once (`chalHandler`), with the outer
query and the two answer parts as parameters (`ChalParams`), and proves its calls on the encoded
states (`chalState`) and that a whole run asks at most one outer query
(`chalHandler_costBoundedBy`).

## Main definitions

* `NMSim.ChalParams`: the parameters of the handler.
* `NMSim.chalHandler`, `NMSim.chalState`.

## Main results

* `NMSim.chalHandler_impl_dec`, `NMSim.chalHandler_impl_some`, `NMSim.chalHandler_impl_none`.
* `NMSim.chalHandler_costBoundedBy`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- **The parameters of the challenge handler** for inner oracles of parameter length `pl` and
history length `hl`, and `k'` outer oracles with lengths `din'`, `dout'`: the outer oracle `j` of
the challenge, the seed length, the adversary's input, the outer query `qry`, the two answer parts
`ansY` (`ctLen(n)` bits) and `ansH` (`hl(n)` bits), all read from the round input (the last two
with the outer answer in its log), and the finalization. -/
structure ChalParams (pl hl : PolyExpr) (k' : ℕ) (din' dout' : Fin k' → PolyExpr) where
  /-- The outer oracle asked on the first challenge. -/
  j : Fin k'
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The adversary's input, from the context. -/
  advIn : List Bool → List Bool
  /-- It is polynomial-time. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The outer query, from the round input. -/
  qry : List Bool → List Bool
  /-- It is polynomial-time. -/
  qry_poly : PolyTimeComputable qry
  /-- It has the outer query length. -/
  qry_len : ∀ w, (qry w).length = (din' j).eval (rdU w).length
  /-- The ciphertext part of the answer, from the round input with the outer answer. -/
  ansY : List Bool → List Bool
  /-- It is polynomial-time. -/
  ansY_poly : PolyTimeComputable ansY
  /-- It has `ctLen(n)` bits. -/
  ansY_len : ∀ w, (ansY w).length = S.ctLen.eval (rdU w).length
  /-- The history part of the answer, from the round input with the outer answer. -/
  ansH : List Bool → List Bool
  /-- It is polynomial-time. -/
  ansH_poly : PolyTimeComputable ansH
  /-- It has `hl(n)` bits. -/
  ansH_len : ∀ w, (ansH w).length = hl.eval (rdU w).length
  /-- The length of the output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- The finalization's round. -/
  finRun : List Bool → List Bool
  /-- It is polynomial-time. -/
  finRun_poly : PolyTimeComputable finRun

variable {S} {pl hl : PolyExpr} {k' : ℕ} {din' dout' : Fin k' → PolyExpr}

/-- **One round of the challenge handler** on `w = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, with the
state `s = [flag] ‖ Y ‖ H ‖ a`: `Dec` (`i = 0`) returns `⊥ = 0^{msgLen + 1}` and keeps `s`; a
challenge with the flag set returns the recorded `⟨Y, H⟩`; otherwise, with an empty outer log, it
asks `qry w` to the outer oracle `j`, and with the answer in the log it returns `⟨Y, H⟩` and the
state `[true] ‖ Y ‖ H ‖ x`. -/
def chalRun (P : ChalParams S pl hl k' din' dout') (w : List Bool) : List Bool :=
  if decide (rdIdx w = []) then
    pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
      rdState w)
  else if (rdState w).headD false then
    pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
      rdState w)
  else if decide (rdLog w = []) then
    pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
  else
    pairEncode [true] (P.ansY w ++ P.ansH w ++
      (true :: (P.ansY w ++ P.ansH w ++ EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w))))

/-- `chalRun P w` is `⟨[true], 0^{msgLen+1} ‖ s⟩` if `i = 0`; else
`⟨[true], (s.drop 1).take (ctLen + hl) ‖ s⟩` if the flag is set; else
`⟨[false], ⟨1^j, qry w⟩⟩` if the outer log is empty; else
`⟨[true], Y ‖ H ‖ (true :: Y ‖ H ‖ padL pl x)⟩`, with `Y = ansY w` and `H = ansH w`. -/
theorem chalRun_eq (P : ChalParams S pl hl k' din' dout') (w : List Bool) :
    chalRun P w =
      if decide (rdIdx w = []) then
        pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rdU w).length) false ++
          rdState w)
      else if (rdState w).headD false then
        pairEncode [true] (((rdState w).drop 1).take ((S.ctLen.add hl).eval (rdU w).length) ++
          rdState w)
      else if decide (rdLog w = []) then
        pairEncode [false] (pairEncode (List.replicate P.j true) (P.qry w))
      else
        pairEncode [true] (P.ansY w ++ P.ansH w ++ (true :: (P.ansY w ++ P.ansH w ++
          EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)))) := rfl

/-- The round is polynomial-time. -/
theorem polyTimeComputable_chalRun (P : ChalParams S pl hl k' din' dout') :
    PolyTimeComputable (chalRun P) := by
  obtain ⟨hU, -, -, hS, hI, hQ, hL, -⟩ := polyTimeComputable_rd
  have hT := polyTimeComputable_const [true]
  have hY := P.ansY_poly
  have hH := P.ansH_poly
  have hYH : PolyTimeComputable fun w => P.ansY w ++ P.ansH w := hY.append hH
  refine polyTimeComputable_ite (polyTimeComputable_isNil.comp hI)
    (hT.pairEncode ((EnsembleLemmas.polyTimeComputable_zeros _ hU).append hS))
    (polyTimeComputable_ite (polyTimeComputable_headD.comp hS)
      (hT.pairEncode (((polyTimeComputable_pairTakePoly (S.ctLen.add hl)).comp
        (hU.pairEncode (polyTimeComputable_tail.comp hS))).congr (fun w => by
          simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]) |>.append hS))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
        ((polyTimeComputable_const [false]).pairEncode
          ((polyTimeComputable_const _).pairEncode P.qry_poly))
        (hT.pairEncode (hYH.append (BinArith.polyTimeComputable_cons
          (polyTimeComputable_const [true])
          (hYH.append (EnsembleLemmas.polyTimeComputable_padL pl hU hQ)))))))

/-- **The challenge handler** for the parameters `P`: the state `[flag] ‖ Y ‖ H ‖ a`
(`1 + (ctLen + hl) + pl` bits, initially all `false`), one outer call per inner query, the round
`chalRun P`, and `P`'s seed, adversary input and finalization. -/
def chalHandler (P : ChalParams S pl hl k' din' dout') :
    InteractiveHandler 2 (snmDin S pl) (snmDout S hl) k' din' dout' where
  stateLen := ((PolyExpr.const 1).add (S.ctLen.add hl)).add pl
  seedLen := P.seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := chalRun P
  poly := polyTimeComputable_chalRun P
  advIn := P.advIn
  advIn_poly := P.advIn_poly
  outLen := P.outLen
  finCall := P.finCall
  finRun := P.finRun
  finRun_poly := P.finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall advIn outLen finCall
  finRun] chalHandler

section State

variable (P : ChalParams S pl hl k' din' dout') (n : ℕ)

/-- The state has `1 + (ctLen(n) + hl(n)) + pl(n)` bits. -/
theorem chalHandler_stateLen_eval :
    (chalHandler P).stateLen.eval n = 1 + (S.ctLen.eval n + hl.eval n) + pl.eval n := by
  rw [chalHandler_stateLen, PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_add,
    PolyExpr.eval_const]

/-- **The encoded states:** `none` (no challenge yet) is all `false`, and `some (Y, H, a)` is
`[true] ‖ Y ‖ H ‖ a`. -/
def chalState
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) ×
      (Fin (pl.eval n) → Bool))) :
    Fin ((chalHandler P).stateLen.eval n) → Bool :=
  match o with
  | none => zeroBits _
  | some (y, h, a) => padFin _ (true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a))

/-- `chalState P n none = 0`. -/
theorem chalState_none : chalState P n none = zeroBits _ := rfl

/-- `chalState P n (some (Y, H, a)) = padFin _ ([true] ‖ Y ‖ H ‖ a)`. -/
theorem chalState_some (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    chalState P n (some (y, h, a)) =
      padFin _ (true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a)) := rfl

/-- The initial state is `chalState P n none`. -/
theorem chalHandler_init : (chalHandler P).init n = chalState P n none := rfl

/-- The encoded state `some (Y, H, a)` as a string: `[true] ‖ Y ‖ H ‖ a`. -/
theorem ofFn_chalState_some (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    List.ofFn (chalState P n (some (y, h, a))) =
      true :: (List.ofFn y ++ List.ofFn h ++ List.ofFn a) := by
  rw [chalState_some]
  refine GGMRed.ofFn_padFin_of_length ?_
  rw [List.length_cons, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    List.length_ofFn, chalHandler_stateLen_eval]
  omega

/-- The encoded state `none` as a string is all `false`. -/
theorem ofFn_chalState_none :
    List.ofFn (chalState P n none) =
      List.replicate ((chalHandler P).stateLen.eval n) false := by
  rw [chalState_none, ofFn_zeroBits]

/-- The first bit of an encoded state tells whether a challenge was recorded. -/
theorem headD_ofFn_chalState
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) ×
      (Fin (pl.eval n) → Bool))) :
    (List.ofFn (chalState P n o)).headD false = o.isSome := by
  cases o with
  | none =>
    rw [ofFn_chalState_none, chalHandler_stateLen_eval, Nat.add_assoc, Nat.add_comm,
      List.replicate_succ, List.headD_cons]
    rfl
  | some yha =>
    obtain ⟨y, h, a⟩ := yha
    rw [ofFn_chalState_some, List.headD_cons]
    rfl

end State

/-- A padded run of `false`s is all `false`: `padFin d (0^m) = 0`. -/
private theorem padFin_replicate_false (d m : ℕ) :
    padFin d (List.replicate m false) = zeroBits d := by
  funext i
  rw [padFin_apply, zeroBits_apply]
  by_cases h : (i : ℕ) < m
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]

section Calls

variable (P : ChalParams S pl hl k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin ((chalHandler P).seedLen.eval n) → Bool)

/-- **`Dec` answers `⊥` and keeps the state**, asking nothing. -/
theorem chalHandler_impl_dec (x : Fin ((snmDin S pl 0).eval n) → Bool)
    (o : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (hl.eval n) → Bool) ×
      (Fin (pl.eval n) → Bool))) :
    (chalHandler P).impl n z ω 0 x (chalState P n o) = .pure (zeroBits _, chalState P n o) := by
  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n o)) 0 (List.ofFn x) []
  rw [impl_of_ret (chalHandler P) n z ω 0 x (chalState P n o)
    (List.replicate ((S.msgLen.add (.const 1)).eval n) false) (List.ofFn (chalState P n o))
    (by rw [List.length_replicate, snmDout_zero]) List.length_ofFn (by
      show chalRun P _ = _
      rw [chalRun_eq, hI, hU, hS, List.length_replicate]
      rfl), padFin_replicate_false, padFin_ofFn]

/-- **A repeated challenge answers the recorded `⟨Y, H⟩`** and keeps the state, asking nothing. -/
theorem chalHandler_impl_some (x : Fin ((snmDin S pl 1).eval n) → Bool)
    (y : Fin (S.ctLen.eval n) → Bool) (h : Fin (hl.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
    (chalHandler P).impl n z ω 1 x (chalState P n (some (y, h, a))) =
      .pure (padFin _ (List.ofFn y ++ List.ofFn h), chalState P n (some (y, h, a))) := by
  obtain ⟨hU, -, -, hS, hI, -, -⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n (some (y, h, a)))) 1 (List.ofFn x) []
  have hans : ((List.ofFn (chalState P n (some (y, h, a)))).drop 1).take
      ((S.ctLen.add hl).eval n) = List.ofFn y ++ List.ofFn h := by
    rw [ofFn_chalState_some, List.drop_one, List.tail_cons, PolyExpr.eval_add]
    exact List.take_left' (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
  rw [impl_of_ret (chalHandler P) n z ω 1 x _ (List.ofFn y ++ List.ofFn h)
    (List.ofFn (chalState P n (some (y, h, a))))
    (by rw [List.length_append, List.length_ofFn, List.length_ofFn, snmDout_one, PolyExpr.eval_add])
    List.length_ofFn (by
      show chalRun P _ = _
      rw [chalRun_eq, hI, hU, hS, List.length_replicate, headD_ofFn_chalState, hans]
      rfl), padFin_ofFn]

/-- **A first challenge asks one outer query:** on the parameter `x` in the empty state it asks
`qry w₀` to the outer oracle `j` (`w₀` the round input with the empty log) and, on the answer `y`,
answers `⟨Y, H⟩ = ⟨ansY w₁, ansH w₁⟩` (`w₁` the round input with `y` in the log), recording
`⟨Y, H, x⟩`.

**Proof sketch.** `impl_of_query` with the answer `ansY w₁ ‖ ansH w₁` and the encoded state
`chalState (some ⟨Y, H, x⟩)` (lengths by `ansY_len`, `ansH_len`; `perCall = 1`). The first
round, on `w₀` (a challenge, flag unset, empty log), is the query branch of `chalRun_eq`; the
second, on `w₁`, is its answer branch, with `x` read back through `padL`
(`ofFn_chalState_some`, `ofFn_padFin_of_length`). -/
theorem chalHandler_impl_none (x : Fin ((snmDin S pl 1).eval n) → Bool) :
    (chalHandler P).impl n z ω 1 x (chalState P n none) =
      .query P.j (padFin _ (P.qry (InteractiveHandler.input n z (List.ofFn ω)
          (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) [])))
        fun y : Fin ((dout' P.j).eval n) → Bool =>
          .pure (padFin _ (P.ansY (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []))
                  (List.ofFn y))) [])) ++
            P.ansH (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []))
                  (List.ofFn y))) []))),
          chalState P n (some (padFin _ (P.ansY (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []))
                  (List.ofFn y))) []))),
            padFin _ (P.ansH (InteractiveHandler.input n z (List.ofFn ω)
              (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
              (pairEncode (pairEncode (List.replicate P.j true)
                (pairEncode (P.qry (InteractiveHandler.input n z (List.ofFn ω)
                  (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []))
                  (List.ofFn y))) []))),
            padFin (pl.eval n) (List.ofFn x)))) := by
  set w₀ := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (chalState P n none)) (1 : Fin 2)
    (List.ofFn x) [] with hw₀
  obtain ⟨hU₀, -, -, hS₀, hI₀, -, hL₀⟩ := fields_input (k := 2) n z (List.ofFn ω)
    (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x) []
  have hq : List.ofFn (padFin ((din' P.j).eval n) (P.qry w₀)) = P.qry w₀ :=
    GGMRed.ofFn_padFin_of_length (by rw [P.qry_len, hU₀, List.length_replicate])
  have hxl : (List.ofFn x).length = pl.eval n := by
    rw [List.length_ofFn]
    show (snmDin S pl 1).eval n = _
    rw [snmDin_one]
  have hx : EnsembleLemmas.padL (pl.eval n) (List.ofFn x) =
      List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
    rw [EnsembleLemmas.padL_eq, GGMRed.ofFn_padFin_of_length hxl]
    exact List.take_left' hxl
  have hpc : 1 ≤ (chalHandler P).perCall.eval n := by
    rw [chalHandler_perCall, PolyExpr.eval_const]
  set W₁ : (Fin ((dout' P.j).eval n) → Bool) → List Bool := fun y =>
    InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (chalState P n none)) (1 : Fin 2)
      (List.ofFn x)
      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
    with hW₁
  have hY : ∀ y, (P.ansY (W₁ y)).length = S.ctLen.eval n := fun y => by
    rw [P.ansY_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
  have hH : ∀ y, (P.ansH (W₁ y)).length = hl.eval n := fun y => by
    rw [P.ansH_len, hW₁, (fields_input (k := 2) n z _ _ 1 _ _).1, List.length_replicate]
  rw [impl_of_query (chalHandler P) n z ω 1 x (chalState P n none) P.j (padFin _ (P.qry w₀))
    (fun y => P.ansY (W₁ y) ++ P.ansH (W₁ y))
    (fun y => List.ofFn (chalState P n (some (padFin _ (P.ansY (W₁ y)), padFin _ (P.ansH (W₁ y)),
      padFin (pl.eval n) (List.ofFn x)))))
    (fun y => by rw [List.length_append, hY, hH, snmDout_one, PolyExpr.eval_add])
    (fun y => List.length_ofFn) hpc ?_ (fun y => ?_)]
  · refine congrArg _ (funext fun y => ?_)
    rw [padFin_ofFn (chalState P n (some (padFin _ (P.ansY (W₁ y)), padFin _ (P.ansH (W₁ y)),
      padFin (pl.eval n) (List.ofFn x))))]
  · show chalRun P _ = _
    rw [chalRun_eq, hI₀, hU₀, hS₀, hL₀, List.length_replicate, headD_ofFn_chalState, hq]
    rfl
  · rw [hq]
    obtain ⟨hU₁, -, -, hS₁, hI₁, hQ₁, hL₁⟩ := fields_input (k := 2) n z (List.ofFn ω)
      (List.ofFn (chalState P n none)) (1 : Fin 2) (List.ofFn x)
      (pairEncode (pairEncode (List.replicate P.j true) (pairEncode (P.qry w₀) (List.ofFn y))) [])
    show chalRun P (W₁ y) = _
    beta_reduce
    rw [chalRun_eq, hW₁]
    beta_reduce
    rw [hI₁, hU₁, hS₁, hL₁, hQ₁, List.length_replicate, headD_ofFn_chalState, hx,
      ofFn_chalState_some, GGMRed.ofFn_padFin_of_length (hY y), GGMRed.ofFn_padFin_of_length (hH y)]
    rw [if_neg (by simp), if_neg (by simp),
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

/-- **A whole run asks at most one outer query:** from the initial state, the simulation of any
computation by the challenge handler is `CostBoundedBy 1` (one per outer query).

**Proof sketch.** `simulate_costBoundedBy_once` with the encoded states as the invariant and the
recorded ones as used: `Dec` and repeated challenges are free (`chalHandler_impl_dec`,
`chalHandler_impl_some`), and the first challenge asks one query and records
(`chalHandler_impl_none`). -/
theorem chalHandler_costBoundedBy {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α) :
    (simulate ((chalHandler P).impl n z ω) c (chalState P n none)).CostBoundedBy
      (fun _ => 1) 1 := by
  classical
  have hne : ∀ y h a, chalState P n none ≠ chalState P n (some (y, h, a)) := by
    intro y h a heq
    have := congrArg (fun s => (List.ofFn s).headD false) heq
    simp only [headD_ofFn_chalState, Option.isSome_none, Option.isSome_some] at this
    exact Bool.false_ne_true this
  have key := simulate_costBoundedBy_once ((chalHandler P).impl n z ω) (fun _ => 1)
    (fun s => ∃ o, s = chalState P n o) (fun s => ∃ y h a, s = chalState P n (some (y, h, a)))
    (fun i x s _ hu => ?_) (fun i x s hg hu => ?_) c (chalState P n none) ⟨none, rfl⟩
  · rwa [if_neg (fun ⟨y, h, a, heq⟩ => hne y h a heq)] at key
  · obtain ⟨y, h, a, rfl⟩ := hu
    match i, x with
    | 0, x =>
      rw [chalHandler_impl_dec]
      exact ⟨OracleComp.costBoundedBy_pure _ _ _,
        OracleComp.allOutputs_pure.2 ⟨⟨some (y, h, a), rfl⟩, ⟨y, h, a, rfl⟩⟩⟩
    | 1, x =>
      rw [chalHandler_impl_some]
      exact ⟨OracleComp.costBoundedBy_pure _ _ _,
        OracleComp.allOutputs_pure.2 ⟨⟨some (y, h, a), rfl⟩, ⟨y, h, a, rfl⟩⟩⟩
  · obtain ⟨o, rfl⟩ := hg
    cases o with
    | some yha => exact absurd ⟨yha.1, yha.2.1, yha.2.2, rfl⟩ hu
    | none =>
      match i, x with
      | 0, x =>
        rw [chalHandler_impl_dec]
        exact Or.inl ⟨OracleComp.costBoundedBy_pure _ _ _,
          OracleComp.allOutputs_pure.2 ⟨⟨none, rfl⟩, hu⟩⟩
      | 1, x =>
        rw [chalHandler_impl_none]
        exact Or.inr ⟨(OracleComp.costBoundedBy_query _ _ _ _ _).2 ⟨le_rfl, fun _ =>
          OracleComp.costBoundedBy_pure _ _ _⟩, OracleComp.allOutputs_query.2 fun _ =>
            OracleComp.allOutputs_pure.2 ⟨⟨some (_, _, padFin _ (List.ofFn x)), rfl⟩,
              ⟨_, _, padFin _ (List.ofFn x), rfl⟩⟩⟩

end Calls

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Simulator.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The simulator of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message), under CPA.
The simulator runs the SIM adversary `A` on `pk`, answering `Dec` with `⊥`. On `A`'s first
challenge `a` it asks its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own coins
(with `M`'s advice, read from its input `⟨pk, α_M⟩`), encrypts `ỹ = Enc_pk(m̃; re)` with its own
coins, answers `⟨ỹ, h(m)⟩` and records it. It outputs `A`'s ciphertexts, each flagged `COPY` iff it
equals `ỹ`, and `σ`.

It is the challenge handler (`chalHandler`) with the parameters `simParams`. Against the history
oracle, its run is `A`'s run against the hybrid oracle `rImpl … true … ρ ρ̃ (some re)`, which
encrypts an independent draw (`simComp_abs`); and the ideal experiment's view of its output is the
hybrid's view of `A`'s (`idealView_simOut`).

## Main definitions

* `NMSim.simMsg`, `NMSim.simCt`: `m̃` and `ỹ` read from a round input.
* `NMSim.flagF`, `NMSim.simOutL`, `NMSim.simFin`: the finalization.
* `NMSim.simParams`: the parameters of the simulator's handler.

## Main results

* `NMSim.simFinish`, `NMSim.simComp_abs`, `NMSim.idealView_simOut`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (finU finA fields_finInput polyTimeComputable_finFields)
open AdaptiveCPA (simulate_eq_of_abs)

variable (S : FixedLengthPKScheme) (samp : NUPPT)

/-! ### The dummy challenge -/

/-- The dummy message `m̃ = M(a; ρ̃)` read in a round `w`: with `n = |rdU w|`, `a = rdQuery w`, the
advice `α = snd (rdZ w)` and `ρ̃` the first `coins(n)` bits of the seed, `padL msgLen(n)` of `M`'s
output on `layout 1^n a α ρ̃`. -/
def simMsg (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
    (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
      ((rdW w).take (samp.coins.eval (rdU w).length))))

/-- `simMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
theorem simMsg_eq (w : List Bool) :
    simMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
      (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
        ((rdW w).take (samp.coins.eval (rdU w).length)))) := rfl

/-- The dummy challenge `ỹ = Enc_pk(m̃; re)` read in a round `w`: `pk = fst (rdZ w)`, `re` the seed
after `ρ̃`, `padL ctLen(n)` of `Enc`'s output on `⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩`. -/
def simCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
      (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
      ((rdW w).drop (samp.coins.eval (rdU w).length))))

/-- `simCt S samp w = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩)`. -/
theorem simCt_eq (w : List Bool) :
    simCt S samp w = EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
      (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
        (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
        ((rdW w).drop (samp.coins.eval (rdU w).length)))) := rfl

/-- The dummy message is polynomial-time. -/
theorem polyTimeComputable_simMsg : PolyTimeComputable (simMsg S samp) := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -, -⟩ := polyTimeComputable_rd
  have hρ : PolyTimeComputable fun w => (rdW w).take (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU hQ (polyTimeComputable_pairSndD.comp hZ) hρ))

/-- The dummy challenge is polynomial-time. -/
theorem polyTimeComputable_simCt : PolyTimeComputable (simCt S samp) := by
  obtain ⟨hU, hZ, hW, -, -, -, -, -⟩ := polyTimeComputable_rd
  have hre : PolyTimeComputable fun w => (rdW w).drop (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
    (((hU.pairEncode ((polyTimeComputable_pairFstD.comp hZ).pairEncode
      (polyTimeComputable_simMsg S samp))).pairEncode (polyTimeComputable_const [])).pairEncode
      hre))

/-! ### The finalization -/

/-- The state `s` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
def finSt (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- `finSt w = pairFstD (pairSndD w)`. -/
theorem finSt_eq (w : List Bool) : finSt w = pairFstD (pairSndD w) := rfl

/-- The state of a finalization input: `finSt (finInput n z ω s a L) = s`. -/
theorem finSt_finInput (n : ℕ) (z ω s a L : List Bool) :
    finSt (InteractiveHandler.finInput n z ω s a L) = s := by
  rw [finSt, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The state reader is polynomial-time. -/
theorem polyTimeComputable_finSt : PolyTimeComputable finSt :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The flagged entry** of a ciphertext `c`, on the context `⟨1^n, s⟩` with the state
`s = [flag] ‖ ỹ ‖ …`: `[flag ∧ c = ỹ]` followed by `c`. -/
def flagF (ctx c : List Bool) : List Bool :=
  ((pairSndD ctx).headD false &&
    decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c

/-- `flagF S ctx c = [snd ctx's flag ∧ c = ỹ] ++ c`. -/
theorem flagF_eq (ctx c : List Bool) :
    flagF S ctx c = ((pairSndD ctx).headD false &&
      decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c := rfl

/-- The flagged entry is polynomial-time, as a function of `⟨ctx, c⟩`. -/
theorem polyTimeComputable_flagF :
    PolyTimeComputable fun z => flagF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hy : PolyTimeComputable fun z =>
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp ((hF.comp hF).pairEncode
      (polyTimeComputable_tail.comp (hD.comp hF)))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun z => [decide (pairSndD z =
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length))] :=
    (polyTimeComputable_pairEq.comp (hD.pairEncode hy)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact BinArith.polyTimeComputable_cons
    (polyTimeComputable_and (polyTimeComputable_headD.comp (hD.comp hF)) heq) hD

/-- **The simulator's output** at parameter `n`, for the state string `st` and `A`'s output `a`
(`r(n)` ciphertexts, then `σ`): the flagged entries `flagF ⟨1^n, st⟩ c_i`, then `σ`. -/
def simOutL (r : PolyExpr) (n : ℕ) (st a : List Bool) : List Bool :=
  ((List.range (r.eval n)).map fun i =>
    flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
  a.drop (r.eval n * S.ctLen.eval n)

/-- `simOutL S r n st a = (flagF ⟨1^n, st⟩ c_0 ++ ⋯ ++ flagF ⟨1^n, st⟩ c_{r-1}) ++ σ`. -/
theorem simOutL_eq (r : PolyExpr) (n : ℕ) (st a : List Bool) :
    simOutL S r n st a =
      ((List.range (r.eval n)).map fun i =>
        flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
      a.drop (r.eval n * S.ctLen.eval n) := rfl

/-- **The simulator's finalization round**: `⟨[true], F ‖ a.drop (r·ctLen)⟩`, with no outer query,
where `F` is `chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` (the flagged entries) when
`ctLen(n) > 0`, and the `r` flags `[flag]` when `ctLen(n) = 0` (every ciphertext is then empty, and
equal to `ỹ`). -/
def simFin (r : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode [true]
    ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
        (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
          else List.replicate (r.eval (finU w).length) false)
      else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
        ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
    (finA w).drop ((r.mul S.ctLen).eval (finU w).length))

/-- `simFin S r w = ⟨[true], F ‖ a.drop (r·ctLen)⟩`, with `F = flag^r` if `ctLen(n) = 0` and
`F = chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` otherwise. -/
theorem simFin_eq (r : PolyExpr) (w : List Bool) :
    simFin S r w = pairEncode [true]
      ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
          (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
            else List.replicate (r.eval (finU w).length) false)
        else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
          ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
      (finA w).drop ((r.mul S.ctLen).eval (finU w).length)) := rfl

/-- The finalization round is polynomial-time. -/
theorem polyTimeComputable_simFin (r : PolyExpr) : PolyTimeComputable (simFin S r) := by
  obtain ⟨hU, -, -, hA, -⟩ := polyTimeComputable_finFields
  have hS := polyTimeComputable_finSt
  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (polyTimeComputable_const [true]).pairEncode
    ((polyTimeComputable_ite (polyTimeComputable_isNil.comp
        ((polyTimeComputable_unaryPoly S.ctLen).comp hU))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hS)
        ((polyTimeComputable_unaryPoly r).comp hU) (EnsembleLemmas.polyTimeComputable_zeros r hU))
      ((polyTimeComputable_chunkMap S.ctLen (polyTimeComputable_flagF S)).comp
        ((hU.pairEncode hS).pairEncode htake))).append hdrop)

/-- Every flagged entry has one bit more than its ciphertext. -/
theorem length_flagF (ctx c : List Bool) : (flagF S ctx c).length = c.length + 1 := by
  rw [flagF_eq, List.length_cons]

/-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits)
returns `⟨[true], simOutL …⟩`.

**Proof sketch.** Read the fields of the input in `simFin_eq` and split on `ctLen(n)`. If
`ctLen(n) = 0`, every chunk is empty and equals `ỹ`, so every flagged entry is `[flag]` and the
`r` entries flatten to `flag^r`. Otherwise cut `a.take (r·ctLen)` into its `r` chunks of
`ctLen(n)` bits (`take_eq_flatten_chunkAt`, `length_chunkAt`); `chunkMap_flatten` maps
`flagF` over them, which is `simOutL_eq`. -/
theorem simFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    simFin S r (InteractiveHandler.finInput n z ω s a L) =
      pairEncode [true] (simOutL S r n s a) := by
  obtain ⟨hU, -, -, hA, -⟩ := fields_finInput n z ω s a L
  rw [simFin_eq, hU, hA, finSt_finInput, List.length_replicate, PolyExpr.eval_mul, simOutL_eq]
  congr 2
  by_cases hct : S.ctLen.eval n = 0
  · rw [if_pos (by rw [hct, List.replicate_zero]; rfl)]
    have hent : ∀ i, flagF S (pairEncode (List.replicate n true) s) (chunkAt (S.ctLen.eval n) i a) =
        [s.headD false] := by
      intro i
      rw [flagF_eq, pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hct,
        chunkAt_eq, List.take_zero, List.take_zero, decide_eq_true rfl, Bool.and_true]
    have hrep : ∀ (b : Bool) (m : ℕ), ((List.range m).map fun _ => [b]).flatten =
        List.replicate m b := by
      intro b m
      induction m with
      | zero => rfl
      | succ m ih => rw [List.range_succ, List.map_append, List.flatten_append, ih,
          List.map_singleton, List.flatten_singleton, List.replicate_succ']
    simp only [hent]
    rw [hrep]
    cases s.headD false <;> rfl
  · rw [if_neg (by rw [decide_eq_true_eq, List.replicate_eq_nil_iff]; exact hct),
      take_eq_flatten_chunkAt,
      chunkMap_flatten _ _ n s _ (fun ch hch => ?_) (Nat.pos_of_ne_zero hct), List.map_map]
    · rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      rw [List.mem_range] at hi
      refine length_chunkAt _ _ _ ?_
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega

/-! ### The handler -/

variable (pl hl : PolyExpr)

/-- **The parameters of the simulator's handler** (on the real experiment's oracles with parameter
length `pl` and history length `hl`; one outer oracle, the history oracle): the first challenge `a`
asks `a`; it answers `⟨ỹ, h⟩` with `ỹ = simCt` and `h` the outer answer. The seed is `ρ̃ ‖ re`
(the sampler's and `Enc`'s coins), the adversary runs on `pk = fst z`, the output is `r` flagged
entries and `σ` (`r·(ctLen + 1) + sl` bits, `simFin`), and the finalization may ask one query (it
asks none), so that T2's budget is at least `1`. -/
def simParams (r sl : PolyExpr) : ChalParams S pl hl 1 (fun _ => pl) (fun _ => hl) where
  j := 0
  seedLen := samp.coins.add S.enc.coins
  advIn ctx := pairFstD (pairFstD (pairSndD ctx))
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  qry w := EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)
  qry_poly := EnsembleLemmas.polyTimeComputable_padL pl polyTimeComputable_rd.1
    polyTimeComputable_rd.2.2.2.2.2.1
  qry_len _ := EnsembleLemmas.length_padL _ _
  ansY := simCt S samp
  ansY_poly := polyTimeComputable_simCt S samp
  ansY_len _ := EnsembleLemmas.length_padL _ _
  ansH w := EnsembleLemmas.padL (hl.eval (rdU w).length) (rdAns w)
  ansH_poly := EnsembleLemmas.polyTimeComputable_padL hl polyTimeComputable_rd.1
    polyTimeComputable_rd.2.2.2.2.2.2.2
  ansH_len _ := EnsembleLemmas.length_padL _ _
  outLen := (r.mul (S.ctLen.add (.const 1))).add sl
  finCall := .const 1
  finRun := simFin S r
  finRun_poly := polyTimeComputable_simFin S r

attribute [simps (config := { isSimp := false }) j seedLen advIn qry ansY ansH outLen finCall
  finRun] simParams

section Run

variable (r sl : PolyExpr) (n : ℕ)

/-- The simulator's seed is `ρ̃ ‖ re`: `seedLen = samp.coins + enc.coins`. -/
theorem simParams_seedLen_handler :
    (chalHandler (simParams S samp pl hl r sl)).seedLen = samp.coins.add S.enc.coins := by
  rw [chalHandler_seedLen, simParams_seedLen]

/-- The simulator outputs `r·(ctLen + 1) + sl` bits. -/
theorem simParams_outLen_eval :
    (chalHandler (simParams S samp pl hl r sl)).outLen.eval n =
      r.eval n * (S.ctLen.eval n + 1) + sl.eval n := by
  rw [chalHandler_outLen, simParams_outLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_const]

/-- The simulator runs `A` on `pk`: `advInput n ⟨pk, α⟩ ω = pk`. -/
theorem simParams_advInput (pk α : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) :
    (chalHandler (simParams S samp pl hl r sl)).advInput n (pairEncode pk α) ω = pk := by
  rw [InteractiveHandler.advInput_eq, chalHandler_advIn, simParams_advIn, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode]

/-- **The simulator's finalization** on `A`'s output `a` (`r·ctLen + sl` bits) returns
`simOutL` of the state and `a`, asking nothing. -/
theorem simFinish (z : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
    (s : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) (hd : d = r.eval n * S.ctLen.eval n + sl.eval n) :
    (chalHandler (simParams S samp pl hl r sl)).finish n z ω s a =
      .pure (padFin _ (simOutL S r n (List.ofFn s) (List.ofFn a))) := by
  have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [List.length_ofFn, hd]
  refine finish_of_ret _ n z ω s a _ ?_ ?_
  · rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ fun i hi => ?_]
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [length_flagF, length_chunkAt _ _ _ (by
        rw [ha]
        have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
        omega)]
  · rw [chalHandler_finRun, simParams_finRun]
    exact simFin_finInput S r sl n z _ _ _ _ ha

end Run

/-! ### The simulator against the history oracle -/

section Composite

variable (hist : List Bool → List Bool) (r sl : PolyExpr) (n : ℕ)

/-- **The abstraction of the hybrid's state** to the simulator's and the history oracle's: no
challenge is `(empty, none)`; the challenge `y` on `a` is `(⟨y, h(M(a; ρ)), a⟩, some a)`. -/
def simAbs (ρ : samp.Coins n) :
    Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) →
      (Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) ×
        Option (Fin (pl.eval n) → Bool)
  | none => (chalState (simParams S samp pl hl r sl) n none, none)
  | some (y, a) => (chalState (simParams S samp pl hl r sl) n
      (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)), some a)

/-- `simAbs … none = (chalState none, none)`. -/
theorem simAbs_none (ρ : samp.Coins n) :
    simAbs S samp pl hl hist r sl n ρ none =
      (chalState (simParams S samp pl hl r sl) n none, none) := rfl

/-- `simAbs … (some (y, a)) = (chalState (some (y, h(M(a; ρ)), a)), some a)`. -/
theorem simAbs_some (ρ : samp.Coins n) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    simAbs S samp pl hl hist r sl n ρ (some (y, a)) =
      (chalState (simParams S samp pl hl r sl) n
        (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
        some a) := rfl

/-- The history oracle's part of the abstraction is the recorded parameter. -/
theorem simAbs_snd (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (simAbs S samp pl hl hist r sl n ρ s).2 = s.map Prod.snd := by
  cases s with
  | none => rfl
  | some ya => rfl

/-- **The dummy challenge in a round of the simulator** (input `⟨pk, M.advice n⟩`, seed
`ρ̃ ‖ re`, on
the parameter `x`): `simCt … = ⟦Enc_pk(M(x; ρ̃); re)⟧`. -/
theorem simCt_input (pk : List Bool) (ρ' : samp.Coins n) (re : S.enc.Coins n) (s : List Bool)
    (x : Fin ((snmDin S pl 1).eval n) → Bool) (L : List Bool) :
    simCt S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s
        (1 : Fin 2) (List.ofFn x) L) =
      List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re) := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -⟩ := fields_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hxl : (List.ofFn x).length = pl.eval n := by
    rw [List.length_ofFn]
    show (snmDin S pl 1).eval n = _
    rw [snmDin_one]
  rw [simCt_eq, simMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairFstD_pairEncode,
    pairSndD_pairEncode, seedEquiv_ofFn,
    List.take_left' (length_ofFn_coins samp n ρ'), List.drop_left' (length_ofFn_coins samp n ρ'),
    encWith_eq, drawWith_eq, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
    GGMRed.ofFn_padFin_of_length hxl, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]

/-- **The simulator against the history oracle is the hybrid with an independent draw:** for the
input `⟨pk, M.advice n⟩` and the seed `ρ̃ ‖ re`, the composition of the history oracle (coins `ρ`)
with the simulator's handler, from the abstracted state, is `rImpl … true … ρ ρ̃ (some re)` (under
CPA) with its state abstracted (`simAbs`).

**Proof sketch.** Query by query: `Dec` is `⊥` on both sides (`chalHandler_impl_dec`,
`rImpl_dec_cpa`); a repeated challenge repeats `⟨y, h(M(a; ρ))⟩` (`chalHandler_impl_some`,
`rImpl_some`); a first challenge asks `a`, receives `h(M(a; ρ))` (`histImpl_eq`) and answers
`⟨Enc_pk(M(a; ρ̃); re), h(M(a; ρ))⟩` (`chalHandler_impl_none`, `simCt_input`,
`rImpl_none_eager`). -/
theorem simComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    ((histImpl S samp pl hl hist n ρ).comp ((chalHandler (simParams S samp pl hl r sl)).impl n
        (pairEncode pk (samp.advice n))
        (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))))
        i x (simAbs S samp pl hl hist r sl n ρ s) =
      (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re) i x s).bind
        fun p => .pure (p.1, simAbs S samp pl hl hist r sl n ρ p.2) := by
  rw [QueryImpl.comp_apply]
  match i, x, s with
  | 0, x, none =>
    rw [simAbs_none, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_none]
  | 0, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_some, simulate_pure, OracleComp.pure_bind, rImpl_some,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, none =>
    have hxl : (List.ofFn x).length = pl.eval n := by
      rw [List.length_ofFn]
      show (snmDin S pl 1).eval n = _
      rw [snmDin_one]
    have hq : ∀ (s' : List Bool) (L : List Bool),
        (simParams S samp pl hl r sl).qry
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) L) = List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
      intro s' L
      rw [simParams_qry, (fields_input (k := 2) n _ _ s' 1 _ L).1,
        (fields_input (k := 2) n _ _ s' 1 _ L).2.2.2.2.2.1, List.length_replicate,
        ofFn_padFin_eq_padL]
    have hH : ∀ (s' q : List Bool) (y : Fin (hl.eval n) → Bool),
        (simParams S samp pl hl r sl).ansH
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) (pairEncode (pairEncode (List.replicate 0 true)
            (pairEncode q (List.ofFn y))) [])) = List.ofFn y := by
      intro s' q y
      rw [simParams_ansH, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
        rdAns_input, EnsembleLemmas.padL_eq]
      exact List.take_left' List.length_ofFn
    rw [simAbs_none, chalHandler_impl_none, simulate_query, histImpl_eq, OracleComp.pure_bind,
      simulate_pure, OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind, simAbs_some,
      if_pos rfl]
    simp only [simParams_j, simParams_ansY, Fin.val_zero, hq, hH, simCt_input, Option.getD_none,
      padFin_ofFn (padFin (pl.eval n) (List.ofFn x)),
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re),
      padFin_ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ))]

/-- **The ideal view of the simulator's output is the hybrid's view of `A`'s output:** for `A`'s
output `a` (`r·ctLen + sl` bits) and the hybrid's final state `s`, `idealView` of the simulator's
output (flags from the abstracted state) with the history oracle's state is `realView` of `a` and
`s`.

**Proof sketch.** Entry `i` of the output is `flagF ⟨1^n, st⟩ c_i` (`chunkAt_flatten_append`), whose
flag is `[c_i = y]` for the recorded `y` and `false` without a challenge (`headD_ofFn_chalState`,
`ofFn_chalState_some`), as `realView`'s copy test; `σ` is the tail (`drop_flatten_append`). -/
theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (a : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin
        ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)
        (simOutL S r n (List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1) a)))
        (simAbs S samp pl hl hist r sl n ρ s).2 =
      realView S samp pl n (r.eval n) sk ρ a s := by
  set st := List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1 with hst
  have hc : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_chunkAt _ _ _ (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hg : ∀ i < r.eval n, (flagF S (pairEncode (List.replicate n true) st)
      (chunkAt (S.ctLen.eval n) i a)).length = S.ctLen.eval n + 1 := fun i hi => by
    rw [length_flagF, hc i hi]
  have hlen : (simOutL S r n st a).length =
      (chalHandler (simParams S samp pl hl r sl)).outLen.eval n := by
    rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ hg, Nat.mul_add, Nat.mul_one]
    omega
  rw [GGMRed.ofFn_padFin_of_length hlen, simAbs_snd, idealView_eq, realView_eq, simOutL_eq,
    drop_flatten_append _ _ _ hg]
  congr 3
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [chunkAt_flatten_append _ _ _ hg _ _ hi, flagF_eq, List.headD_cons, List.tail_cons,
    pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
  congr 1
  cases s with
  | none =>
    rw [hst, simAbs_none, headD_ofFn_chalState]
    simp
  | some ya =>
    obtain ⟨y, a'⟩ := ya
    rw [hst, simAbs_some, ofFn_chalState_some, List.headD_cons, List.drop_one, List.tail_cons,
      List.append_assoc, List.take_left' List.length_ofFn]
    simp only [Bool.true_and, Option.map_some, Option.some.injEq, decide_eq_decide]
    exact eq_comm

end Composite

/-! ### The ideal experiment is the hybrid `H_true` -/

section Ideal

variable (hist : List Bool → List Bool) (A : NUPPT) (q r sl : PolyExpr)

/-- **One run of the simulator is one run of the hybrid `H_true`:** let `Sim₀` be T2's machine of
the simulator's handler (coin bijection `φ`). For the input `⟨pk, M.advice n⟩`, coins
`φ (ρ̃ ‖ re, rA)` and budget `1`, the law of `F(idealView)` over `Sim₀`'s run against the history
oracle (coins `ρ`) is the law of `F(realView)` over `A`'s run (coins `rA`) against
`rImpl … true … ρ ρ̃ (some re)`.

**Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); the run at budget `1` is
the run at T2's budget (`toCompOn_budget_eq`: the handler asks at most one query,
`chalHandler_costBoundedBy`, and its finalization none, `simFinish`); T2's equation; the
composition of the two simulations (`simulate_bind`, `simulate_comp`) is the hybrid's run through
the abstraction (`simulate_eq_of_abs`, `simComp_abs`); the views agree (`idealView_simOut`). -/
theorem simRun_eq (Sim₀ : NUPPT) (n : ℕ)
    (φ : (Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) × A.Coins n ≃
      Sim₀.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
      (rA : A.Coins n),
      (simulate ((chalHandler (simParams S samp pl hl r sl)).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (((r.mul S.ctLen).add sl).eval n)) n (q.eval n)
            ((chalHandler (simParams S samp pl hl r sl)).advInput n z ω) rA)
          ((chalHandler (simParams S samp pl hl r sl)).init n)).bind
          (fun res => (chalHandler (simParams S samp pl hl r sl)).finish n z ω res.2 res.1) =
        Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)) n
          (q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
            (chalHandler (simParams S samp pl hl r sl)).finCall.eval n) z (φ (ω, rA)))
    (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (rA : A.Coins n)
    (F : List Bool → ℝ) :
    ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r.eval n * (S.ctLen.eval n + 1) + sl.eval n)) n 1 (pairEncode pk (samp.advice n))
          (φ (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re), rA))) none)
        (fun p => F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) =
      ProbComp.expect (simulate (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re))
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r.eval n * S.ctLen.eval n + sl.eval n)) n (q.eval n) pk rA) none)
        (fun p => F (realView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) := by
  set ω := seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re) with hω
  set z := pairEncode pk (samp.advice n) with hz
  have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hfin : ∀ (st : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool)
      (a : Fin (((r.mul S.ctLen).add sl).eval n) → Bool),
      (chalHandler (simParams S samp pl hl r sl)).finish n z ω st a =
        .pure (padFin _ (simOutL S r n (List.ofFn st) (List.ofFn a))) :=
    fun st a => simFinish S samp pl hl r sl n z ω st a hdα
  -- The output length, the budget and T2.
  refine (expect_toCompOn_outLen _ Sim₀ n 1 z _ none
    (simParams_outLen_eval S samp pl hl r sl n).symm
    (fun p => F (idealView S samp pl n (r.eval n) sk ρ p.1 p.2))).trans ?_
  have hK : 1 ≤ q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
      (chalHandler (simParams S samp pl hl r sl)).finCall.eval n := by
    rw [chalHandler_finCall, simParams_finCall, PolyExpr.eval_const]
    omega
  rw [toCompOn_budget_eq Sim₀ _ n 1 _ z (φ (ω, rA)) hK (by
    rw [← hφ z ω rA, chalHandler_init]
    refine OracleComp.CostBoundedBy.bind (q₁ := 1) (q₂ := 0) (chalHandler_costBoundedBy _ n z ω _)
      fun res => ?_
    rw [hfin]
    exact OracleComp.costBoundedBy_pure _ _ _), ← hφ z ω rA, simParams_advInput, chalHandler_init,
    simulate_bind,
    simulate_comp, ← simAbs_none S samp pl hl hist r sl n ρ,
    simulate_eq_of_abs _ _ _ (simComp_abs S samp pl hl hist r sl n pk sk ρ ρ' re),
    OracleComp.bind_assoc, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, hfin, simulate_pure]
  rw [ProbComp.expect_bind]
  simp only [ProbComp.expect_pure]
  refine (expect_toCompOn_outLen _ A n (q.eval n) pk rA none hdα fun p =>
    F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin _ (simOutL S r n
      (List.ofFn (simAbs S samp pl hl hist r sl n ρ p.2).1) p.1)))
      (simAbs S samp pl hl hist r sl n ρ p.2).2)).trans ?_
  refine congrArg _ (funext fun p => ?_)
  rw [idealView_simOut S samp pl hl hist r sl n sk ρ p.2 _ (by
    rw [List.length_ofFn])]

/-- **The simulator exists:** for the sampler `samp` (parameter length `pl`, history `hist` of
length `hl`), the adversary `A` and the polynomials `q`, `r`, `sl`, there is a machine `Sim` whose
ideal acceptance rate (budget `1`) is, for every distinguisher and every `n`, the hybrid `H_true`'s
(under CPA).

**Proof sketch.** `Sim₀` is T2's machine of the simulator's handler and `Sim` hard-wires
`M.advice n` as the second input component (`exists_withAdviceOn`). Reindex `Sim`'s coins as
`(ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`, `seedEquiv`, `expect_sample_prod`), draw the hybrid's encryption
coins in advance (`expect_simulate_rImpl_eager`) and reorder the samples (`expect_sample_comm`);
pointwise this is `simRun_eq`. -/
theorem exists_simulator : ∃ Sim : NUPPT, ∀ (X : NUPPT) (n : ℕ),
    idealAcc S samp pl hl hist Sim (r.eval n) (sl.eval n) X n =
      hybAcc S .cpa true samp pl hl hist A (q.eval n) (r.eval n) (sl.eval n) X n := by
  obtain ⟨Sim₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
    (fun _ : Fin 1 => pl) (fun _ => hl) ((r.mul S.ctLen).add sl)
    (chalHandler (simParams S samp pl hl r sl))
  obtain ⟨Sim, hc, hSim⟩ := NMCCA2.exists_withAdviceOn Sim₀ samp.advice samp.adv
    samp.advice_length
  refine ⟨Sim, fun X n => ?_⟩
  obtain ⟨φ, hφ⟩ := hT2 n
  rw [idealAcc_eq, hybAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr hc n)]
  simp only [hSim]
  rw [← ChallengeSim.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
    ← ChallengeSim.expect_sample_equiv (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ' => ?_)
  simp only [expect_simulate_rImpl_eager]
  refine (congrArg _ (funext fun re => congrArg _ (funext fun rA => congrArg _ (funext fun rX =>
    simRun_eq S samp pl hl hist A q r sl Sim₀ n φ hφ _ _ ρ ρ' re rA fun v =>
      if X.distinguisherL n v rX = true then 1 else 0)))).trans ?_
  rw [ChallengeSim.expect_sample_comm]
  refine congrArg _ (funext fun rA => ?_)
  rw [ChallengeSim.expect_sample_comm]

end Ideal

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The NM adversary of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message), under CPA.
The NM adversary `B` runs the SIM adversary `A` on `pk`, answering `Dec` with `⊥`. On `A`'s first
challenge `a` it draws `m = M(a; ρ)` and `m̃ = M(a; ρ̃)` with its own coins (and `M`'s advice, from
its input `⟨pk, α_M⟩`), asks its own challenge on `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)` and answers
`A` with `⟨y, h(m)⟩`, recording `⟨y, h(m), a⟩`. It outputs, for each of `A`'s ciphertexts `c_i`,
`c_i` followed by the pair `Enc_pk(f^{msgLen})`, `Enc_pk((¬f)^{msgLen})` for the copy flag
`f = [c_i = y]`, and then the same pair for each bit of `a`, `m = M(a; ρ)` and `σ` (one encryption
tape `re` for all of them).

It is the challenge handler (`chalHandler`) with the parameters `nmParams`. Against `NM_b`'s
oracles, its run is `A`'s run against the hybrid oracle `rImpl … b …` (`nmComp_abs`).

## Main definitions

* `NMSim.altMsg`: `m̃` read from a round input.
* `NMSim.encBit`, `NMSim.encPair`, `NMSim.encF`, `NMSim.bitF`, `NMSim.nmOutL`, `NMSim.nmFin`:
  the finalization.
* `NMSim.nmParams`, `NMSim.nmLen`: the parameters and the number of output ciphertexts.

## Main results

* `NMSim.nmFinish`, `NMSim.nmComp_abs`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (finU finZ finW finA fields_finInput polyTimeComputable_finFields)

variable (S : FixedLengthPKScheme) (samp : NUPPT)

/-! ### The challenge pair -/

/-- The second message `m̃ = M(a; ρ̃)` read in a round `w`: as `simMsg`, with the coins `ρ̃` after
the first `coins(n)` bits of the seed. -/
def altMsg (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
    (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
      (((rdW w).drop (samp.coins.eval (rdU w).length)).take (samp.coins.eval (rdU w).length))))

/-- `altMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
theorem altMsg_eq (w : List Bool) :
    altMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
      (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
        (((rdW w).drop (samp.coins.eval (rdU w).length)).take
          (samp.coins.eval (rdU w).length)))) := rfl

/-- The second message is polynomial-time. -/
theorem polyTimeComputable_altMsg : PolyTimeComputable (altMsg S samp) := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -, -⟩ := polyTimeComputable_rd
  have hd : PolyTimeComputable fun w => (rdW w).drop (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hρ : PolyTimeComputable fun w =>
      ((rdW w).drop (samp.coins.eval (rdU w).length)).take (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hd)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU hQ (polyTimeComputable_pairSndD.comp hZ) hρ))

/-! ### The finalization -/

/-- The bit encryption `Enc_pk(x^{msgLen}; re)` on the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`: `pk = fst z`
and `re` the seed after its first `2·coins(n)` bits, padded to `ctLen(n)` bits. -/
def encBit (ctx : List Bool) (x : Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (pairFstD ctx).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (pairFstD ctx)
      (pairEncode (pairFstD (pairFstD (pairSndD ctx)))
        (List.replicate (S.msgLen.eval (pairFstD ctx).length) x))) [])
      ((pairFstD (pairSndD (pairSndD ctx))).drop
        ((samp.coins.add samp.coins).eval (pairFstD ctx).length))))

/-- `encBit S samp ctx x = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, x^{msgLen}⟩⟩, []⟩, re⟩)`. -/
theorem encBit_eq (ctx : List Bool) (x : Bool) :
    encBit S samp ctx x = EnsembleLemmas.padL (S.ctLen.eval (pairFstD ctx).length)
      (S.enc.output (pairEncode (pairEncode (pairEncode (pairFstD ctx)
        (pairEncode (pairFstD (pairFstD (pairSndD ctx)))
          (List.replicate (S.msgLen.eval (pairFstD ctx).length) x))) [])
        ((pairFstD (pairSndD (pairSndD ctx))).drop
          ((samp.coins.add samp.coins).eval (pairFstD ctx).length)))) := rfl

/-- **The encoding of a bit** `x`: `Enc_pk(x^{msgLen}) ‖ Enc_pk((¬x)^{msgLen})`. -/
def encPair (ctx : List Bool) (x : Bool) : List Bool :=
  encBit S samp ctx x ++ encBit S samp ctx (!x)

/-- `encPair S samp ctx x = encBit ctx x ++ encBit ctx (¬x)`. -/
theorem encPair_eq (ctx : List Bool) (x : Bool) :
    encPair S samp ctx x = encBit S samp ctx x ++ encBit S samp ctx (!x) := rfl

/-- The state `s` of the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`. -/
def ctxSt (ctx : List Bool) : List Bool := pairSndD (pairSndD (pairSndD ctx))

/-- `ctxSt ctx = pairSndD (pairSndD (pairSndD ctx))`. -/
theorem ctxSt_eq (ctx : List Bool) : ctxSt ctx = pairSndD (pairSndD (pairSndD ctx)) := rfl

/-- **A ciphertext with its copy flag**: `c` followed by the encoding of
`[flag ∧ c = y]`, with `s = [flag] ‖ y ‖ …` the state of the context. -/
def encF (ctx c : List Bool) : List Bool :=
  c ++ encPair S samp ctx ((ctxSt ctx).headD false &&
    decide (c = ((ctxSt ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length)))

/-- `encF S samp ctx c = c ++ encPair ctx [flag ∧ c = y]`. -/
theorem encF_eq (ctx c : List Bool) :
    encF S samp ctx c = c ++ encPair S samp ctx ((ctxSt ctx).headD false &&
      decide (c = ((ctxSt ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) := rfl

/-- **A bit of the view**, encoded: `bitF ctx b = encPair ctx (b.headD false)`. -/
def bitF (ctx b : List Bool) : List Bool := encPair S samp ctx (b.headD false)

/-- `bitF S samp ctx b = encPair ctx (b.headD false)`. -/
theorem bitF_eq (ctx b : List Bool) : bitF S samp ctx b = encPair S samp ctx (b.headD false) := rfl

/-- The bit encryption is polynomial-time, for a computed context and bit. -/
theorem polyTimeComputable_encBit {u : List Bool → List Bool} {x : List Bool → Bool}
    (hu : PolyTimeComputable u) (hx : PolyTimeComputable fun z => [x z]) :
    PolyTimeComputable fun z => encBit S samp (u z) (x z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable fun z => pairFstD (u z) := hF.comp hu
  have hrep : PolyTimeComputable fun z =>
      List.replicate (S.msgLen.eval (pairFstD (u z)).length) (x z) :=
    (polyTimeComputable_ite hx ((polyTimeComputable_unaryPoly S.msgLen).comp hU)
      (EnsembleLemmas.polyTimeComputable_zeros S.msgLen hU)).congr fun z => by
        cases x z <;> rfl
  have hre : PolyTimeComputable fun z => (pairFstD (pairSndD (pairSndD (u z)))).drop
      ((samp.coins.add samp.coins).eval (pairFstD (u z)).length) :=
    ((polyTimeComputable_pairDropPoly (samp.coins.add samp.coins)).comp
      (hU.pairEncode (hF.comp (hD.comp (hD.comp hu))))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
    (((hU.pairEncode ((hF.comp (hF.comp (hD.comp hu))).pairEncode hrep)).pairEncode
      (polyTimeComputable_const [])).pairEncode hre))

/-- The encoding of a bit is polynomial-time, for a computed context and bit. -/
theorem polyTimeComputable_encPair {u : List Bool → List Bool} {x : List Bool → Bool}
    (hu : PolyTimeComputable u) (hx : PolyTimeComputable fun z => [x z]) :
    PolyTimeComputable fun z => encPair S samp (u z) (x z) :=
  (polyTimeComputable_encBit S samp hu hx).append
    (polyTimeComputable_encBit S samp hu (polyTimeComputable_not hx))

/-- `encF` is polynomial-time, as a function of `⟨ctx, c⟩`. -/
theorem polyTimeComputable_encF :
    PolyTimeComputable fun z => encF S samp (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hst : PolyTimeComputable fun z => ctxSt (pairFstD z) := hD.comp (hD.comp (hD.comp hF))
  have hy : PolyTimeComputable fun z =>
      ((ctxSt (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp ((hF.comp hF).pairEncode
      (polyTimeComputable_tail.comp hst))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun z => [decide (pairSndD z =
      ((ctxSt (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length))] :=
    (polyTimeComputable_pairEq.comp (hD.pairEncode hy)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact hD.append (polyTimeComputable_encPair S samp hF
    (polyTimeComputable_and (polyTimeComputable_headD.comp hst) heq))

/-- `bitF` is polynomial-time, as a function of `⟨ctx, b⟩`. -/
theorem polyTimeComputable_bitF :
    PolyTimeComputable fun z => bitF S samp (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPair S samp polyTimeComputable_pairFstD
    (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)

variable (pl hl : PolyExpr)

/-- **The NM adversary's output** at parameter `n` on the context `ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, for
`A`'s output `a` (`r(n)` ciphertexts, then `σ`), the recorded parameter `aP` and the message `mP`:
`encF ctx c_i` for each ciphertext, then `encPair ctx x` for each bit `x` of `aP ‖ mP ‖ σ`. -/
def nmOutL (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) : List Bool :=
  ((List.range (r.eval n)).map fun i => encF S samp ctx (chunkAt (S.ctLen.eval n) i a)).flatten ++
    ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x => encPair S samp ctx x).flatten

/-- `nmOutL S samp r n ctx a aP mP = (encF ctx c_i)_i ++ (encPair ctx x)_{x ∈ aP ‖ mP ‖ σ}`. -/
theorem nmOutL_eq (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) :
    nmOutL S samp r n ctx a aP mP =
      ((List.range (r.eval n)).map fun i =>
        encF S samp ctx (chunkAt (S.ctLen.eval n) i a)).flatten ++
        ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x =>
          encPair S samp ctx x).flatten := rfl

/-- The parameter recorded in a state `[flag] ‖ y ‖ h ‖ a` (`1 + (ctLen + hl)` bits before `a`). -/
def stParam (n : ℕ) (st : List Bool) : List Bool :=
  st.drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval n)

/-- `stParam S hl n st = st.drop (1 + (ctLen(n) + hl(n)))`. -/
theorem stParam_eq (n : ℕ) (st : List Bool) :
    stParam S hl n st = st.drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval n) := rfl

/-- The message `M(aP; ρ)` of the finalization, with the advice `α` and the seed `ω` (`ρ` its first
`coins(n)` bits). -/
def finMsg (n : ℕ) (α ω aP : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval n)
    (samp.output (NUPPT.layout (List.replicate n true) aP α (ω.take (samp.coins.eval n))))

/-- `finMsg S samp n α ω aP = padL msgLen(n) (M.output (layout 1^n aP α ρ))`. -/
theorem finMsg_eq (n : ℕ) (α ω aP : List Bool) :
    finMsg S samp n α ω aP = EnsembleLemmas.padL (S.msgLen.eval n)
      (samp.output (NUPPT.layout (List.replicate n true) aP α (ω.take (samp.coins.eval n)))) := rfl

/-- **The NM adversary's finalization round**: `⟨[true], chunkMap ctLen encF ⟨ctx, a.take (r·ctLen)⟩
‖ chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩⟩`, with `ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩` and
no outer query. -/
def nmFin (r : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode [true]
    (chunkMap S.ctLen (encF S samp)
        (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
          ((finA w).take ((r.mul S.ctLen).eval (finU w).length))) ++
      chunkMap (.const 1) (bitF S samp)
        (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
          ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) ++
            EnsembleLemmas.padL (S.msgLen.eval (finU w).length)
              (samp.output (NUPPT.layout (finU w)
                ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length))
                (pairSndD (finZ w)) ((finW w).take (samp.coins.eval (finU w).length)))) ++
            (finA w).drop ((r.mul S.ctLen).eval (finU w).length))))

/-- `nmFin S samp hl r w = ⟨[true], E ‖ B⟩`, with `E = chunkMap ctLen encF ⟨ctx, a.take (r·ctLen)⟩`
and `B = chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩`, where
`ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, `aP = s.drop (1 + ctLen + hl)`, `ρ = ω.take coins` and
`M(aP; ρ) = padL msgLen (M.output (layout 1^n aP (snd z) ρ))`. -/
theorem nmFin_eq (r : PolyExpr) (w : List Bool) :
    nmFin S samp hl r w = pairEncode [true]
      (chunkMap S.ctLen (encF S samp)
          (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
            ((finA w).take ((r.mul S.ctLen).eval (finU w).length))) ++
        chunkMap (.const 1) (bitF S samp)
          (pairEncode (pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))))
            ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) ++
              EnsembleLemmas.padL (S.msgLen.eval (finU w).length)
                (samp.output (NUPPT.layout (finU w)
                  ((finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length))
                  (pairSndD (finZ w)) ((finW w).take (samp.coins.eval (finU w).length)))) ++
              (finA w).drop ((r.mul S.ctLen).eval (finU w).length)))) := rfl

/-- The finalization round is polynomial-time.

**Proof sketch.** From the polynomial-time field readers (`polyTimeComputable_finFields`,
`polyTimeComputable_finSt`): the context by `pairEncode`; the cuts of `a` at `r·ctLen`, the
parameter `aP` and the coins `ρ` by `pairTakePoly`/`pairDropPoly`; the message by
`polyTimeComputable_padL` of `M`'s output on `layout`. The two chunk maps are
`polyTimeComputable_chunkMap` of `encF` and `bitF`, joined by `append` and `pairEncode`. -/
theorem polyTimeComputable_nmFin (r : PolyExpr) : PolyTimeComputable (nmFin S samp hl r) := by
  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
  have hS := polyTimeComputable_finSt
  have hctx : PolyTimeComputable fun w =>
      pairEncode (finU w) (pairEncode (finZ w) (pairEncode (finW w) (finSt w))) :=
    hU.pairEncode (hZ.pairEncode (hW.pairEncode hS))
  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have haP : PolyTimeComputable fun w =>
      (finSt w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (finU w).length) :=
    ((polyTimeComputable_pairDropPoly ((PolyExpr.const 1).add (S.ctLen.add hl))).comp
      (hU.pairEncode hS)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hρ : PolyTimeComputable fun w => (finW w).take (samp.coins.eval (finU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hm := EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU haP (polyTimeComputable_pairSndD.comp hZ) hρ))
  exact (polyTimeComputable_const [true]).pairEncode
    (((polyTimeComputable_chunkMap S.ctLen (polyTimeComputable_encF S samp)).comp
      (hctx.pairEncode htake)).append
      ((polyTimeComputable_chunkMap (.const 1) (polyTimeComputable_bitF S samp)).comp
        (hctx.pairEncode ((haP.append hm).append hdrop))))

/-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits, and
`ctLen(n) > 0`) returns `⟨[true], nmOutL …⟩`.

**Proof sketch.** Read the fields of the input in `nmFin_eq` (`fields_finInput`,
`finSt_finInput`). Cut `a.take (r·ctLen)` into its `r` chunks of `ctLen(n) > 0` bits
(`take_eq_flatten_chunkAt`, `length_chunkAt`), so the first chunk map is `encF` over them
(`chunkMap_flatten`). Write `aP ‖ M(aP; ρ) ‖ σ` as the flatten of its singletons, so the second,
with chunk length `1`, is `bitF` over its bits; both match `nmOutL_eq`. -/
theorem nmFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) (hct : 0 < S.ctLen.eval n) :
    nmFin S samp hl r (InteractiveHandler.finInput n z ω s a L) =
      pairEncode [true] (nmOutL S samp r n
        (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω s))) a (stParam S hl n s)
        (finMsg S samp n (pairSndD z) ω (stParam S hl n s))) := by
  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z ω s a L
  have hbits : ∀ l : List Bool, l = (l.map fun x => [x]).flatten := by
    intro l
    induction l with
    | nil => rfl
    | cons x t ih => rw [List.map_cons, List.flatten_cons, ← ih]; rfl
  rw [nmFin_eq, hU, hZ, hW, hA, finSt_finInput, List.length_replicate, PolyExpr.eval_mul,
    take_eq_flatten_chunkAt,
    chunkMap_flatten _ _ n _ _ (fun ch hch => ?_) hct, List.map_map, nmOutL_eq, stParam_eq,
    finMsg_eq]
  · congr 1
    rw [hbits (List.drop _ s ++ _ ++ _), chunkMap_flatten _ _ n _ _ (fun ch hch => ?_)
      (by rw [PolyExpr.eval_const]; omega), List.map_map, ← hbits]
    · rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hch
      rw [PolyExpr.eval_const, List.length_singleton]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
    rw [List.mem_range] at hi
    refine length_chunkAt _ _ _ ?_
    rw [ha]
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
    omega

/-! ### The handler -/

/-- **The number of the NM adversary's ciphertexts**: `3r` (each of `A`'s ciphertexts with the
encoding of its copy flag) and `2(pl + msgLen + sl)` (the encodings of `a`, `m`, `σ`). -/
def nmLen (r sl : PolyExpr) : PolyExpr :=
  ((PolyExpr.const 3).mul r).add ((PolyExpr.const 2).mul ((pl.add S.msgLen).add sl))

/-- `nmLen S pl r sl = 3·r + 2·(pl + msgLen + sl)`. -/
theorem nmLen_eval (r sl : PolyExpr) (n : ℕ) :
    (nmLen S pl r sl).eval n = 3 * r.eval n + 2 * (pl.eval n + S.msgLen.eval n + sl.eval n) := by
  rw [nmLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]

variable (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist)

/-- **The parameters of the NM adversary's handler** (on the real experiment's oracles with
parameter length `pl` and history `hist` of length `hl`; the outer oracles are those of
Definition 171.5 on T2's lengths): the first challenge `a` asks the challenge `⟨m, m̃⟩`
(oracle `1`),
with `m = M(a; ρ)` (`simMsg`) and `m̃ = M(a; ρ̃)` (`altMsg`); it answers `⟨y, h(m)⟩` with `y` the
outer answer. The seed is `ρ ‖ ρ̃ ‖ re`, the adversary runs on `pk = fst z`, the output is `nmLen`
ciphertexts (`nmFin`), and the finalization asks nothing. -/
def nmParams (r sl : PolyExpr) :
    ChalParams S pl hl 2 (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) where
  j := 1
  seedLen := samp.coins.add (samp.coins.add S.enc.coins)
  advIn ctx := pairFstD (pairFstD (pairSndD ctx))
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  qry w := EnsembleLemmas.padL ((S.msgLen.add S.msgLen).eval (rdU w).length)
    (simMsg S samp w ++ altMsg S samp w)
  qry_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
    ((polyTimeComputable_simMsg S samp).append (polyTimeComputable_altMsg S samp))
  qry_len w := by rw [EnsembleLemmas.length_padL, snmDin_one]
  ansY w := EnsembleLemmas.padL (S.ctLen.eval (rdU w).length) (rdAns w)
  ansY_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
    polyTimeComputable_rd.2.2.2.2.2.2.2
  ansY_len _ := EnsembleLemmas.length_padL _ _
  ansH w := EnsembleLemmas.padL (hl.eval (rdU w).length) (hist (simMsg S samp w))
  ansH_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rd.1
    (hist_poly.comp (polyTimeComputable_simMsg S samp))
  ansH_len _ := EnsembleLemmas.length_padL _ _
  outLen := (nmLen S pl r sl).mul S.ctLen
  finCall := .const 0
  finRun := nmFin S samp hl r
  finRun_poly := polyTimeComputable_nmFin S samp hl r

attribute [simps (config := { isSimp := false }) j seedLen advIn qry ansY ansH outLen finCall
  finRun] nmParams

section Run

variable (r sl : PolyExpr) (n : ℕ)

/-- The NM adversary's seed is `ρ ‖ (ρ̃ ‖ re)`. -/
theorem nmParams_seedLen_handler :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen =
      samp.coins.add (samp.coins.add S.enc.coins) := by
  rw [chalHandler_seedLen, nmParams_seedLen]

/-- The NM adversary outputs `nmLen · ctLen` bits. -/
theorem nmParams_outLen_eval :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n =
      (nmLen S pl r sl).eval n * S.ctLen.eval n := by
  rw [chalHandler_outLen, nmParams_outLen, PolyExpr.eval_mul]

/-- The NM adversary runs `A` on `pk`: `advInput n ⟨pk, α⟩ ω = pk`. -/
theorem nmParams_advInput (pk α : List Bool)
    (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool) :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).advInput n (pairEncode pk α) ω =
      pk := by
  rw [InteractiveHandler.advInput_eq, chalHandler_advIn, nmParams_advIn, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode]

/-- The bit encryptions have `ctLen(n)` bits. -/
theorem length_encBit (n : ℕ) (e : List Bool) (x : Bool) :
    (encBit S samp (pairEncode (List.replicate n true) e) x).length = S.ctLen.eval n := by
  rw [encBit_eq, EnsembleLemmas.length_padL, pairFstD_pairEncode, List.length_replicate]

/-- **The NM adversary outputs `nmLen` ciphertexts:** for `A`'s output of `r·ctLen + sl` bits, a
parameter of `pl` bits and a message of `msgLen` bits, `|nmOutL …| = nmLen · ctLen`. -/
theorem length_nmOutL (e a aP mP : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n)
    (haP : aP.length = pl.eval n) (hmP : mP.length = S.msgLen.eval n) :
    (nmOutL S samp r n (pairEncode (List.replicate n true) e) a aP mP).length =
      (nmLen S pl r sl).eval n * S.ctLen.eval n := by
  rw [nmLen_eval, nmOutL_eq, List.length_append,
    length_flatten_map_range (S.ctLen.eval n + 2 * S.ctLen.eval n) _ _ fun i hi => ?_,
    length_flatten_map_const _ _ (2 * S.ctLen.eval n) fun x => ?_, List.length_append,
    List.length_append, List.length_drop, ha, haP, hmP]
  · rw [Nat.add_sub_cancel_left]
    ring
  · rw [encPair_eq, List.length_append, length_encBit, length_encBit]
    ring
  · rw [encF_eq, encPair_eq, List.length_append, List.length_append, length_encBit,
      length_encBit, length_chunkAt _ _ _ (by
        rw [ha]
        have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
        omega)]
    ring

/-- **The NM adversary's finalization** on `A`'s output `a` (`r·ctLen + sl` bits, `ctLen(n) > 0`)
returns `nmOutL` on the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, asking nothing. -/
theorem nmFinish (z : List Bool)
    (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
    (s : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool)
    {d : ℕ} (a : Fin d → Bool) (hd : d = r.eval n * S.ctLen.eval n + sl.eval n)
    (hct : 0 < S.ctLen.eval n) :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω s a =
      .pure (padFin _ (nmOutL S samp r n
        (pairEncode (List.replicate n true) (pairEncode z (pairEncode (List.ofFn ω) (List.ofFn s))))
        (List.ofFn a) (stParam S hl n (List.ofFn s))
        (finMsg S samp n (pairSndD z) (List.ofFn ω) (stParam S hl n (List.ofFn s))))) := by
  have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [List.length_ofFn, hd]
  refine finish_of_ret _ n z ω s a _ ?_ ?_
  · have hs : (List.ofFn s).length = 1 + (S.ctLen.eval n + hl.eval n) + pl.eval n := by
      rw [List.length_ofFn, chalHandler_stateLen_eval]
    rw [nmParams_outLen_eval, length_nmOutL S samp pl r sl n _ _ _ _ ha ?_ ?_]
    · rw [stParam_eq, List.length_drop, hs, PolyExpr.eval_add, PolyExpr.eval_add,
        PolyExpr.eval_const]
      omega
    · rw [finMsg_eq, EnsembleLemmas.length_padL]
  · rw [chalHandler_finRun, nmParams_finRun]
    exact nmFin_finInput S samp hl r sl n z _ _ _ _ ha hct

end Run

/-! ### The NM adversary against `NM_b`'s oracles -/

section Composite

variable (r sl : PolyExpr) (n : ℕ)

/-- The NM adversary's seed for the coins `ρ`, `ρ̃` and `re`: `ρ ‖ (ρ̃ ‖ re)`. -/
def nmSeed (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool :=
  seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n
    (ρ, seedEquiv (A := samp) (B := S.enc) rfl n (ρ', re))

/-- `nmSeed … ρ ρ̃ re = seedEquivPoly _ n (ρ, seedEquiv rfl n (ρ̃, re))`. -/
theorem nmSeed_eq (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re =
      seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n
        (ρ, seedEquiv (A := samp) (B := S.enc) rfl n (ρ', re)) := rfl

/-- `⟦nmSeed … ρ ρ̃ re⟧ = ⟦ρ⟧ ++ (⟦ρ̃⟧ ++ ⟦re⟧)`. -/
theorem nmSeed_ofFn (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re) =
      List.ofFn ρ ++ (List.ofFn ρ' ++ List.ofFn re) := by
  rw [nmSeed, seedEquivPoly_ofFn, seedEquiv_ofFn]

/-- **The messages of a round of the NM adversary** (input `⟨pk, M.advice n⟩`, seed `ρ ‖ ρ̃ ‖ re`,
parameter `xs` of `pl(n)` bits): `m = M(xs; ρ)` and `m̃ = M(xs; ρ̃)`. -/
theorem nmMsgs_input (pk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (s : List Bool)
    (i : Fin 2) (xs L : List Bool) (hxs : xs.length = pl.eval n) :
    simMsg S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L) =
      List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) xs) ρ) ∧
    altMsg S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L) =
      List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) xs) ρ') := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -⟩ := fields_input n (pairEncode pk (samp.advice n))
    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
  have hρ := length_ofFn_coins samp n ρ
  have hρ' := length_ofFn_coins samp n ρ'
  rw [simMsg_eq, altMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairSndD_pairEncode,
    nmSeed_ofFn, List.take_left' hρ, List.drop_left' hρ, List.take_left' hρ', drawWith_eq,
    drawWith_eq, GGMRed.ofFn_padFin_of_length hxs, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
    NUPPT.runAt_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.runAtL_eq_output_layout]
  exact ⟨rfl, rfl⟩

/-- The challenge pair `⟨M(a; ρ), M(a; ρ̃)⟩` asked on the parameter `a`. -/
def nmPair (ρ ρ' : samp.Coins n) (a : Fin (pl.eval n) → Bool) :
    Fin ((S.msgLen.add S.msgLen).eval n) → Bool :=
  padFin _ (List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ'))

/-- `nmPair … ρ ρ̃ a = padFin _ (⟦M(a; ρ)⟧ ++ ⟦M(a; ρ̃)⟧)`. -/
theorem nmPair_eq (ρ ρ' : samp.Coins n) (a : Fin (pl.eval n) → Bool) :
    nmPair S samp pl n ρ ρ' a = padFin _ (List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ) ++
      List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ')) := rfl

/-- **The abstraction of the hybrid's state** to the NM adversary's and `NM_b`'s: no challenge is
`(empty, none)`; the challenge `y` on `a` is
`(⟨y, h(M(a; ρ)), a⟩, some (y, ⟨M(a; ρ), M(a; ρ̃)⟩))`. -/
def nmAbs (ρ ρ' : samp.Coins n) :
    Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) →
      (Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool) ×
        Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))
  | none => (chalState (nmParams S samp pl hl hist hist_poly r sl) n none, none)
  | some (y, a) => (chalState (nmParams S samp pl hl hist hist_poly r sl) n
      (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
      some (y, nmPair S samp pl n ρ ρ' a))

/-- `nmAbs … none = (chalState none, none)`. -/
theorem nmAbs_none (ρ ρ' : samp.Coins n) :
    nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' none =
      (chalState (nmParams S samp pl hl hist hist_poly r sl) n none, none) := rfl

/-- `nmAbs … (some (y, a)) = (chalState (some (y, h(M(a; ρ)), a)), some (y, nmPair a))`. -/
theorem nmAbs_some (ρ ρ' : samp.Coins n) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' (some (y, a)) =
      (chalState (nmParams S samp pl hl hist hist_poly r sl) n
        (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
        some (y, nmPair S samp pl n ρ ρ' a)) := rfl

/-- `NM_b`'s part of the abstraction records the hybrid's challenge ciphertext. -/
theorem nmAbs_snd_fst (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).2.map Prod.fst = s.map Prod.fst := by
  cases s with
  | none => rfl
  | some ya => rfl

/-- **The NM adversary against `NM_b`'s oracles is the hybrid `H_b`:** for the input
`⟨pk, M.advice n⟩` and the seed `ρ ‖ ρ̃ ‖ re`, the composition of `NM_b`'s oracles (the hybrid
oracle
with the sampler `halfSamp` and its coin `b`, under CPA) with the NM adversary's handler, from the
abstracted state, is `rImpl … b … ρ ρ̃ none` with its state abstracted (`nmAbs`).

**Proof sketch.** Query by query: `Dec` is `⊥` on both sides; a repeated challenge repeats
`⟨y, h(M(a; ρ))⟩`; a first challenge asks `⟨M(a; ρ), M(a; ρ̃)⟩` (`nmMsgs_input`), whose half `b` is
`M(a; ρ_b)` (`ofFn_drawWith_half`), so the challenge ciphertext is `Enc_pk(M(a; ρ_b))` with the same
lazily drawn coins, and answers it with `h(M(a; ρ))`. -/
theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (b : Bool)
    (ρ'' : (halfSamp S).Coins n) (i : Fin 2) (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    ((rImpl S .cpa false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) n pk sk
        ((halfCoins S n).symm b) ρ'' none).comp
        ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).impl n
          (pairEncode pk (samp.advice n)) (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)))
        i x (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s) =
      (rImpl S .cpa b samp pl hl hist n pk sk ρ ρ' none i x s).bind
        fun p => .pure (p.1, nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2) := by
  rw [QueryImpl.comp_apply]
  match i, x, s with
  | 0, x, none =>
    rw [nmAbs_none, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, nmAbs_none]
  | 0, x, some (y, a) =>
    rw [nmAbs_some, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, nmAbs_some]
  | 1, x, some (y, a) =>
    rw [nmAbs_some, chalHandler_impl_some, simulate_pure, OracleComp.pure_bind, rImpl_some,
      OracleComp.pure_bind, nmAbs_some]
  | 1, x, none =>
    have hxl : (List.ofFn x).length = pl.eval n := by
      rw [List.length_ofFn]
      show (snmDin S pl 1).eval n = _
      rw [snmDin_one]
    have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
      PolyExpr.eval_add _ _ _
    have hq : ∀ (s' L : List Bool), (nmParams S samp pl hl hist hist_poly r sl).qry
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x) L) =
        List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) := by
      intro s' L
      obtain ⟨hm, hm'⟩ := nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1
        (List.ofFn x) L hxl
      rw [nmParams_qry, (fields_input (k := 2) n _ _ s' 1 _ L).1, List.length_replicate, hm, hm',
        nmPair_eq, ofFn_padFin_eq_padL]
    have hH : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansH
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x)
          (pairEncode (pairEncode (List.replicate ((1 : Fin 2) : ℕ) true) (pairEncode q t))
            [])) =
        List.ofFn (histWith hist (hl.eval n)
          (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x)) ρ)) := by
      intro s' q t
      rw [nmParams_ansH, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
        (nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1 (List.ofFn x) _ hxl).1,
        histWith_eq, ofFn_padFin_eq_padL]
    have hY : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansY
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x)
          (pairEncode (pairEncode (List.replicate ((1 : Fin 2) : ℕ) true) (pairEncode q t))
            [])) =
        EnsembleLemmas.padL (S.ctLen.eval n) t := by
      intro s' q t
      rw [nmParams_ansY, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
        rdAns_input]
    have hdraw : ∀ re' : S.enc.Coins n, encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
        (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) ((halfCoins S n).symm b)) re' =
        encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re' := by
      intro re'
      have hlen : (List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
            ρ)
          ++ List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
            ρ')).length = (S.msgLen.add S.msgLen).eval n := by
        rw [List.length_append, List.length_ofFn, List.length_ofFn, hpl]
      rw [encWith_eq, encWith_eq, ofFn_drawWith_half S n _ hpl, nmPair_eq,
        GGMRed.ofFn_padFin_of_length hlen]
      cases b
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
          List.take_left' List.length_ofFn]
      · rw [if_pos rfl, if_pos rfl, List.drop_left' List.length_ofFn]
    have h0 : ∀ m : Fin (S.msgLen.eval n) → Bool,
        List.ofFn (histWith (fun _ => []) ((PolyExpr.const 0).eval n) m) = [] := fun m =>
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
    rw [nmAbs_none, chalHandler_impl_none, nmParams_j, simulate_query, rImpl_none_lazy,
      rImpl_none_lazy, OracleComp.bind_assoc, OracleComp.bind_assoc, OracleComp.bind_assoc]
    refine congrArg _ (funext fun re' => ?_)
    have hx' : List.ofFn (padFin ((snmDin S (S.msgLen.add S.msgLen) 1).eval n)
        (List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))))) =
        List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, snmDin_one])
    have hlen : (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re') ++ []).length =
        (snmDout S (.const 0) 1).eval n := by
      rw [List.append_nil, List.length_ofFn, snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const,
        Nat.add_zero]
    have hans := GGMRed.ofFn_padFin_of_length hlen
    rw [rImpl_none_eager, rImpl_none_eager]
    simp only [OracleComp.pure_bind, simulate_pure, nmAbs_some, Bool.false_eq_true, ↓reduceIte, hq]
    rw [hx', padFin_ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))), hdraw, h0]
    simp only [hH, hY]
    rw [hans, List.append_nil, ← ofFn_padFin_eq_padL,
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re'),
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re'),
      padFin_ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ))]

end Composite

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Recover.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The NM distinguisher of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message). The NM
experiment hands its distinguisher the decryptions of the NM adversary's ciphertexts (`⊥` on a copy
of the challenge). The distinguisher `recDist S D` reads back the SIM experiment's view
`(a, m, (d_i)_i, σ)` from them and runs `D` on it:
* each of `A`'s ciphertexts comes with the encoding of its copy flag: the entry `d_i` is `COPY` if
  the flag is set, and the decryption otherwise (`entF`);
* each bit `x` of `a`, `m`, `σ` is encoded by `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})`; by
  correctness at most one of them is the challenge, and `guessBit` reads `x` from the two
  decryptions (`guessBit_encPair`).

## Main definitions

* `NMSim.entF`, `NMSim.bitG`, `NMSim.recView`: the reading of the view.
* `NMSim.recDist`: the distinguisher.

## Main results

* `NMSim.recDist_distinguisherL`, `NMSim.nmOutput_flatten`, `NMSim.guessBit_encPair`,
  `NMSim.recView_nmOutL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused)

variable (S : FixedLengthPKScheme)

/-! ### Reading the view -/

/-- `guessBit` is polynomial-time (DL-30–36 overlap: the content of the private
`polyTimeComputable_guessFun` of `Indistinguishability/Encrypt.lean`, on the bare string). -/
theorem polyTimeComputable_guessBit : PolyTimeComputable fun w => [guessBit w] :=
  (polyTimeComputable_ite polyTimeComputable_headD
    (polyTimeComputable_headD.comp polyTimeComputable_tail)
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp BinArith.polyTimeComputable_reverse))).congr fun w => by
    rw [guessBit_eq]
    split <;> rfl

/-- **An entry read back** from the decryptions `v ‖ v₁ ‖ v₂` (`msgLen(n) + 1` bits each) of a
ciphertext and the encoding of its copy flag, on the context `⟨1^n, _⟩`: `COPY` if
`guessBit (v₁ ‖ v₂)`,
and `false` followed by `v` otherwise. -/
def entF (ctx ch : List Bool) : List Bool :=
  if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
    true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
  else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)

/-- `entF S ctx ch =
if guessBit (ch.drop (msgLen + 1)) then COPY else false :: ch.take (msgLen + 1)`. -/
theorem entF_eq (ctx ch : List Bool) :
    entF S ctx ch =
      if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
        true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
      else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) := rfl

/-- **A bit read back** from the decryptions of its encoding: `[guessBit ch]`. -/
def bitG (_ctx ch : List Bool) : List Bool := [guessBit ch]

/-- `bitG ctx ch = [guessBit ch]`. -/
theorem bitG_eq (ctx ch : List Bool) : bitG ctx ch = [guessBit ch] := rfl

/-- `entF` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_entF : PolyTimeComputable fun z => entF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD (pairFstD z)) (pairSndD z) :=
    (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun z =>
      (pairSndD z).drop ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairDropPoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun z =>
      (pairSndD z).take ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact polyTimeComputable_ite (polyTimeComputable_guessBit.comp hdrop)
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [true])
      (EnsembleLemmas.polyTimeComputable_zeros (S.msgLen.add (.const 1)) (hF.comp hF)))
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [false]) htake)

/-- `bitG` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_bitG : PolyTimeComputable fun z => bitG (pairFstD z) (pairSndD z) :=
  polyTimeComputable_guessBit.comp polyTimeComputable_pairSndD

variable (pl : PolyExpr) (r sl : PolyExpr)

/-- **The view read back** on the parameter string `U = 1^n` from the decryptions `u`: the entries
`E` (`chunkMap` of `entF` over the first `r` groups of three decryptions) and the bits `B`
(`chunkMap`
of `bitG` over the remaining pairs); the view is `B.take pl ‖ (B.drop pl).take msgLen ‖ E ‖
B.drop (pl + msgLen)`. -/
def recView (U u : List Bool) : List Bool :=
  (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).take
      (pl.eval U.length) ++
    ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      (pl.eval U.length)).take (S.msgLen.eval U.length) ++
    chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
      (pairEncode (pairEncode U [])
        (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
    (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      ((pl.add S.msgLen).eval U.length)

/-- `recView S pl r U u = B.take pl ++ (B.drop pl).take msgLen ++ E ++ B.drop (pl + msgLen)`. -/
theorem recView_eq (U u : List Bool) :
    recView S pl r U u =
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).take (pl.eval U.length) ++
        ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop (pl.eval U.length)).take (S.msgLen.eval U.length) ++
        chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
          (pairEncode (pairEncode U [])
            (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
        (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop ((pl.add S.msgLen).eval U.length) := rfl

/-- The reading of the view is polynomial-time, as a function of `⟨U, u⟩`.

**Proof sketch.** The chunk maps `B` (of `bitG`, on the `drop` of `u` after the `r` groups) and
`E` (of `entF`, on the matching `take`) are `polyTimeComputable_chunkMap` composed with
`pairTakePoly`/`pairDropPoly`. The three pieces of `B` cut `⟨U, B⟩` the same way (`take pl`,
`take msgLen` of `drop pl`, `drop (pl + msgLen)`), and `recView_eq` joins the four parts by
`append`. -/
theorem polyTimeComputable_recView :
    PolyTimeComputable fun z => recView S pl r (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : ∀ p : PolyExpr,
      PolyTimeComputable (fun z => (pairSndD z).take (p.eval (pairFstD z).length)) ∧
      PolyTimeComputable (fun z => (pairSndD z).drop (p.eval (pairFstD z).length)) := fun p =>
    ⟨polyTimeComputable_pairTakePoly p, polyTimeComputable_pairDropPoly p⟩
  have hctx : PolyTimeComputable fun z => pairEncode (pairFstD z) ([] : List Bool) :=
    hF.pairEncode (polyTimeComputable_const [])
  have hB : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ polyTimeComputable_bitG).comp
      (hctx.pairEncode (hcut _).2)
  have hE : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ (polyTimeComputable_entF S)).comp
      (hctx.pairEncode (hcut _).1)
  have hBU : ∀ p : PolyExpr, PolyTimeComputable (fun z => pairEncode (pairFstD z)
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))))) := fun _ => hF.pairEncode hB
  have h1 : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).take (pl.eval (pairFstD z).length) :=
    ((hcut pl).1.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2a : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length) :=
    ((hcut pl).2.comp (hBU pl)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2 : PolyTimeComputable fun z =>
      ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length)).take
        (S.msgLen.eval (pairFstD z).length) :=
    ((hcut S.msgLen).1.comp (hF.pairEncode h2a)).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h3 : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop ((pl.add S.msgLen).eval (pairFstD z).length) :=
    ((hcut (pl.add S.msgLen)).2.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (((h1.append h2).append hE).append h3).congr fun z => by rw [recView_eq]

variable (D : NUPPT)

/-- `recDist`'s raw function on `⟨⟨⟨1^n, u⟩, α⟩, ρ⟩`: `D`'s output (advice `α`, coins `ρ`) on the
view read back from `u`. -/
private def recFun (z : List Bool) : List Bool :=
  D.output (NUPPT.layout (NUPPT.inParam z) (recView S pl r (NUPPT.inParam z) (NUPPT.inArg z))
    (NUPPT.inAdvice z) (NUPPT.inCoins z))

/-- The raw function is polynomial-time. -/
private theorem polyTimeComputable_recFun : PolyTimeComputable (recFun S pl r D) :=
  D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_recView S pl r).comp (NUPPT.polyTimeComputable_inParam.pairEncode
      NUPPT.polyTimeComputable_inArg) |>.congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)

/-- **The NM distinguisher** built from `D`, with `D`'s coins and advice: it reads the SIM view back
from the decryptions (`recView`) and runs `D` on it. -/
noncomputable def recDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_recFun S pl r D) D.coins D.adv D.advice D.advice_length

/-- The NM distinguisher has `D`'s coins. -/
theorem recDist_coins : (recDist S pl r D).coins = D.coins := by
  rw [recDist, NUPPT.coins_ofPolyTime]

/-- **The NM distinguisher's verdict** on the decryptions `u`, with `D`'s coins `rD` carried over,
is `D`'s verdict on the view read back: `recDist.distinguisherL n u rD = D.distinguisherL n
(recView 1^n u) rD`. -/
theorem recDist_distinguisherL (n : ℕ) (u : List Bool) (rD : D.Coins n) :
    (recDist S pl r D).distinguisherL n u (NUPPT.coinsCongr (recDist_coins S pl r D).symm n rD) =
      D.distinguisherL n (recView S pl r (List.replicate n true) u) rD := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n u) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) u (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, recDist, NUPPT.runAtL_ofPolyTime, recFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-! ### The view is read back -/

/-- **The decryptions of concatenated ciphertexts:** for `ℓ` ciphertexts `cs` of `ctLen(n)` bits,
`nmOutput sk s' (padFin _ cs.flatten)` is the concatenation of the entries' tails
`(entryL … [c is the challenge] c).drop 1` (`nmOutput_eq_entryTails`, `map_chunkAt_flatten`). -/
theorem nmOutput_flatten (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (cs : List (List Bool)) (hℓ : cs.length = ℓ) (hc : ∀ c ∈ cs, c.length = S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) cs.flatten) =
      (cs.map fun c => (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1).flatten := by
  have hlen : cs.flatten.length = ℓ * S.ctLen.eval n := by
    rw [List.length_flatten, ← hℓ]
    have : cs.map List.length = cs.map fun _ => S.ctLen.eval n := List.map_congr_left hc
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [nmOutput_eq_entryTails S n ℓ sk s' _ hlen, ← hℓ,
    map_chunkAt_flatten (S.ctLen.eval n) (fun c => (entryL S n sk
      (decide (s'.map List.ofFn = some c)) c).drop 1) cs hc]

variable (samp : NUPPT)

/-- **The ciphertexts are not empty** when the messages are not: with `msgLen(n) > 0`, correctness
gives `ctLen(n) > 0` (two different messages cannot both decrypt from the empty ciphertext). -/
theorem ctLen_pos (n : ℕ) (rg : S.gen.Coins n) (re : S.enc.Coins n) (hL : 0 < S.msgLen.eval n) :
    0 < S.ctLen.eval n := by
  by_contra h
  have h0 : S.ctLen.eval n = 0 := by omega
  have hnil : ∀ m : Fin (S.msgLen.eval n) → Bool,
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re = [] := fun m =>
    List.eq_nil_of_length_eq_zero ((S.enc_length n rg m re).trans h0)
  have h₁ := S.correct n (fun _ => true) rg re
  have h₂ := S.correct n (fun _ => false) rg re
  rw [hnil] at h₁ h₂
  have := congrFun (Option.some.inj (h₁.symm.trans h₂)) ⟨0, hL⟩
  exact absurd this (by decide)

/-- **The encoding of a bit is read back** from its decryptions: under generated keys, with
`msgLen(n) > 0`, for the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` with `pk = fst z` and the tape `re` after
`2·coins(n)` bits of `ω`, `guessBit (v(Enc_pk(x^{msgLen})) ‖ v(Enc_pk((¬x)^{msgLen}))) = x`, where
`v c` is the decryption of `c` in the NM output (`⊥` on the challenge `s'`).

**Proof sketch.** The two ciphertexts decrypt to `x^{msgLen}` and `(¬x)^{msgLen}` (correctness), so
they differ and at most one is the challenge: `guessBit_valid` or `guessBit_refused`. -/
theorem guessBit_encPair (n : ℕ) (rg : S.gen.Coins n) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (hL : 0 < S.msgLen.eval n) (z ω st : List Bool)
    (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg))
    (re : S.enc.Coins n) (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (x : Bool) :
    guessBit ((entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) x)))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
          x)).drop 1 ++
      (entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) (!x))))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
          (!x))).drop 1) = x := by
  have henc : ∀ y,
      encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
      y = S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re := by
    intro y
    rw [encBit_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hω, hz, List.ofFn_const,
      EnsembleLemmas.padL_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq]
    refine List.take_left' ?_
    have := S.enc_length n rg (fun _ => y) re
    rw [NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq, List.ofFn_const] at this
    exact this
  have hdec : ∀ y, decodeFin (S.msgLen.eval n) (S.dec (pairEncode (pairSndD (S.gen.runAt n [] rg))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re))) = some fun _ => y :=
    fun y => S.correct n _ rg re
  have hne : S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
      (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re ≠
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re := by
    intro heq
    have h₁ := hdec x
    rw [heq, hdec (!x)] at h₁
    have := congrFun (Option.some.inj h₁) ⟨0, hL⟩
    cases x <;> exact absurd this (by decide)
  rw [henc, henc, entryL_drop_one, entryL_drop_one, hdec, hdec]
  by_cases h : s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
    (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re)
  · have h' : ¬ s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re) := by
      rw [h]
      exact fun h'' => hne (Option.some.inj h'')
    rw [if_pos (decide_eq_true h), if_neg (by simpa using h'), ← ofFn_zeroBits]
    exact guessBit_refused hL x
  · rw [if_neg (by simpa using h)]
    exact guessBit_valid hL x _

/-- **The view is read back from the NM output** (under generated keys, `msgLen(n) > 0`): for the
NM adversary's output on the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` (`A`'s output `a`, the parameter `aP`,
the message `mP`), whose copy flags agree with the challenge `s'` (`hflag`), `recView` of the
decryptions is `aP ‖ mP ‖ (d_i)_i ‖ σ` with `d_i = entryL … [c_i is the challenge] c_i`.

**Proof sketch.** The output is a concatenation of `ctLen(n)`-bit ciphertexts
(`nmOutput_flatten`): for each `c_i`, its decryption and those of its flag's encoding; for each bit
of `aP ‖ mP ‖ σ`, the decryptions of its encoding. `entF` turns each group of three into `d_i`
(`guessBit_encPair`, `hflag`) and `bitG` each pair into its bit (`chunkMap_flatten`). -/
theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
    (s' : Option (Fin (S.ctLen.eval n) → Bool)) (z ω st a aP mP : List Bool)
    (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg)) (re : S.enc.Coins n)
    (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) (haP : aP.length = pl.eval n)
    (hmP : mP.length = S.msgLen.eval n)
    (hflag : ∀ c : List Bool, (st.headD false && decide (c = (st.drop 1).take (S.ctLen.eval n))) =
      decide (s'.map List.ofFn = some c)) :
    recView S pl r (List.replicate n true) (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) s'
        (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (nmOutL S samp r n
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) a aP mP))) =
      aP ++ mP ++ ((List.range (r.eval n)).map fun i => entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
        (chunkAt (S.ctLen.eval n) i a)).flatten ++ a.drop (r.eval n * S.ctLen.eval n) := by
  set sk := pairSndD (S.gen.runAt n [] rg) with hsk
  set ctx := pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)) with hctx
  set v : List Bool → List Bool := fun c =>
    (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1 with hvdef
  set f : ℕ → Bool := fun i => st.headD false &&
    decide (chunkAt (S.ctLen.eval n) i a = (st.drop 1).take (S.ctLen.eval n)) with hfdef
  set bits := aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n) with hbits
  have hct := ctLen_pos S n rg re hL
  have hci : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_chunkAt _ _ _ (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hv : ∀ c, (v c).length = S.msgLen.eval n + 1 := fun c => by
    rw [hvdef, List.length_drop, length_entryL]
    omega
  have he : ∀ x, (encBit S samp ctx x).length = S.ctLen.eval n := fun x =>
    length_encBit S samp n _ x
  set cs : List (List Bool) := ((List.range (r.eval n)).map fun i =>
      [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)]).flatten ++
    (bits.map fun x => [encBit S samp ctx x, encBit S samp ctx (!x)]).flatten with hcs
  have hW : nmOutL S samp r n ctx a aP mP = cs.flatten := by
    rw [nmOutL_eq, hcs, List.flatten_append, List.flatten_flatten, List.flatten_flatten,
      List.map_map, List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, encF_eq, encPair_eq, ctxSt_eq, hctx]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.flatten_cons,
        List.flatten_nil, List.append_nil, hfdef]
    · refine List.map_congr_left fun x _ => ?_
      rw [Function.comp_apply, encPair_eq]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  have hcs_len : cs.length = (nmLen S pl r sl).eval n := by
    rw [hcs, List.length_append, List.length_flatten, List.length_flatten, List.map_map,
      List.map_map]
    have h3 : (List.map (List.length ∘ fun i =>
        [chunkAt (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)])
        (List.range (r.eval n))) = List.replicate (r.eval n) 3 := by
      rw [List.eq_replicate_iff, List.length_map, List.length_range]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    have h2 : (List.map (List.length ∘ fun x => [encBit S samp ctx x, encBit S samp ctx (!x)])
        bits) = List.replicate bits.length 2 := by
      rw [List.eq_replicate_iff, List.length_map]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    rw [h3, h2, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul, nmLen_eval, hbits,
      List.length_append, List.length_append, List.length_drop, haP, hmP, ha]
    omega
  have hcs_ct : ∀ c ∈ cs, c.length = S.ctLen.eval n := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      rw [List.mem_range] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact hci i hi
      · exact he _
      · exact he _
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact he _
      · exact he _
  rw [hW, nmOutput_flatten S n _ sk s' cs hcs_len hcs_ct]
  have hP : (cs.map v).flatten =
      ((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten ++
      (bits.map fun x => v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))).flatten := by
    rw [hcs, List.map_append, List.flatten_append, List.map_flatten, List.map_flatten,
      List.flatten_flatten, List.flatten_flatten, List.map_map, List.map_map, List.map_map,
      List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
    · refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
  have h3 : ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n =
      3 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h2 : ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))).eval n =
      2 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h1 : (S.msgLen.add (.const 1)).eval n = S.msgLen.eval n + 1 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  have hg3 : ∀ i < r.eval n, (v (chunkAt (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).length =
      ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n := fun i _ => by
    rw [List.length_append, List.length_append, hv, hv, hv, h3]
    ring
  have hP1 : (((List.range (r.eval n)).map fun i => v (chunkAt (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten).length =
      (r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval n := by
    rw [length_flatten_map_range _ _ _ hg3]
    exact (PolyExpr.eval_mul _ _ _).symm
  rw [hP, recView_eq, List.length_replicate, List.take_left' hP1, List.drop_left' hP1,
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hch
      rw [List.length_append, hv, hv, h2]
      ring) (by rw [h2]; omega),
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      exact hg3 i (List.mem_range.1 hi)) (by rw [h3]; omega), List.map_map, List.map_map]
  have hB : (bits.map (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
      v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x)))).flatten = bits := by
    have hx : ∀ x, (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
        v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))) x = [x] := by
      intro x
      rw [Function.comp_apply, bitG_eq, hvdef]
      exact congrArg (· :: []) (guessBit_encPair S samp n rg s' hL z ω st hz re hω x)
    have hfl : ∀ l : List Bool, (l.map fun x => [x]).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x t ih => rw [List.map_cons, List.flatten_cons, ih]; rfl
    rw [List.map_congr_left (fun x _ => hx x), hfl]
  have hE : (List.range (r.eval n)).map (entF S (pairEncode (List.replicate n true) []) ∘ fun i =>
      v (chunkAt (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))) =
      (List.range (r.eval n)).map fun i => entryL S n sk
        (decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)))
        (chunkAt (S.ctLen.eval n) i a) := by
    refine List.map_congr_left fun i _ => ?_
    have hg : guessBit (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i))) = f i := by
      rw [hvdef]
      exact guessBit_encPair S samp n rg s' hL z ω st hz re hω (f i)
    have hf : f i = decide (s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)) := hflag _
    rw [Function.comp_apply, entF_eq, pairFstD_pairEncode, List.length_replicate, h1,
      List.drop_left' (hv _), List.take_left' (hv _), hg, hf, entryL_eq]
    by_cases hc : s'.map List.ofFn = some (chunkAt (S.ctLen.eval n) i a)
    · rw [if_pos (decide_eq_true hc), if_pos (decide_eq_true hc)]
    · rw [if_neg (by simpa using hc), if_neg (by simpa using hc), hvdef]
      simp only [hc, decide_false, entryL_eq, Bool.false_eq_true, ↓reduceIte, List.drop_one,
        List.tail_cons]
  rw [hB, hE, hbits, PolyExpr.eval_add]
  have hmP' : (aP ++ mP).length = pl.eval n + S.msgLen.eval n := by
    rw [List.length_append, haP, hmP]
  rw [List.append_assoc aP mP, List.take_left' (by rw [haP]), List.drop_left' (by rw [haP]),
    List.take_left' hmP, ← List.append_assoc, List.drop_left' hmP']

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-malleability implies SIM-NME′ under CPA: the NM games are the hybrids

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message). For the NM
adversary `B` (T2's machine of `nmParams`, with `M`'s advice hard-wired) and the distinguisher
`recDist S pl r X`, the experiment `NM_b` accepts with the probability of the hybrid `H_b`
(`hybAcc … b …`) whenever `msgLen(n) > 0` (`exists_nmAdversary`). With `H_false` the real
experiment and `H_true` the ideal one (`Simulator.lean`), the SIM advantage is `B`'s NM advantage.

## Main results

* `NMSim.recView_nmOut`: the view read back from `B`'s NM output is the hybrid's view.
* `NMSim.nmRun_eq`: one run of `NM_b` is one run of `H_b`.
* `NMSim.exists_nmAdversary`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (simulate_eq_of_abs)

variable (S : FixedLengthPKScheme) (samp : NUPPT) (pl hl : PolyExpr)
  (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist) (r sl : PolyExpr)

/-! ### The view -/

section View

variable (n : ℕ)

/-- **The NM adversary's recorded parameter** is the hybrid's: `stParam` of the abstracted state is
`⟦a⟧` for the challenge on `a`, and `0^{pl}` without a challenge. -/
theorem stParam_nmAbs (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1) =
      List.ofFn ((s.map Prod.snd).getD (zeroBits _)) := by
  have hs : ((PolyExpr.const 1).add (S.ctLen.add hl)).eval n =
      1 + (S.ctLen.eval n + hl.eval n) := by
    rw [PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_const]
  cases s with
  | none =>
    rw [nmAbs_none, ofFn_chalState_none, stParam_eq, List.drop_replicate, chalHandler_stateLen_eval,
      hs, Option.map_none, Option.getD_none, ofFn_zeroBits]
    congr 1
    omega
  | some ya =>
    obtain ⟨y, a⟩ := ya
    rw [nmAbs_some, ofFn_chalState_some, stParam_eq, hs, Option.map_some, Option.getD_some,
      Nat.add_comm 1, List.drop_succ_cons,
      List.drop_left' (by rw [List.length_append, List.length_ofFn, List.length_ofFn])]

/-- **The NM adversary's copy flags are the hybrid's copy test:** for the abstracted state `st` and
every string `c`, `[flag ∧ c = y] = [c is the hybrid's recorded challenge]`. -/
theorem flag_nmAbs (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (c : List Bool) :
    ((List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1).headD false &&
      decide (c = ((List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1).drop 1).take
        (S.ctLen.eval n))) = decide ((s.map Prod.fst).map List.ofFn = some c) := by
  cases s with
  | none =>
    rw [nmAbs_none, headD_ofFn_chalState]
    simp
  | some ya =>
    obtain ⟨y, a⟩ := ya
    rw [nmAbs_some, ofFn_chalState_some, List.headD_cons, List.drop_one, List.tail_cons,
      List.append_assoc, List.take_left' List.length_ofFn]
    simp only [Bool.true_and, Option.map_some, Option.some.injEq, decide_eq_decide]
    exact eq_comm

/-- **The view read back from the NM adversary's output is the hybrid's view** (under generated
keys, `msgLen(n) > 0`): for the hybrid's final state `s` and `A`'s output `a`, `recView` of the
decryptions of `B`'s output (on the abstracted state, the input `⟨pk, M.advice n⟩` and the seed
`ρ ‖ ρ̃ ‖ re`) is `realView` of `a` and `s`.

**Proof sketch.** `recView_nmOutL`, with the copy flags `flag_nmAbs`, the parameter `stParam_nmAbs`
and the message `M(a; ρ)` read from the seed (`nmSeed_ofFn`). -/
theorem recView_nmOut (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n) (ρ ρ' : samp.Coins n)
    (re : S.enc.Coins n) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)))
    (a : List Bool) (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    recView S pl r (List.replicate n true) (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
        ((nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).2.map Prod.fst)
        (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn (padFin
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n)
          (nmOutL S samp r n (pairEncode (List.replicate n true)
            (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
              (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
                (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)))) a
            (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))
            (finMsg S samp n
              (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
              (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
              (stParam S hl n
                (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)))))))) =
      realView S samp pl n (r.eval n) (pairSndD (S.gen.runAt n [] rg)) ρ a s := by
  have hω := nmSeed_ofFn S samp pl hl hist hist_poly r sl n ρ ρ' re
  have haP :
      (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1)).length =
      pl.eval n := by
    rw [stParam_nmAbs, List.length_ofFn]
  have hmP : (finMsg S samp n
      (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
      (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
      (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))).length =
      S.msgLen.eval n := by
    rw [finMsg_eq, EnsembleLemmas.length_padL]
  have hlen := length_nmOutL S samp pl r sl n
    (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
      (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
        (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).1))) a _ _ ha haP hmP
  rw [← nmParams_outLen_eval S samp pl hl hist hist_poly r sl n] at hlen
  rw [GGMRed.ofFn_padFin_of_length hlen, nmAbs_snd_fst,
    recView_nmOutL S pl r sl samp n rg hL (s.map Prod.fst) _ _ _ a _ _
      (pairFstD_pairEncode _ _) re
      (by rw [hω, PolyExpr.eval_add, ← List.append_assoc, List.drop_left' (by
        rw [List.length_append, length_ofFn_coins, length_ofFn_coins])]) ha haP hmP
      (flag_nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s),
    realView_eq, stParam_nmAbs, finMsg_eq, pairSndD_pairEncode, hω,
    List.take_left' (length_ofFn_coins samp n ρ), drawWith_eq, ofFn_padFin_eq_padL,
    samp.runAt_eq, samp.runAtL_eq_output_layout]

end View

/-! ### `NM_b` is the hybrid `H_b` -/

section Games

variable (A : NUPPT) (q : PolyExpr)

/-- **One run of `NM_b` is one run of the hybrid `H_b`** (under generated keys, `msgLen(n) > 0`):
let `B₀` be T2's machine of the NM adversary's handler (coin bijection `φ`). For the input
`⟨pk, M.advice n⟩` and coins `φ (ρ ‖ ρ̃ ‖ re, rA)`, the law of `recDist X`'s verdict over `B₀`'s run
against `NM_b`'s oracles is the law of `X`'s verdict on `realView` over `A`'s run (coins `rA`)
against `rImpl … b … ρ ρ̃ none`.

**Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); T2's equation; the
finalization asks nothing (`nmFinish`); the composition of the two simulations is the hybrid's
run through the abstraction (`simulate_comp`, `simulate_eq_of_abs`, `nmComp_abs`); the views agree
(`recDist_distinguisherL`, `recView_nmOut`). -/
theorem nmRun_eq (B₀ : NUPPT) (n : ℕ)
    (φ : (Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B₀.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
      (rA : A.Coins n),
      (simulate ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (((r.mul S.ctLen).add sl).eval n)) n (q.eval n)
            ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).advInput n z ω) rA)
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).init n)).bind
          (fun res => (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω
            res.2 res.1) =
        B₀.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n)
          ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n)) n
          (q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
            (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n) z (φ (ω, rA)))
    (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n)
    (rA : A.Coins n) (b : Bool) (ρ'' : (halfSamp S).Coins n) (X : NUPPT) (rX : X.Coins n) :
    ProbComp.expect (simulate (rImpl S .cpa false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0)
          (fun _ => []) n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
          ((halfCoins S n).symm b) ρ'' none)
        (B₀.toCompOn (bitCodec (fun j => (snmDin S (S.msgLen.add S.msgLen) j).eval n)
          (fun j => (snmDout S (.const 0) j).eval n) ((nmLen S pl r sl).eval n * S.ctLen.eval n)) n
          (q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
            (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n)
          (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
          (φ (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re, rA))) none)
        (fun p => if (recDist S pl r X).distinguisherL n
          (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
          (p.2.map Prod.fst) (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn p.1)))
          (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0) =
      ProbComp.expect (simulate (rImpl S .cpa b samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) ρ ρ' none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r.eval n * S.ctLen.eval n + sl.eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) rA)
          none)
        (fun p => if X.distinguisherL n (realView S samp pl n (r.eval n)
          (pairSndD (S.gen.runAt n [] rg)) ρ (List.ofFn p.1) p.2) rX = true then 1 else 0) := by
  have hct := ctLen_pos S n rg re hL
  have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hfin : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
      (st : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool)
      (a : Fin (((r.mul S.ctLen).add sl).eval n) → Bool),
      (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω st a =
        .pure (padFin _ (nmOutL S samp r n (pairEncode (List.replicate n true)
          (pairEncode z (pairEncode (List.ofFn ω) (List.ofFn st)))) (List.ofFn a)
          (stParam S hl n (List.ofFn st)) (finMsg S samp n (pairSndD z) (List.ofFn ω)
            (stParam S hl n (List.ofFn st))))) :=
    fun z ω st a => nmFinish S samp pl hl hist hist_poly r sl n z ω st a hdα hct
  refine (expect_toCompOn_outLen _ B₀ n _ _ _ none
    (nmParams_outLen_eval S samp pl hl hist hist_poly r sl n).symm
    (fun p => if (recDist S pl r X).distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
      (p.2.map Prod.fst) (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) p.1))
      (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0)).trans ?_
  rw [← hφ, nmParams_advInput, chalHandler_init, simulate_bind, simulate_comp,
    ← nmAbs_none S samp pl hl hist hist_poly r sl n ρ ρ',
    simulate_eq_of_abs _ _ _ (nmComp_abs S samp pl hl hist hist_poly r sl n _ _ ρ ρ' re b ρ''),
    OracleComp.bind_assoc, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, hfin, simulate_pure]
  rw [ProbComp.expect_bind]
  simp only [ProbComp.expect_pure]
  refine (expect_toCompOn_outLen _ A n (q.eval n) _ rA none hdα fun p =>
    if (recDist S pl r X).distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg))
      ((nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).2.map Prod.fst)
      (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (List.ofFn (padFin _ (nmOutL S samp r n
        (pairEncode (List.replicate n true)
          (pairEncode (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n))
            (pairEncode (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
              (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1)))) p.1
        (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1))
        (finMsg S samp n (pairSndD (pairEncode (pairFstD (S.gen.runAt n [] rg)) (samp.advice n)))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re))
          (stParam S hl n (List.ofFn (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2).1))))))))
      (NUPPT.coinsCongr (recDist_coins S pl r X).symm n rX) = true then 1 else 0).trans ?_
  refine congrArg _ (funext fun p => ?_)
  rw [recDist_distinguisherL, recView_nmOut S samp pl hl hist hist_poly r sl n rg hL ρ ρ' re p.2 _
    (by rw [List.length_ofFn])]

include hist_poly in
/-- **The NM adversary exists:** for the sampler `samp` (parameter length `pl`, history `hist` of
length `hl`), the adversary `A` and the polynomials `q`, `r`, `sl`, there are a machine `B` and a
budget `qB` such that for every distinguisher `X`, every `n` with `msgLen(n) > 0` and every `b`,
`NM_b(B, recDist X)` (budget `qB`, `nmLen` ciphertexts, under CPA) accepts with the probability of
the hybrid `H_b`.

**Proof sketch.** `B₀` is T2's machine of the NM adversary's handler and `B` hard-wires
`M.advice n` (`exists_withAdviceOn`). Reindex `B`'s coins as `(ρ ‖ ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`,
`seedEquivPoly`, `seedEquiv`, `expect_sample_prod`) and the distinguisher's as `X`'s; pointwise
this is
`nmRun_eq`, which does not read `re` (`expect_const`). -/
theorem exists_nmAdversary : ∃ (B : NUPPT) (qB : PolyExpr), ∀ (X : NUPPT) (n : ℕ) (b : Bool),
    0 < S.msgLen.eval n →
      accept (S.nmGame .cpa B (qB.eval n) ((nmLen S pl r sl).eval n) (recDist S pl r X) b n) =
        hybAcc S .cpa b samp pl hl hist A (q.eval n) (r.eval n) (sl.eval n) X n := by
  obtain ⟨B₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
    (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) ((r.mul S.ctLen).add sl)
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl))
  obtain ⟨B, hc, hB⟩ := NMCCA2.exists_withAdviceOn B₀ samp.advice samp.adv samp.advice_length
  refine ⟨B, (q.mul (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall).add
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall, fun X n b hL => ?_⟩
  obtain ⟨φ, hφ⟩ := hT2 n
  have hK : ((q.mul (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall).add
      (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall).eval n =
      q.eval n * (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).perCall.eval n +
        (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finCall.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  rw [accept_nmGame_eq_rImpl S .cpa B _ _ (recDist S pl r X) b n (fun _ => [])
    ((halfCoins S n).symm false), hybAcc_eq, hK]
  refine congrArg _ (funext fun rg => ?_)
  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr hc n)]
  simp only [hB]
  rw [← ChallengeSim.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
    ← ChallengeSim.expect_sample_equiv
      (seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ => ?_)
  rw [← ChallengeSim.expect_sample_equiv (seedEquiv (A := samp) (B := S.enc) rfl n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ' => ?_)
  refine Eq.trans ?_ (ProbComp.expect_const (ProbComp.sample (S.enc.Coins n)) _)
  refine congrArg _ (funext fun re => congrArg _ (funext fun rA => ?_))
  rw [← ChallengeSim.expect_sample_equiv (NUPPT.coinsCongr (recDist_coins S pl r X).symm n)]
  refine congrArg _ (funext fun rX => ?_)
  rw [← nmSeed_eq]
  exact nmRun_eq S samp pl hl hist hist_poly r sl A q B₀ n φ hφ rg hL ρ ρ' re rA b _ X rX

end Games

end TCSlib.Cryptography.Composability.NMSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-malleable encryption

[PS10, Definition 172.6] and Theorem 175.9, over the public-key experiment of Definition 171.5
(`Encryption/PublicKey/OracleSecurity.lean`).

**The experiment** `NM_b(Π, A, n)`: `(pk, sk) ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁}(1^n, pk)`;
`c ← Enc_pk(m_b)`; `(c'₁, …, c'_ℓ) ← A^{O₂}(c, state)`; output `(m'₁, …, m'_ℓ)` with
`m'_i = ⊥` if `c'_i = c` and `m'_i = Dec_sk(c'_i)` otherwise. The scheme is non-malleable when,
for every adversary `A` and distinguisher `D`, `D` tells `NM_0` from `NM_1` with negligible
advantage.

**Its encoding.** The oracles and the phases are those of Definition 171.5 (`indImpl`). The
adversary's final output is `ℓ(n)` ciphertexts of `ctLen(n)` bits. Each decryption is encoded as
`Dec`'s oracle answers are (`decAnswer`): a validity flag and the message, all-`false` for `⊥`.
`D` receives their concatenation.

**Source notes.**
- The definition writes private-key notation (`k ← Gen(1^n)`, `Dec_k`) for a public-key scheme;
  the public-key reading is taken (inventory Def-172.6).
- The source leaves the oracles `O₁, O₂` open; they are parametrized by the attack, as in
  Definition 171.5. Theorem 175.9's "CCA2 non-malleability" is the CCA2 instance.
- The adversary chooses `m₀, m₁`, so the definition's closing "for all `m₀, m₁ ∈ {0,1}^n`" is
  dropped. At CPA this is [PSV06, Definition 3], by the source's authors (ruling of 2026-11-05):
  the adversary picks `m₀, m₁` after seeing `pk`, `D` sees only the decryptions, and a copy of
  the challenge and an invalid ciphertext both decrypt to `⊥`.
- [PSV07, Definition 3] (IND-NME′) allows many challenges and distinguishes `COPY` from
  an invalid ciphertext's `⊥`; it is not literally the many-message form of this encoding.
  For the one-challenge security comparison, the complementary-pair copy-flag export argument
  is in the maintainer's sketch of `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa`
  (`SimNonMalleable.lean`). It separates `L = msgLen(n) = 0`, when the two experiments
  coincide, from `L > 0`, when the complementary plaintexts differ and their encrypted pair
  exports each copy flag. This is a security comparison of the one-challenge conventions;
  no many-challenge bridge is claimed here.
- Definition 173.7 and Theorem 174.8 follow [PSV07] (same ruling), in
  `Encryption/PublicKey/NonMalleability/Simulation.lean`.

## Contents

* `NonMalleability.Indistinguishability.Forward`: the forwarding handler and the log readers.
* `NonMalleability.Indistinguishability.Decrypt`: the reduction (⇒), whose finalization decrypts
  the adversary's ciphertexts and runs the distinguisher.
* `NonMalleability.Indistinguishability.Encrypt`: the reduction (⇐), whose finalization encrypts
  the guess and its negation, and the distinguisher that reads the guess back.

## Main definitions

* `FixedLengthPKScheme.nmGame`, `FixedLengthPKScheme.NMSecure`: [PS10, Definition 172.6].

## Main results

* `FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2`: the
  two directions of Thm 175.9.
* `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2` (Thm 175.9, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.5 and §7.1.7, Definition 172.6 and Theorem 175.9 (book pp. 172–175).
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 3.
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The codec of the adversary: the oracles of Definition 171.5, and a final output of `ℓ`
ciphertexts. -/
def nmCodec (n ℓ : ℕ) : MachineCodec (S.indSpec n) (Fin (ℓ * S.ctLen.eval n) → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The non-malleability codec uses `decodeBitMove` with the scheme's oracle lengths and an
output of `ℓ * ctLen(n)` bits. -/
theorem nmCodec_decodeMove (n ℓ : ℕ) (w : List Bool) :
    (S.nmCodec n ℓ).decodeMove w =
      decodeBitMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) w

/-- The non-malleability codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem nmCodec_encodeEntry (n ℓ : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.nmCodec n ℓ).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) e

/-- When its query budget expires, the non-malleability codec returns `zeroBits (ℓ * ctLen(n))`.
-/
theorem nmCodec_timeout (n ℓ : ℕ) :
    (S.nmCodec n ℓ).timeout = zeroBits (ℓ * S.ctLen.eval n) :=
  bitCodec_timeout (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n)

/-- The `i`-th of the `ℓ` ciphertexts in the adversary's output. -/
def nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (finProdFinEquiv (i, j))

/-- Ciphertext `i` is the block whose bit `j` is output bit `finProdFinEquiv (i, j)`. -/
theorem nthCt_eq {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    S.nthCt w i = fun j => w (finProdFinEquiv (i, j)) := rfl

/-- The decryption `m'` of an output ciphertext `c'` against the recorded challenge `s`: `⊥` if
`c'` is the challenge, and `Dec_sk(c')` otherwise, encoded as `Dec`'s oracle answers are. -/
def nmDecrypt {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) : Fin (S.msgLen.eval n + 1) → Bool :=
  if s = some c' then zeroBits _
  else FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c'))))

/-- An output ciphertext decrypts to all-false bits when it copies the challenge, and to the
encoded decryption answer otherwise [PS10, Definition 172.6]. -/
theorem nmDecrypt_eq {n : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (c' : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk s c' =
      if s = some c' then zeroBits (S.msgLen.eval n + 1)
      else FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c')))) := rfl

/-- The output of `NM_b`: the concatenated decryptions of the adversary's `ℓ` ciphertexts. -/
def nmOutput {n ℓ : ℕ} (sk : List Bool) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (w : Fin (ℓ * S.ctLen.eval n) → Bool) : List Bool :=
  (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten

/-- The non-malleability output flattens the encoded decryptions of all `ℓ` output blocks. -/
theorem nmOutput_eq {n ℓ : ℕ} (sk : List Bool)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) (w : Fin (ℓ * S.ctLen.eval n) → Bool) :
    S.nmOutput sk s w =
      (List.ofFn fun i : Fin ℓ => List.ofFn (S.nmDecrypt sk s (S.nthCt w i))).flatten := rfl

/-- **The experiment `NM_b(Π, A, n)`** [PS10, Definition 172.6] for the attack `atk`, with query
budget `q` and `ℓ` output ciphertexts, followed by the distinguisher `D`: sample the keys and the
coins, run `A` on `pk` against the oracles of Definition 171.5, decrypt its output (`⊥` on a copy
of the challenge), and output `D`'s verdict on the decryptions. -/
noncomputable def nmGame (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (D.Coins n)).bind fun ρ =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res =>
      .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)

/-- The non-malleability experiment samples keys and both machines' coins, runs the adversary
against the IND oracles, and applies the distinguisher to its decrypted output
[PS10, Definition 172.6]. -/
theorem nmGame_eq (atk : Attack) (A : NUPPT) (q ℓ : ℕ) (D : NUPPT) (b : Bool) (n : ℕ) :
    S.nmGame atk A q ℓ D b n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (ProbComp.sample (D.Coins n)).bind fun ρ =>
      (simulate
          (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
          (A.toCompOn (S.nmCodec n ℓ) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res =>
          .pure (D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) :=
  rfl

/-- **Non-malleability** [PS10, Definition 172.6] under the attack `atk`: for every non-uniform
PPT adversary `A`, every polynomial query budget `q` and number `ℓ` of output ciphertexts, and
every non-uniform PPT distinguisher `D`, `D`'s advantage between `NM_0` and `NM_1` is
negligible. -/
def NMSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
      (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n

/-- Non-malleability holds exactly when every adversary, polynomial query and output budgets,
and distinguisher have a negligible bound on the two games' advantage
[PS10, Definition 172.6]. -/
theorem NMSecure_iff (atk : Attack) :
    S.NMSecure atk ↔
      ∀ (A : NUPPT) (q ℓ : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D false n)
          (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n := Iff.rfl

/-- A copy of the challenge decrypts to `⊥`. -/
theorem nmDecrypt_challenge {n : ℕ} (sk : List Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.nmDecrypt sk (some c) c = zeroBits _ := by
  simp [nmDecrypt]

/-! ### Proof of Theorem 175.9 -/

section Proof

open AdaptiveCPA NMCCA2 ProbComp ChallengeSim

/-- The non-malleability codec is the bit codec of the oracles of Definition 171.5 with
`ℓ · ctLen(n)` output bits: `S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ · ctLen(n))`. -/
theorem nmCodec_eq_bitCodec (n ℓ : ℕ) :
    S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) := rfl

/-- Ciphertext `i` of an output string is its `i`-th block of `ctLen(n)` bits:
`⟦S.nthCt w i⟧ = (⟦w⟧.drop (i · ctLen(n))).take ctLen(n)`. -/
theorem ofFn_nthCt {n ℓ : ℕ} (w : Fin (ℓ * S.ctLen.eval n) → Bool) (i : Fin ℓ) :
    List.ofFn (S.nthCt w i) =
      ((List.ofFn w).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
  have hle : (i : ℕ) * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [finProdFinEquiv_apply_val]
    show j + S.ctLen.eval n * i = i * S.ctLen.eval n + j
    rw [Nat.mul_comm]
    omega

/-! ### (⇒) The CCA2 adversary built from a non-malleability adversary -/

/-- **The CCA2 decryption oracle on T2's codec answers as the experiment decrypts:** a query `x`
in state `st` is answered `⟦S.nmDecrypt sk st c⟧`, `c` the query read as a ciphertext, and the
state is kept.

**Proof sketch.** `castImpl_eq` and the decryption reader with its answer cast
(`indImpl_dec_onSpec_cast`); under CCA2 `Dec` is open (`decOpen_cca2`), so it refuses exactly
the recorded challenge with `⊥ = 0`, as `nmDecrypt` does (`nmDecrypt_eq`); the casts keep the
strings (`ofFn_cast`, `ofFn_zeroBits`, `outLens_zero`). -/
private theorem castImpl_indImpl_dec (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (S.indImpl .cca2 b n pk sk) 0 x st =
      .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
        (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
  rw [castImpl_eq, S.indImpl_dec_onSpec_cast, FixedLengthScheme.decOpen_cca2, Bool.true_and,
    S.nmDecrypt_eq]
  by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
  · rw [if_neg (by rw [decide_eq_true hs, Bool.not_true]; exact Bool.false_ne_true), if_pos hs,
      OracleComp.pure_bind]
    dsimp only
    rw [ofFn_zeroBits, ofFn_zeroBits, S.outLens_zero]
  · rw [if_pos (by rw [decide_eq_false hs, Bool.not_false]), if_neg hs, OracleComp.pure_bind]
    dsimp only
    rw [ofFn_cast (S.outLens_zero n).symm]

/-- **The reduction's queries are the experiment's ciphertexts:** block `i < ℓ(n)` of the
adversary's output `a`, read as a decryption query, is ciphertext `i` of `a`.

**Proof sketch.** Both are the bits `[i · ctLen(n), (i + 1) · ctLen(n))` of `⟦a⟧`
(`ofFn_nthCt`, `ofFn_padFin_eq_take`, `ofFn_cast`); they are equal as strings
(`List.ofFn_injective`). -/
private theorem decBlock_eq_nthCt (ℓ : PolyExpr) (n : ℕ)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (i : ℕ) (hi : i < ℓ.eval n) :
    cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn (decBlock S n a i))) =
      S.nthCt (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) ⟨i, hi⟩ := by
  have hct : (acDin S 0).eval n = S.ctLen.eval n := by rw [acDin_zero]
  have hin : S.inLens n 0 = S.ctLen.eval n := S.inLens_zero n
  have ha : (List.ofFn a).length = ℓ.eval n * S.ctLen.eval n := by
    rw [List.length_ofFn, PolyExpr.eval_mul]
  have hle : i * S.ctLen.eval n + S.ctLen.eval n ≤ ℓ.eval n * S.ctLen.eval n := by
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    exact this
  have hblk : List.ofFn (decBlock S n a i) =
      ((List.ofFn a).drop (i * S.ctLen.eval n)).take (S.ctLen.eval n) := by
    rw [decBlock_eq, ofFn_padFin_eq_take, hct,
      List.take_append_of_le_length (by rw [List.length_drop, ha]; omega)]
  apply List.ofFn_injective
  rw [ofFn_cast hin, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hct, hin]), hblk,
    ofFn_nthCt, GGMRed.ofFn_padFin_of_length ha]

/-- **The reduction's collected answers are the experiment's output:** the concatenated answers
of the CCA2 decryption oracle on the `ℓ(n)` blocks of `a`, in state `st`, are
`S.nmOutput sk st a`.

**Proof sketch.** Answer `i` is `⟦nmDecrypt sk st (block i)⟧` (`castImpl_indImpl_dec`, read at
its width by `acDout_zero`), and block `i` is ciphertext `i` (`decBlock_eq_nthCt`); compare the
two lists entrywise (`nmOutput_eq`). -/
private theorem decAnswers_eq_nmOutput (ℓ : PolyExpr) (n : ℕ) (sk : List Bool)
    (a : Fin ((ℓ.mul S.ctLen).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    ((List.range (ℓ.eval n)).map fun i => List.ofFn (padFin ((acDout S 0).eval n) (List.ofFn
        (S.nmDecrypt sk st (cast (S.indSpec_decDom n) (padFin (S.inLens n 0)
          (List.ofFn (decBlock S n a i)))))))).flatten =
      S.nmOutput sk st (padFin (ℓ.eval n * S.ctLen.eval n) (List.ofFn a)) := by
  have hout : (acDout S 0).eval n = S.msgLen.eval n + 1 := by
    rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const]
  rw [nmOutput_eq]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn])
    fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hout]),
    decBlock_eq_nthCt S ℓ n a i (by rw [List.length_map, List.length_range] at h₁; exact h₁)]

/-- **The reduction's game is the non-malleability experiment.** Let `B` be T2's machine for the
handler `decHandler S ℓ D` (with its coin bijection `φ` at `n`) and `B'` the machine `B` with
`D`'s advice hard-wired (`hB'`, coins identified by `hc`). Then `B'`'s CCA2 game `Ind_b` and the
experiment `NM_b` for `A` and `D` accept with the same probability.

**Proof sketch.** Fix the keys. `B'`'s coins are the handler's seed (`D`'s coins, `e`) and `A`'s
coins (`φ`, `expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`). For fixed coins,
transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards (`simulate_decHandler_impl`),
so the run is `A`'s run against the CCA2 oracles followed by the finalization in the final
state (`simulate_bind`), which decrypts the `ℓ` ciphertexts with the state kept
(`simulate_decHandler_finish`, `castImpl_indImpl_dec`) and outputs `D`'s verdict on
`S.nmOutput sk st a` (`decAnswers_eq_nmOutput`). That is `NM_b`'s output, after transporting
`A`'s run back to the experiment's codec (`nmCodec_eq_bitCodec`). -/
private theorem accept_indGame_decRed (A D B B' : NUPPT) (q ℓ : PolyExpr) (n : ℕ)
    (φ : (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((decHandler S ℓ D).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((ℓ.mul S.ctLen).eval n)) n (q.eval n) ((decHandler S ℓ D).advInput n z ω) r)
          ((decHandler S ℓ D).init n)).bind
          (fun res => (decHandler S ℓ D).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((decHandler S ℓ D).outLen.eval n)) n
          (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n)
          z (φ (ω, r)))
    (hc : B.coins = B'.coins)
    (hB' : ∀ (Q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn (S.indCodec n) n Q x (NUPPT.coinsCongr hc n r) =
        B.toCompOn (S.indCodec n) n Q (pairEncode x (D.advice n)) r)
    (b : Bool) :
    accept (S.indGame .cca2 B'
        (q.eval n * (decHandler S ℓ D).perCall.eval n + (decHandler S ℓ D).finCall.eval n) b n) =
      accept (S.nmGame .cca2 A (q.eval n) (ℓ.eval n) D b n) := by
  have hd1 : (decHandler S ℓ D).outLen.eval n = 1 := by
    rw [decHandler_outLen, PolyExpr.eval_const]
  have hdα : (ℓ.mul S.ctLen).eval n = ℓ.eval n * S.ctLen.eval n := PolyExpr.eval_mul _ _ _
  let e : D.Coins n ≃ (Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) :=
    NUPPT.coinsEquivPoly (decHandler_seedLen S ℓ D).symm n
  rw [accept_eq, accept_eq, S.indGame_eq, S.nmGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  conv_lhs => rw [prob_bind, ← expect_sample_equiv (φ.trans (NUPPT.coinsCongr hc n)),
    expect_sample_prod, expect_sample_comm]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  conv_lhs => rw [← expect_sample_equiv e]
  conv_rhs => rw [prob_bind]
  refine congrArg _ (funext fun ρ => ?_)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [Equiv.trans_apply, hB', prob_bind, indCodec_eq_bitCodec, h1]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
  rw [← hφ, decHandler_advInput, pairFstD_pairEncode, simulate_decHandler_impl,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]
  rw [simulate_bind, expect_bind]
  simp only [simulate_decHandler_finish S ℓ D n _ _ _ _ _ _ (castImpl_indImpl_dec S b n _ _),
    expect_pure]
  -- The experiment's side: transport `A`'s run to T2's codec.
  have h2 : (fun res : (Fin (ℓ.eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (D.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0)
        (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hdα _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if D.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin (ℓ.eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the verdict on the collected answers is `D`'s verdict on `NM_b`'s output.
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_singleton, hd1]), List.headD_cons,
    pairSndD_pairEncode, decAnswers_eq_nmOutput, NUPPT.coinsEquivPoly_ofFn,
    ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-- **(⇒) of Theorem 175.9: CCA2 security implies CCA2 non-malleability** [PS10, Theorem 175.9].

**Proof sketch.** Given `A` (budget `q`, `ℓ` ciphertexts) and `D`, T2
(`Games.exists_interactiveHandlerMachine`) makes the handler `decHandler S ℓ D` a machine `B`, and
`exists_withAdviceOn` hard-wires `D`'s advice into it (`B'`). `B'`'s budget is
`q · 1 + ℓ`, a polynomial; CCA2 security gives a negligible bound on `B'`'s advantage, which at
every `n` equals the advantage of `D` between `NM_0` and `NM_1` (`accept_indGame_decRed`). -/
theorem nmSecure_cca2_of_indSecure_cca2 (h : S.INDSecure .cca2) : S.NMSecure .cca2 := by
  rw [NMSecure_iff]
  intro A q ℓ D
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (ℓ.mul S.ctLen) (decHandler S ℓ D)
  obtain ⟨B', hc, hB'⟩ := exists_withAdviceOn B D.advice D.adv D.advice_length
  obtain ⟨ε, hε, hbound⟩ := (S.INDSecure_iff .cca2).1 h B'
    ((q.mul (decHandler S ℓ D).perCall).add (decHandler S ℓ D).finCall)
  refine ⟨ε, hε, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have key := fun b => accept_indGame_decRed S A D B B' q ℓ n φ hφ hc
    (fun Q x r => hB' n (S.indCodec n) Q x r) b
  have hn := hbound n
  rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
  rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
  exact hn

/-! ### (⇐) The non-malleability adversary built from a CCA2 adversary -/

/-- A two-block concatenation at a width only propositionally equal to `2`: for `k = 2`,
`(List.ofFn f).flatten = f 0 ++ f 1` (`OneWay.flatten_ofFn_two` after substituting `k`). -/
private theorem flatten_ofFn_two {k : ℕ} (hk : k = 2) (f : Fin k → List Bool) :
    (List.ofFn f).flatten = f ⟨0, by omega⟩ ++ f ⟨1, by omega⟩ := by
  subst hk
  exact OneWay.flatten_ofFn_two f

/-- **The distinguisher recovers the guess.** Let the reduction output the ciphertexts
`c₁ = encCt … g true` (an encryption of `g^m`) and `c₂ = encCt … g false` (of `(¬g)^m`) under a
generated key, with `m = msgLen(n) > 0`. Then for every recorded challenge `st`, the distinguisher's
verdict on the experiment's output `S.nmOutput sk st (c₁ ‖ c₂)` is `g`.

**Proof sketch.** By correctness `c₁` decrypts to `g^m` and `c₂` to `(¬g)^m` (`S.correct`, with
`S.enc_length` for the padding), so `c₁ ≠ c₂` (their messages differ at bit `0`), and `st` copies
at most one of them. If `st ≠ some c₁` the first decryption is valid (`guessBit_valid`); otherwise
the first is `⊥` and the second valid (`guessBit_refused`). -/
private theorem guessDist_nmOutput (n : ℕ) (hm : 0 < S.msgLen.eval n) (rg : S.gen.Coins n)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g : Bool)
    (st : Option (Fin (S.ctLen.eval n) → Bool)) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) st
      (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n)
        (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g true ++
          encCt S n (pairFstD (S.gen.runAt n [] rg)) ω g false))) ρ = g := by
  set pk := pairFstD (S.gen.runAt n [] rg)
  set sk := pairSndD (S.gen.runAt n [] rg)
  set c₁ := encCt S n pk ω g true
  set c₂ := encCt S n pk ω g false
  have h2 : (PolyExpr.const 2).eval n = 2 := PolyExpr.eval_const _ _
  -- The honest ciphertexts and their decryptions.
  have hc : ∀ β, encCt S n pk ω g β = S.enc.runAt n (pairEncode pk (List.ofFn
      fun _ : Fin (S.msgLen.eval n) => if β then g else !g)) (encTape S n ω β) := fun β => by
    rw [encCt_eq, EnsembleLemmas.padL_eq, List.take_append_of_le_length (by rw [S.enc_length]),
      List.take_of_length_le (by rw [S.enc_length])]
  have hlen : ∀ β, (encCt S n pk ω g β).length = S.ctLen.eval n := fun β => by
    rw [encCt_eq, EnsembleLemmas.length_padL]
  have hdec : ∀ β, decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (encCt S n pk ω g β))) =
      some fun _ => if β then g else !g := fun β => by
    rw [hc]
    exact S.correct n _ rg (encTape S n ω β)
  -- The two blocks of the output.
  set W := padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) (c₁ ++ c₂)
  have hW : List.ofFn W = c₁ ++ c₂ := GGMRed.ofFn_padFin_of_length (by
    rw [List.length_append, hlen, hlen, h2]; omega)
  have hblk : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool), (i : ℕ) = (if β then 0 else 1) →
      List.ofFn (S.nthCt W i) = encCt S n pk ω g β := by
    intro i β hi
    rw [ofFn_nthCt, hW, hi]
    cases β
    · rw [if_neg Bool.false_ne_true, Nat.one_mul, List.drop_left' (hlen true),
        List.take_of_length_le (by rw [hlen])]
    · rw [if_pos rfl, Nat.zero_mul, List.drop_zero, List.take_left' (hlen true)]
  have hdecB : ∀ (i : Fin ((PolyExpr.const 2).eval n)) (β : Bool),
      (i : ℕ) = (if β then 0 else 1) →
      decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn (S.nthCt W i)))) =
        some fun _ => if β then g else !g := fun i β hi => by
    rw [hblk i β hi]
    exact hdec β
  -- The output is the two decryptions.
  have i₀ : (0 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have i₁ : (1 : ℕ) < (PolyExpr.const 2).eval n := by rw [h2]; omega
  have hout : S.nmOutput sk st W = List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨0, i₀⟩)) ++
      List.ofFn (S.nmDecrypt sk st (S.nthCt W ⟨1, i₁⟩)) := by
    rw [nmOutput_eq]
    exact flatten_ofFn_two h2 _
  -- The two ciphertexts differ.
  have hne : S.nthCt W ⟨0, i₀⟩ ≠ S.nthCt W ⟨1, i₁⟩ := by
    intro h
    have e := (hdecB ⟨0, i₀⟩ true rfl).symm.trans (h ▸ hdecB ⟨1, i₁⟩ false rfl)
    have := congrFun (Option.some.inj e) ⟨0, hm⟩
    simp at this
  rw [guessDist_distinguisherL, hout]
  by_cases hs : st = some (S.nthCt W ⟨0, i₀⟩)
  · have hs' : st ≠ some (S.nthCt W ⟨1, i₁⟩) := fun h => hne (Option.some.inj (hs.symm.trans h))
    rw [S.nmDecrypt_eq, S.nmDecrypt_eq, if_pos hs, if_neg hs', hdecB ⟨1, i₁⟩ false rfl]
    simpa only [if_neg Bool.false_ne_true] using guessBit_refused hm g
  · rw [S.nmDecrypt_eq, if_neg hs, hdecB ⟨0, i₀⟩ true rfl]
    simpa only [if_pos rfl] using guessBit_valid hm g _

/-- **The reduction's experiment is the CCA2 game.** Let `B` be T2's machine for the handler
`encHandler S` (with its coin bijection `φ` at `n`), and `msgLen(n) > 0`. Then `B`'s experiment
`NM_b` with two output ciphertexts and the distinguisher `guessDist` accepts with the probability
of `A`'s CCA2 game `Ind_b`.

**Proof sketch.** Fix the keys. `B`'s coins are the handler's seed `ω` and `A`'s coins `r` (`φ`,
`expect_sample_equiv`, `expect_sample_prod`). For fixed `ω`, `r` and the distinguisher's coins,
transport `B`'s run to T2's codec (`nmCodec_eq_bitCodec`, `expect_simulate_castImpl_toCompOn`) and
replace it by the reduction (T2's equation `hφ`). The handler forwards
(`simulate_encHandler_impl`), so the run is `A`'s run against the CCA2 oracles, after which the
finalization outputs the two ciphertexts and keeps the recorded challenge (`simulate_bind`,
`encHandler_finish`). Whatever that challenge is, `guessDist` outputs `A`'s guess
(`guessDist_nmOutput`). Transport `A`'s run back to the game's codec (`indCodec_eq_bitCodec`). The
result does not depend on `ω` or on the distinguisher's coins (`expect_const`). -/
private theorem accept_nmGame_encRed (A B : NUPPT) (q : PolyExpr) (n : ℕ)
    (hm : 0 < S.msgLen.eval n)
    (φ : (Fin ((encHandler S).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (r : A.Coins n),
      (simulate ((encHandler S).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((encHandler S).advInput n z ω) r)
          ((encHandler S).init n)).bind
          (fun res => (encHandler S).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((encHandler S).outLen.eval n)) n
          (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n) z (φ (ω, r)))
    (b : Bool) :
    accept (S.nmGame .cca2 B
        (q.eval n * (encHandler S).perCall.eval n + (encHandler S).finCall.eval n)
        ((PolyExpr.const 2).eval n) guessDist b n) =
      accept (S.indGame .cca2 A (q.eval n) b n) := by
  have hd1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const _ _
  have hd2 : (encHandler S).outLen.eval n = (PolyExpr.const 2).eval n * S.ctLen.eval n := by
    rw [encHandler_outLen, PolyExpr.eval_add, PolyExpr.eval_const]
    omega
  rw [accept_eq, accept_eq, S.nmGame_eq, S.indGame_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod]
  refine (congrArg _ (funext fun ω => ?_)).trans (expect_const _ _)
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  refine (congrArg _ (funext fun ρ => ?_)).trans (expect_const _ _)
  -- The reduction's side: transport to T2's codec and unfold the reduction.
  have h2 : (fun res : (Fin ((PolyExpr.const 2).eval n * S.ctLen.eval n) → Bool) ×
      Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (guessDist.distinguisherL n
        (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) res.2 res.1) ρ)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
          (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
        else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [padFin_ofFn]
  rw [prob_bind, nmCodec_eq_bitCodec, h2]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd2 _ B n _ _ _
    none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if guessDist.distinguisherL n (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) p.2
        (padFin ((PolyExpr.const 2).eval n * S.ctLen.eval n) p.1)) ρ = true then (1 : ℝ)
      else 0)).symm.trans ?_
  rw [← hφ, encHandler_advInput, simulate_encHandler_impl, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, encHandler_finish]
  rw [simulate_bind, expect_bind]
  simp only [simulate_pure, expect_pure]
  -- The game's side: transport `A`'s run to T2's codec.
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
        if p.1.headD false = true then (1 : ℝ) else 0) (List.ofFn res.1, res.2) := by
    funext res
    rw [prob_pure]
    dsimp only
    rw [headD_ofFn_one]
  rw [prob_bind, indCodec_eq_bitCodec, h1]
  refine Eq.trans ?_ (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd1 _
    A n _ _ _ none (fun p : List Bool × Option (Fin (S.ctLen.eval n) → Bool) =>
      if p.1.headD false = true then (1 : ℝ) else 0))
  refine congrArg _ (funext fun p => ?_)
  -- Pointwise: the distinguisher outputs `A`'s guess.
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false)) =
      encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) true ++
        encCt S n (pairFstD (S.gen.runAt n [] rg)) ω ((List.ofFn p.1).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  dsimp only
  rw [hw, guessDist_nmOutput S n hm]

/-- **(⇐) of Theorem 175.9: CCA2 non-malleability implies CCA2 security**
[PS10, Theorem 175.9].

**Proof sketch.** Given `A` with budget `q`, T2 (`Games.exists_interactiveHandlerMachine`) makes
the handler `encHandler S` a machine `B`, with budget `q · 1 + 0`. Non-malleability for `B`, two
output ciphertexts and `guessDist` gives a negligible bound. At `n` with `msgLen(n) > 0`, `A`'s
CCA2 advantage equals that experiment's advantage (`accept_nmGame_encRed`). At `msgLen(n) = 0` the
two CCA2 games coincide (`indImpl_eq_of_msgLen_eq_zero`), so `A`'s advantage is `0`. -/
theorem indSecure_cca2_of_nmSecure_cca2 (h : S.NMSecure .cca2) : S.INDSecure .cca2 := by
  rw [INDSecure_iff]
  intro A q
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (acDin S) (acDout S) (acDin S)
    (acDout S) (.const 1) (encHandler S)
  obtain ⟨ε, hε, hbound⟩ := (S.NMSecure_iff .cca2).1 h B
    ((q.mul (encHandler S).perCall).add (encHandler S).finCall) (.const 2) guessDist
  refine ⟨ε, hε, fun n => ?_⟩
  have hn := hbound n
  by_cases hm : S.msgLen.eval n = 0
  · have hg : S.indGame .cca2 A (q.eval n) false n = S.indGame .cca2 A (q.eval n) true n := by
      rw [S.indGame_eq, S.indGame_eq]
      simp only [indImpl_eq_of_msgLen_eq_zero S .cca2 n _ _ hm]
    rw [hg, advantage_self]
    exact (advantage_nonneg _ _).trans hn
  · obtain ⟨φ, hφ⟩ := hB n
    have key := fun b => accept_nmGame_encRed S A B q n (Nat.pos_of_ne_zero hm) φ hφ b
    rw [PolyExpr.eval_add, PolyExpr.eval_mul] at hn
    rw [advantage_eq, ← key false, ← key true, ← advantage_eq]
    exact hn

end Proof

/-- **Theorem 175.9: under CCA2, secrecy and non-malleability coincide** [PS10, Theorem 175.9].

**Proof sketch** (the source's, made explicit; the delivered proof).
1. (⇒) Given an NM adversary `A` with `ℓ` ciphertexts and a distinguisher `D`, the IND
   adversary runs `A` on `pk`, forwarding every query to its own oracles, then asks CCA2's `Dec`
   for each of `A`'s ciphertexts. `Dec` refuses the recorded challenge with the same `⊥ = 0` that
   `NM` assigns to its copies and decrypts every other ciphertext as `NM` does
   (`indImpl_dec_cca2_challenge`, `nmDecrypt_challenge`), so the answers are exactly `NM_b`'s
   output. It runs `D` on them and outputs `D`'s verdict. T2
   (`Games.exists_interactiveHandlerMachine`) makes this a machine, for the forwarding handler
   `NMCCA2.decHandler`: `advIn = pk`, one outer call per query, and `finCall = ℓ` in
   finalization before running `D`, for total budget `q + ℓ`. `D`'s advice is carried through
   `z = ⟨pk, α⟩` and hard-wired afterwards (`NMCCA2.exists_withAdviceOn`, from the public
   `exists_withAdvice`/`exists_comp` closure lemmas). The two games accept with the same
   probability at every `n` (`nmSecure_cca2_of_indSecure_cca2`).
2. (⇐) Given an IND adversary `A` with guess `g`, the NM adversary runs `A`, forwarding its
   queries, and outputs fresh encryptions of `g^{msgLen}` and `(¬g)^{msgLen}` under `pk` with its
   own seed (`NMCCA2.encHandler`). The two plaintexts differ, so by correctness at most one of
   the two ciphertexts is the challenge. The distinguisher (`NMCCA2.guessDist`) reads `g` from
   the first if it decrypts, and from the second otherwise. Same advantage; at `msgLen(n) = 0`
   the two CCA2 games coincide and the advantage is `0`
   (`indSecure_cca2_of_nmSecure_cca2`).

The source's sketch argues the contrapositives: an NM break yields a related ciphertext that
`Dec` decrypts, and an IND break lets the adversary decrypt and re-encrypt a related message. -/
theorem indSecure_cca2_iff_nmSecure_cca2 : S.INDSecure .cca2 ↔ S.NMSecure .cca2 := by
  exact ⟨S.nmSecure_cca2_of_indSecure_cca2, S.indSecure_cca2_of_nmSecure_cca2⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Forward.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers and log readers

Both reductions of [PS10, Theorem 175.9] run the adversary once against the reduction's own
oracles: every query is **forwarded** unchanged to the outer oracle of the same index, and only
the finalization differs. This file builds that handler once, generically in the oracle lengths
(`fwdHandler`), as a `Games.InteractiveHandler` with one outer call per inner query and an empty
state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its answers are
the outer oracle's (`fwdHandler_impl`), so simulating it is running the adversary against the
outer oracles (`simulate_fwdHandler_impl`).

It also provides the readers of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (`finU`,
`finZ`, `finW`, `finA`, `finL`) and of an encoded outer log: `logEmit G L` concatenates `G` of the
successive suffixes of the nested log `L`, is polynomial-time for polynomial-time `G`
(`polyTimeComputable_logEmit`), and on an encoded log is the concatenation of `G`'s values on the
entries (`logEmit_encodeLog`).

## Main definitions

* `NMCCA2.fwdHandler`: the forwarding handler with a given finalization.
* `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL`: the fields of a finalization input.
* `NMCCA2.logEmit`: concatenated readings of the suffixes of an encoded log.

## Main results

* `NMCCA2.fwdHandler_impl`, `NMCCA2.simulate_fwdHandler_impl`: forwarding.
* `NMCCA2.polyTimeComputable_logEmit`, `NMCCA2.logEmit_encodeLog`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable {k : ℕ}

/-! ### Readers of a round input -/

/-- The state `s` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rState (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i` of a round input. -/
private def rIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x` of a round input. -/
private def rQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of the call so far. -/
private def rLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The outer answer `y` recorded in a one-entry log `⟨⟨1^j, ⟨x, y⟩⟩, []⟩`. -/
private def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rLog w)))

/-- The fields of a round input (DL-30–34 overlap: the round-input readers). -/
private theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rState (InteractiveHandler.input n z ω s i x L) = s ∧
      rIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
      rQuery (InteractiveHandler.input n z ω s i x L) = x ∧
      rLog (InteractiveHandler.input n z ω s i x L) = L := by
  simp only [InteractiveHandler.input_eq, rState, rIdx, rQuery, rLog, pairFstD_pairEncode,
    pairSndD_pairEncode, and_self]

/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
with the outer answer `y` in the log, return `y` and keep the state. -/
private def fwdRun (w : List Bool) : List Bool :=
  if decide (rLog w = []) then pairEncode [false] (pairEncode (rIdx w) (rQuery w))
  else pairEncode [true] (rAns w ++ rState w)

/-- The forwarding round is polynomial-time. -/
private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hS : PolyTimeComputable rState := hF.comp hD
  have hI : PolyTimeComputable rIdx := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rQuery := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rLog := hD.comp (hD.comp hD)
  have hA : PolyTimeComputable rAns := hD.comp (hD.comp (hF.comp hL))
  exact polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
    ((polyTimeComputable_const [false]).pairEncode (hI.pairEncode hX))
    ((polyTimeComputable_const [true]).pairEncode (hA.append hS))

/-! ### The forwarding handler -/

/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
forwards the query to the outer oracle of the same index and returns its answer; the adversary's
input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
outer queries. -/
def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
  stateLen := .const 0
  seedLen := seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := fwdRun
  poly := polyTimeComputable_fwdRun
  advIn := advIn
  advIn_poly := advIn_poly
  outLen := outLen
  finCall := finCall
  finRun := finRun
  finRun_poly := finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
  finRun] fwdHandler

section Forward

variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)

/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.

**Proof sketch.** The call's first round has an empty outer log, so it is the query
`⟨[false], ⟨1^i, x⟩⟩` (`decodeBitMove_query`); its second round reads the answer `y` from the
one-entry log and returns `y ‖ s` (`decodeBitMove_ret`), which `impl` splits back into `y` and
`s` (`Fin.append_left`, `Fin.append_right`). -/
theorem fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
        i x s = .query i x fun y => .pure (y, s) := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, fwdHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := i) (x := x) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨-, hI, hX, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog [])
    rw [fwdRun, hI, hX, hL, MachineCodec.encodeLog_nil, if_pos (decide_eq_true rfl)]
    exact decodeBitMove_query (fun j => (din j).eval n) (fun j => (dout j).eval n) _ i x),
    OracleComp.query_bind]
  congr 1
  funext y
  rw [buildComp_zero_of_ret (a := Fin.append y s) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨hS, -, -, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]))
    have hlog : (bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]) = pairEncode (pairEncode (List.replicate i true)
          (pairEncode (List.ofFn x) (List.ofFn y))) [] := by
      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
        bitCodec_encodeEntry]
    have hA : rAns (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
          ([] ++ [⟨i, x, y⟩]))) = List.ofFn y := by
      rw [rAns, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
    rw [fwdRun, hA, hS, hL, hlog, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)),
      ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _)]
  rw [OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s j
  · funext j
    exact Fin.append_right y s j

/-- **Simulating the forwarding handler is running the computation:** for every computation
`c` against the oracles and every state `s`, `simulate (H.impl n z ω) c s = c.bind (fun a =>
pure (a, s))`.

**Proof sketch.** Induction on `c`, with `fwdHandler_impl` at each query. -/
theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt din dout n) α)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    simulate ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).impl n z ω) c s = c.bind fun a => .pure (a, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, fwdHandler_impl, OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    rw [OracleComp.pure_bind]
    exact ih y

end Forward

/-! ### Readers of a finalization input -/

/-- The parameter `1^n` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
def finU (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- `finU w = pairFstD (pairFstD w)`. -/
theorem finU_eq (w : List Bool) : finU w = pairFstD (pairFstD w) := rfl

/-- The reduction input `z` of a finalization input. -/
def finZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))

/-- `finZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem finZ_eq (w : List Bool) : finZ w = pairFstD (pairSndD (pairFstD w)) := rfl

/-- The seed `ω` of a finalization input. -/
def finW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))

/-- `finW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem finW_eq (w : List Bool) : finW w = pairSndD (pairSndD (pairFstD w)) := rfl

/-- The adversary's output `a` of a finalization input. -/
def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
theorem finA_eq (w : List Bool) : finA w = pairFstD (pairSndD (pairSndD w)) := rfl

/-- The outer log `L` of the finalization so far. -/
def finL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- `finL w = pairSndD (pairSndD (pairSndD w))`. -/
theorem finL_eq (w : List Bool) : finL w = pairSndD (pairSndD (pairSndD w)) := rfl

/-- **The fields of a finalization input:** on `finInput n z ω s a L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a,
L⟩⟩⟩` the readers return `1^n`, `z`, `ω`, `a` and `L`. -/
theorem fields_finInput (n : ℕ) (z ω s a L : List Bool) :
    finU (InteractiveHandler.finInput n z ω s a L) = List.replicate n true ∧
      finZ (InteractiveHandler.finInput n z ω s a L) = z ∧
      finW (InteractiveHandler.finInput n z ω s a L) = ω ∧
      finA (InteractiveHandler.finInput n z ω s a L) = a ∧
      finL (InteractiveHandler.finInput n z ω s a L) = L := by
  simp only [InteractiveHandler.finInput_eq, seedIn_eq, finU, finZ, finW, finA, finL,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The finalization-input readers are polynomial-time: `PolyTimeComputable finU`, and the same
for `finZ`, `finW`, `finA` and `finL`. -/
theorem polyTimeComputable_finFields :
    PolyTimeComputable finU ∧ PolyTimeComputable finZ ∧ PolyTimeComputable finW ∧
      PolyTimeComputable finA ∧ PolyTimeComputable finL := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp (hD.comp hD),
    hD.comp (hD.comp hD)⟩

/-! ### Readers of an encoded log -/

/-- **Concatenated readings of an encoded log:** `G` applied to the successive suffixes
`L, snd L, snd (snd L), …` of the nested log `L = ⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`, for `|L| + 1` steps, and
concatenated: `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
def logEmit (G : List Bool → List Bool) (L : List Bool) : List Bool :=
  (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L)

/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
theorem logEmit_eq (G : List Bool → List Bool) (L : List Bool) :
    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := rfl

/-- The iterated second projection never lengthens a word. -/
private theorem length_iterate_pairSndD_le (L : List Bool) (i : ℕ) :
    (pairSndD^[i] L).length ≤ L.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_pairSndD_le _).trans ih

/-- **The readings of an encoded log are polynomial-time** when `G` is
(`Complexity.polyTimeComputable_iterateEmit` with the step `pairSndD`, which never lengthens a
word, and `|L|` rounds). -/
theorem polyTimeComputable_logEmit {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (logEmit G) :=
  (polyTimeComputable_iterateEmit polyTimeComputable_pairSndD hG .var .var
    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_iterate_pairSndD_le x i)).congr
    fun L => by rw [PolyExpr.eval_var, logEmit_eq]

section LogEmit

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The second projection of an encoded log drops its first entry. -/
private theorem iterate_pairSndD_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec)
    (i : ℕ) : pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
  induction i generalizing h with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases h with
    | nil =>
      rw [MachineCodec.encodeLog_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
        ← MachineCodec.encodeLog_nil codec, ih, List.drop_nil, List.drop_nil]
    | cons e t =>
      rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- Reading the suffixes of a log within at least its number of steps. -/
private theorem flatMap_range_drop (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) :
    ∀ (h : QueryLog spec) (m : ℕ), h.length ≤ m →
      ((List.range m).flatMap fun i => G (codec.encodeLog (h.drop i))) = h.flatMap g := by
  intro h
  induction h with
  | nil =>
    intro m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, MachineCodec.encodeLog_nil, hnil]
  | cons e t ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      MachineCodec.encodeLog_cons, hcons, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih m' (by rw [List.length_cons] at hm; omega)

/-- An encoded log is at least as long as its number of entries. -/
private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) :
    h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons e t ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **The readings of an encoded log are the readings of its entries:** if `G [] = []` and `G`
reads only the first entry of a nonempty log, `G ⟨⟦e⟧, t⟩ = g e`, then
`logEmit G (codec.encodeLog h) = h.flatMap g`.

**Proof sketch.** The `i`-th suffix of the encoded log encodes `h.drop i`; the first `|h|`
readings are `g` of the entries and the rest are `G [] = []`, since `|h| ≤ |L|`. -/
theorem logEmit_encodeLog (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) (h : QueryLog spec) :
    logEmit G (codec.encodeLog h) = h.flatMap g := by
  rw [logEmit_eq]
  simp only [iterate_pairSndD_encodeLog]
  exact flatMap_range_drop codec G g hnil hcons h _
    (Nat.le_succ_of_le (length_le_length_encodeLog codec h))

end LogEmit

end TCSlib.Cryptography.Composability.NMCCA2

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability/Encrypt.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction from CCA2 security to non-malleability

Direction (⇐) of [PS10, Theorem 175.9]. Given a CCA2 adversary `A` with guess `g`, the
non-malleability adversary runs `A` on the public key and forwards all of `A`'s queries to its own
oracles (`NMCCA2.fwdHandler`). It then outputs two fresh encryptions under `pk`, with its own
coins: of `g^{m}` and of `(¬g)^{m}`, where `m = msgLen(n)`. The distinguisher `guessDist` reads `g`
back from the two decryptions: from the first message bit if the first decryption is valid,
and otherwise from the negated last bit of the second.

This file builds the handler (`encHandler S`), whose seed is two encryption tapes. It proves
the finalization's equation (`encHandler_finish`) and defines the distinguisher with its two
verdicts (`guessBit_valid`, `guessBit_refused`). It also shows that at `msgLen(n) = 0` the two
CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).

## Main definitions

* `NMCCA2.encHandler`: the handler of the reduction.
* `NMCCA2.encTape`, `NMCCA2.encCt`: the seed's two tapes and the two ciphertexts.
* `NMCCA2.guessBit`, `NMCCA2.guessDist`: the distinguisher.

## Main results

* `NMCCA2.simulate_encHandler_impl`, `NMCCA2.encHandler_finish`.
* `NMCCA2.guessDist_distinguisherL`, `NMCCA2.guessBit_valid`, `NMCCA2.guessBit_refused`.
* `NMCCA2.indImpl_eq_of_msgLen_eq_zero`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDout_zero)

variable (S : FixedLengthPKScheme)

/-! ### The finalization -/

/-- The plaintext bit of ciphertext `β`: the adversary's guess `g` (its output's first bit) for
`β = true`, and `¬g` for `β = false`. -/
private def eBit (β : Bool) (w : List Bool) : Bool :=
  if β then (finA w).headD false else !(finA w).headD false

/-- The plaintext of ciphertext `β`: its bit repeated `msgLen(n)` times. -/
private def eMsg (β : Bool) (w : List Bool) : List Bool :=
  if eBit β w then List.replicate (S.msgLen.eval (finU w).length) true
  else List.replicate (S.msgLen.eval (finU w).length) false

/-- The coins of ciphertext `β`: the first (`β = true`) or the second `ρ(n)` bits of the seed. -/
private def eTape (β : Bool) (w : List Bool) : List Bool :=
  if β then (finW w).take (S.enc.coins.eval (finU w).length)
  else (finW w).drop (S.enc.coins.eval (finU w).length)

/-- Ciphertext `β`: `Enc` on `⟨1^n, ⟨pk, plaintext⟩⟩` with empty advice and its coins, padded to
`ctLen(n)` bits. -/
private def eCt (β : Bool) (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (finU w)
      (pairEncode (finZ w) (eMsg S β w))) []) (eTape S β w)))

/-- **The finalization's round:** output the two ciphertexts, `⟨[true], c₁ ‖ c₂⟩`. -/
private def eFin (w : List Bool) : List Bool := pairEncode [true] (eCt S true w ++ eCt S false w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_eFin : PolyTimeComputable (eFin S) := by
  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
  have hg : PolyTimeComputable fun w => [(finA w).headD false] := polyTimeComputable_headD.comp hA
  have hBit : ∀ β, PolyTimeComputable fun w => [eBit β w] := by
    intro β
    cases β
    · exact (polyTimeComputable_not hg).congr fun w => rfl
    · exact hg.congr fun w => rfl
  have hMsg : ∀ β, PolyTimeComputable (eMsg S β) := fun β =>
    polyTimeComputable_ite (hBit β) ((polyTimeComputable_unaryPoly S.msgLen).comp hU)
      (EnsembleLemmas.polyTimeComputable_zeros S.msgLen hU)
  have hTape : ∀ β, PolyTimeComputable (eTape S β) := by
    intro β
    cases β
    · exact ((polyTimeComputable_pairDropPoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
    · exact ((polyTimeComputable_pairTakePoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hCt : ∀ β, PolyTimeComputable (eCt S β) := fun β =>
    EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
      (((hU.pairEncode (hZ.pairEncode (hMsg β))).pairEncode
        (polyTimeComputable_const [])).pairEncode (hTape β)))
  exact (polyTimeComputable_const [true]).pairEncode ((hCt true).append (hCt false))

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_encAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-! ### The handler -/

/-- **The handler of the reduction (⇐)** for the scheme `S`: the forwarding handler
(`fwdHandler`) on the oracles of Definition 171.5, with a seed of two encryption tapes
(`2ρ(n)` bits), the adversary run on the reduction input `pk`, and a finalization without outer
queries whose output is `2 · ctLen(n)` bits: `Enc_pk(g^{msgLen(n)})` with the first tape, then
`Enc_pk((¬g)^{msgLen(n)})` with the second, where `g` is the adversary's first output bit. -/
def encHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) :=
  fwdHandler (acDin S) (acDout S) (S.enc.coins.add S.enc.coins)
    (fun ctx => pairFstD (pairSndD ctx)) polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen)
    (.const 0) (eFin S) (polyTimeComputable_eFin S)

/-- Two encryption tapes: `(encHandler S).seedLen = ρ + ρ`. -/
theorem encHandler_seedLen : (encHandler S).seedLen = S.enc.coins.add S.enc.coins := by
  rw [encHandler, fwdHandler_seedLen]

/-- One outer call per inner query: `(encHandler S).perCall = .const 1`. -/
theorem encHandler_perCall : (encHandler S).perCall = .const 1 := by
  rw [encHandler, fwdHandler_perCall]

/-- No outer query in the finalization: `(encHandler S).finCall = .const 0`. -/
theorem encHandler_finCall : (encHandler S).finCall = .const 0 := by
  rw [encHandler, fwdHandler_finCall]

/-- Two ciphertexts as output: `(encHandler S).outLen = ctLen + ctLen`. -/
theorem encHandler_outLen : (encHandler S).outLen = S.ctLen.add S.ctLen := by
  rw [encHandler, fwdHandler_outLen]

/-- The adversary runs on the reduction input: `(encHandler S).advInput n z ω = z`. -/
theorem encHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) :
    (encHandler S).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [encHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- **The handler forwards** (`simulate_fwdHandler_impl`): `simulate (H.impl n z ω) c s =
c.bind fun a => pure (a, s)`. -/
theorem simulate_encHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (acDin S) (acDout S) n) α)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) :
    simulate ((encHandler S).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (acDin S) (acDout S) (S.enc.coins.add S.enc.coins) _
    polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen) (.const 0) (eFin S)
    (polyTimeComputable_eFin S) n z ω c s

/-- **The seed's two encryption tapes:** tape `true` is the first `ρ(n)` bits of the seed, tape
`false` the rest (`ρ(n)` bits), read as coins of `Enc`. -/
def encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    S.enc.Coins n :=
  (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then (List.ofFn ω).take (S.enc.coins.eval n)
    else (List.ofFn ω).drop (S.enc.coins.eval n)))

/-- `encTape S n ω β = (coinsEquivPoly rfl n).symm (padFin _ (if β then ⟦ω⟧.take ρ(n) else
⟦ω⟧.drop ρ(n)))`. -/
theorem encTape_eq (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    encTape S n ω β = (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then
      (List.ofFn ω).take (S.enc.coins.eval n) else (List.ofFn ω).drop (S.enc.coins.eval n))) :=
  rfl

/-- The tapes as strings: `⟦encTape S n ω β⟧ = if β then ⟦ω⟧.take ρ(n) else ⟦ω⟧.drop ρ(n)`. -/
theorem ofFn_encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    List.ofFn (encTape S n ω β) = if β then (List.ofFn ω).take (S.enc.coins.eval n)
      else (List.ofFn ω).drop (S.enc.coins.eval n) := by
  have hω : (List.ofFn ω).length = S.enc.coins.eval n + S.enc.coins.eval n := by
    rw [List.length_ofFn, encHandler_seedLen, PolyExpr.eval_add]
  rw [encTape_eq, NUPPT.coinsEquivPoly_symm_ofFn]
  cases β
  · exact GGMRed.ofFn_padFin_of_length (by
      rw [if_neg Bool.false_ne_true, List.length_drop, hω]; omega)
  · exact GGMRed.ofFn_padFin_of_length (by rw [if_pos rfl, List.length_take, hω]; omega)

/-- **Ciphertext `β` of the reduction's output**, for the public key `z`, the seed `ω` and the
guess `g`: `padL ctLen(n) (Enc_z(b^{msgLen(n)}); encTape β)` with `b = g` for `β = true` and
`b = ¬g` for `β = false`. -/
def encCt (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g β : Bool) :
    List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
    (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
    (encTape S n ω β))

/-- `encCt S n z ω g β = padL ctLen(n) (Enc_z((if β then g else ¬g)^{msgLen(n)}); encTape β)`. -/
theorem encCt_eq (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (g β : Bool) :
    encCt S n z ω g β = EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
      (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
      (encTape S n ω β)) :=
  rfl

/-- **The finalization outputs the two ciphertexts:** after the adversary's output `a` (guess
`g = ⟦a⟧.headD false`), `H.finish n z ω s a = pure (padFin _ (encCt … g true ++ encCt … g false))`,
asking nothing.

**Proof sketch.** With budget `0` the first round returns (`buildComp_zero_of_ret`): its word is
`⟨[true], c₁ ‖ c₂⟩` of the right length (`length_padL`, `decodeBitMove_ret`), and each `cᵢ` is
`encCt` by the input readers, `NUPPT.Uniform.runAt_eq` and `ofFn_encTape`. -/
theorem encHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
    (encHandler S).finish n z ω s a =
      .pure (padFin _ (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) := by
  have hfin : (encHandler S).finRun = eFin S := by
    funext w
    rw [encHandler, fwdHandler_finRun]
  rw [InteractiveHandler.finish_eq, encHandler_finCall, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
  have hCt : ∀ β, eCt S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        0).encodeLog [])) = encCt S n z ω ((List.ofFn a).headD false) β := by
    intro β
    have hm : eMsg S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
        (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
          0).encodeLog [])) =
        List.ofFn fun _ : Fin (S.msgLen.eval n) =>
          if β then (List.ofFn a).headD false else !(List.ofFn a).headD false := by
      rw [List.ofFn_const, eMsg, eBit, hA, hU, List.length_replicate]
      cases β <;> cases (List.ofFn a).headD false <;> rfl
    rw [eCt, hm, hU, hZ, encCt_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
      ofFn_encTape, eTape, hW, hU, List.length_replicate]
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) =
      encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  show decodeBitMove _ _ _ ((encHandler S).finRun _) = _
  rw [hfin, eFin, hCt, hCt]
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### The distinguisher -/

/-- **The distinguisher's verdict** on the concatenated decryptions `w = v₁ ‖ v₂`: the bit after
the first validity flag if that flag is set, and the negated last bit of `w` otherwise. -/
def guessBit (w : List Bool) : Bool :=
  if w.headD false then (w.drop 1).headD false else !w.reverse.headD false

/-- `guessBit w = if w.headD false then (w.drop 1).headD false else ¬ w.reverse.headD false`. -/
theorem guessBit_eq (w : List Bool) :
    guessBit w = if w.headD false then (w.drop 1).headD false else !w.reverse.headD false := rfl

/-- The distinguisher's raw function on the machine input `⟨⟨⟨1^n, w⟩, α⟩, ρ⟩`. -/
private def guessFun (x : List Bool) : List Bool :=
  if (pairSndD (pairFstD (pairFstD x))).headD false then
    [((pairSndD (pairFstD (pairFstD x))).drop 1).headD false]
  else [!(pairSndD (pairFstD (pairFstD x))).reverse.headD false]

/-- The distinguisher's raw function is polynomial-time. -/
private theorem polyTimeComputable_guessFun : PolyTimeComputable guessFun := by
  have hw : PolyTimeComputable fun x => pairSndD (pairFstD (pairFstD x)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hw)
    (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hw))
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp (BinArith.polyTimeComputable_reverse.comp hw)))

/-- **The distinguisher** of the reduction (⇐): the uniform machine without coins computing
`[guessBit w]` on its argument `w`. -/
noncomputable def guessDist : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_guessFun (.const 0)

/-- The distinguisher accepts `w` exactly when `guessBit w`:
`guessDist.distinguisherL n w ρ = guessBit w`. -/
theorem guessDist_distinguisherL (n : ℕ) (w : List Bool) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n w ρ = guessBit w := by
  have hrun : ∀ y r, guessDist.runAtL n y r = guessFun (pairEncode (pairEncode
      (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform polyTimeComputable_guessFun (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, guessFun, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, guessBit_eq]
  split <;> simp

/-- **A valid first decryption gives the guess:** if `v₁` encodes the message `g^m` with `m > 0`,
then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_valid {m : ℕ} (hm : 0 < m) (g : Bool) (v₂ : List Bool) :
    guessBit (List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => g)) ++ v₂) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [FixedLengthScheme.decAnswer_some, guessBit_eq, List.ofFn_succ, List.ofFn_succ]
  simp

/-- **A refused first decryption is answered by the second:** if `v₁` is `⊥ = 0` and `v₂`
encodes `(¬g)^m` with `m > 0`, then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_refused {m : ℕ} (hm : 0 < m) (g : Bool) :
    guessBit (List.ofFn (zeroBits (m + 1)) ++
      List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => !g))) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h2 : List.ofFn (Fin.cons (α := fun _ => Bool) true (fun _ : Fin (m' + 1) => !g)) =
      true :: (List.replicate m' (!g) ++ [!g]) := by
    rw [List.ofFn_succ, Fin.cons_zero, ← List.replicate_succ', ← List.ofFn_const]
    rfl
  rw [FixedLengthScheme.decAnswer_some, h2, guessBit_eq, ofFn_zeroBits, List.replicate_succ]
  simp

/-! ### Empty messages -/

/-- **With empty messages the two CCA2 oracles coincide:** if `msgLen(n) = 0`, then
`S.indImpl atk false n pk sk = S.indImpl atk true n pk sk` (both halves of a challenge are the
empty message).

**Proof sketch.** Compare query by query through the published equations: decryption does not
depend on the bit (`indImpl_dec_onSpec`), a repeated challenge repeats the record
(`indImpl_challenge_repeat_onSpec`), and a first challenge encrypts a half of the query
(`indImpl_challenge_none_onSpec`), whose string is `[]` either way. -/
theorem indImpl_eq_of_msgLen_eq_zero (atk : Attack) (n : ℕ) (pk sk : List Bool)
    (h : S.msgLen.eval n = 0) : S.indImpl atk false n pk sk = S.indImpl atk true n pk sk := by
  have h0 : ∀ f : Fin (S.msgLen.eval n) → Bool, List.ofFn f = [] := fun f =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, h])
  funext i x s
  match i with
  | 0 => rw [S.indImpl_dec_onSpec, S.indImpl_dec_onSpec]
  | 1 =>
    cases s with
    | some c => rw [S.indImpl_challenge_repeat_onSpec, S.indImpl_challenge_repeat_onSpec]
    | none =>
      rw [S.indImpl_challenge_none_onSpec, S.indImpl_challenge_none_onSpec]
      simp only [h0]

end TCSlib.Cryptography.Composability.NMCCA2

## ===== TCSlib/Cryptography/Games/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Complexity.Randomized.PPT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as oracle computations

The asymptotic layer quantifies over non-uniform probabilistic polynomial-time machines
(`Complexity.NUPPT`). A machine interacts with oracles as a **next-move function**: at
parameter `n`, with one random tape `r` for the whole interaction, it is run on the encoding of the
queries and answers so far. Its output is decoded as the next move: a query to one of the
oracles, or the final output. A query budget `q` ends the interaction (D7 of the ch. 2–4 design:
no oracle tapes, one activation per query).

This file turns such a machine into an oracle computation of the `Games` framework
(`NUPPT.toComp`), for any oracle family and any output type, given a *codec*: how output strings
decode into moves, and how a query-log entry encodes as a string. It needs only the machine model
and the framework, so the asymptotic layer can build on it. The ch. 2–4 layer's
`NUPPT.toOracleAdversary` (one oracle, a Boolean verdict) is the instance with the codec built
from its own `decodeOracleMove` and `encodeHist` (`TCSlib.Cryptography.Games.Bridges.Machines`).

The efficiency counterpart (a reduction written as an implementation of polynomial-time
computable handlers, run on a machine, is again a machine's computation) is the S2b efficiency
result, stated in a later module.

## Main definitions

* `Games.Move spec α`: a query to an oracle of `spec`, or a final output in `α`.
* `Games.MachineCodec spec α`: decoding of moves and encoding of log entries.
* `Games.buildComp next timeout q hist`: the computation of a next-move function with budget `q`.
* `Complexity.NUPPT.toComp D codec n q r`: the computation of the machine `D` at parameter `n`
  with coins `r`; `Complexity.NUPPT.toCompOn D codec n q x r`, the same on the input `x`.

## Main results

* `Games.buildComp_costBoundedBy`, `NUPPT.toComp_costBoundedBy`: the computation makes at most `q`
  queries.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 and Definition 96.1 (oracle machines).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {ι : Type} {α : Type}

/-- A **move** of a next-move machine against the oracles of `spec`: ask oracle `i` the query
`x`, or stop with the output `a`. -/
inductive Move (spec : OracleSpec ι) (α : Type) : Type where
  /-- Ask oracle `i` the query `x`. -/
  | query (i : ι) (x : spec.dom i)
  /-- Stop with the output `a`. -/
  | ret (a : α)

/-- A **codec** for machines against `spec` with outputs in `α`: how an output string decodes
into a move, how one query-log entry is encoded for the machine, and the output forced when the
query budget runs out. -/
structure MachineCodec (spec : OracleSpec ι) (α : Type) where
  /-- Decode a machine output as a move. -/
  decodeMove : List Bool → Move spec α
  /-- Encode one log entry (oracle, query, answer). -/
  encodeEntry : (Σ i, spec.dom i × spec.rng i) → List Bool
  /-- The output when the budget is exhausted. -/
  timeout : α

namespace MachineCodec

variable {spec : OracleSpec ι}

/-- The encoding of a query log handed to the machine: the nested pair of its entries' encodings,
`⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`. -/
def encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) : List Bool :=
  h.foldr (fun e acc => pairEncode (codec.encodeEntry e) acc) []

/-- The empty log is encoded as the empty string: `codec.encodeLog [] = []`. -/
theorem encodeLog_nil (codec : MachineCodec spec α) : codec.encodeLog [] = [] :=
  rfl

/-- A log is encoded entry by entry:
`codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)`. -/
theorem encodeLog_cons (codec : MachineCodec spec α) (e : Σ i, spec.dom i × spec.rng i)
    (h : QueryLog spec) :
    codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h) :=
  rfl

end MachineCodec

/-- The computation of a next-move function `next` with query budget `q`, started from the log
`hist`: a final output stops; a query within budget asks the oracle and continues with the
answer appended to the log; a query when the budget is exhausted gives `timeout`. -/
def buildComp {spec : OracleSpec ι} (next : QueryLog spec → Move spec α) (timeout : α) :
    ℕ → QueryLog spec → OracleComp spec α
  | 0, hist => match next hist with
    | .ret a => .pure a
    | .query _ _ => .pure timeout
  | q + 1, hist => match next hist with
    | .ret a => .pure a
    | .query i x => .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))

section BuildComp

variable {spec : OracleSpec ι} {next : QueryLog spec → Move spec α} {timeout : α}
  {hist : QueryLog spec}

/-- With the budget spent, a final output stops the computation:
`buildComp next timeout 0 hist = pure a` when `next hist = ret a`. -/
theorem buildComp_zero_of_ret {a : α} (h : next hist = .ret a) :
    buildComp next timeout 0 hist = .pure a := by
  rw [buildComp, h]

/-- With the budget spent, a query gives the output `timeout` and asks nothing:
`buildComp next timeout 0 hist = pure timeout` when `next hist = query i x`. -/
theorem buildComp_zero_of_query {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
    buildComp next timeout 0 hist = .pure timeout := by
  rw [buildComp, h]

/-- Within budget, a final output stops the computation:
`buildComp next timeout (q + 1) hist = pure a` when `next hist = ret a`. -/
theorem buildComp_succ_of_ret {q : ℕ} {a : α} (h : next hist = .ret a) :
    buildComp next timeout (q + 1) hist = .pure a := by
  rw [buildComp, h]

/-- Within budget, a query asks the oracle and continues with the entry appended to the log:
`buildComp next timeout (q + 1) hist =
query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩]))` when `next hist = query i x`.
-/
theorem buildComp_succ_of_query {q : ℕ} {i : ι} {x : spec.dom i} (h : next hist = .query i x) :
    buildComp next timeout (q + 1) hist =
      .query i x (fun y => buildComp next timeout q (hist ++ [⟨i, x, y⟩])) := by
  rw [buildComp, h]

end BuildComp

/-- The computation built with budget `q` makes at most `q` queries, from every log. -/
theorem buildComp_costBoundedBy {spec : OracleSpec ι} (next : QueryLog spec → Move spec α)
    (timeout : α) : ∀ (q : ℕ) (hist : QueryLog spec),
      (buildComp next timeout q hist).CostBoundedBy (fun _ => 1) q
  | 0, hist => by
    cases h : next hist with
    | ret a => rw [buildComp_zero_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
    | query i x => rw [buildComp_zero_of_query h]; exact OracleComp.costBoundedBy_pure _ _ _
  | q + 1, hist => by
    cases h : next hist with
    | ret a => rw [buildComp_succ_of_ret h]; exact OracleComp.costBoundedBy_pure _ _ _
    | query i x =>
      rw [buildComp_succ_of_query h]
      exact (OracleComp.costBoundedBy_query _ _ _ _ _).2
        ⟨Nat.le_add_left 1 q, fun y => buildComp_costBoundedBy next timeout q _⟩

/-- The oracle computation of the machine `D` at parameter `n`, with coins `r` and query budget
`q`: the machine's next-move function is one activation of `D` on the encoded log.
[PS10, Definition 96.1], generalized to oracle families and arbitrary outputs. -/
def _root_.Complexity.NUPPT.toComp {spec : OracleSpec ι} (D : NUPPT) (codec : MachineCodec spec α)
    (n q : ℕ) (r : D.Coins n) : OracleComp spec α :=
  buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []

/-- The computation of `D` is built from the empty log, the next move being `D`'s output on the
encoded log, decoded: `D.toComp codec n q r =
buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []`.
-/
theorem _root_.Complexity.NUPPT.toComp_eq {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
    D.toComp codec n q r =
      buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout
        q [] :=
  rfl

/-- A machine's computation makes at most `q` queries. -/
theorem _root_.Complexity.NUPPT.toComp_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (r : D.Coins n) :
    (D.toComp codec n q r).CostBoundedBy (fun _ => 1) q :=
  buildComp_costBoundedBy _ _ q []

/-- The oracle computation of the machine `D` **on input `x`** (for example a public key or a
challenge) at parameter `n`, with coins `r` and query budget `q`: the next-move function is one
activation of `D` on `⟨x, encoded log⟩`. -/
def _root_.Complexity.NUPPT.toCompOn {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) : OracleComp spec α :=
  buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
    codec.timeout q []

/-- The computation of `D` on the input `x` is built from the empty log, the next move being
`D`'s output on `⟨x, encoded log⟩`, decoded: `D.toCompOn codec n q x r =
buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
codec.timeout q []`. -/
theorem _root_.Complexity.NUPPT.toCompOn_eq {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
    D.toCompOn codec n q x r =
      buildComp (fun hist => codec.decodeMove (D.runAt n (pairEncode x (codec.encodeLog hist)) r))
        codec.timeout q [] :=
  rfl

/-- A machine's computation on an input makes at most `q` queries. -/
theorem _root_.Complexity.NUPPT.toCompOn_costBoundedBy {spec : OracleSpec ι} (D : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : D.Coins n) :
    (D.toCompOn codec n q x r).CostBoundedBy (fun _ => 1) q :=
  buildComp_costBoundedBy _ _ q []

end TCSlib.Cryptography.Games
