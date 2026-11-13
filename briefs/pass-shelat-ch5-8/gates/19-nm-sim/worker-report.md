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
