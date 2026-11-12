# Fill `nm-sim` — checkpoint 2: both targets proved

**Worker:** Claude (external). **Issue base:** `262d6e9ae526c82eb68fe5a6169156bd1504e6d8` on
`cryptography/pass-shelat-ch2-4` (the merge of #294). **Local proof branch:** `fill/nm-sim`, head
`6882f3a13`, never pushed; the whole series from the base is in `patches/` (2 commits). **Pack:** read at
exchange `6f1e13ae6`; `SHA256SUMS` 7/7 OK; `order.txt` 252 modules, `roots.txt` 97, `base-sorries.txt` 26.

## Status

| Target | Status | Axioms |
|---|---|---|
| `FixedLengthPKScheme.nmSecure_of_simNMSecure` | **proved** (checkpoint 1) | `propext`, `Classical.choice`, `Quot.sound` |
| `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` | **proved** | `propext`, `Classical.choice`, `Quot.sound` |
| `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa` | admission-free | `propext`, `Classical.choice`, `Quot.sound` |

`evidence/logs/dev/cp2-axioms.log`. No statement changed, no escalation, no reader of a frozen file needed.
The owned file has no `sorry` left; the module title drops "(statement phase)" and gets `## Contents`.

## The proof of `simNMSecure_of_nmSecure_cpa` (brief step 2)

The maintainer's route; the owned sketch now describes it. The proof is organised around the hybrids
`H_b = NMSim.hybAcc … b …`: `A` runs against `NMSim.rImpl … b …`, which on the first challenge `a` answers
`⟨Enc_pk(M(a; ρ_b)), h(M(a; ρ))⟩` (`ρ₀ = ρ` the experiment's sampler coins, `ρ₁` independent), `Dec = ⊥`
under CPA, and the view is `realView`.

1. **Real = `H_false`** (`accept_snmReal_eq`, `NMSim.realAcc_eq_hybAcc`).
2. **Ideal = `H_true`** (`NMSim.exists_simulator`, `Simulator.lean`).
   - The simulator is T2's machine of `chalHandler (simParams …)`, with `M`'s advice hard-wired
     (`NMCCA2.exists_withAdviceOn`, imported). Seed `ρ̃ ‖ re`; state `[flag] ‖ ỹ ‖ h ‖ a`.
   - `Dec` gets `⊥` without a query. The first challenge `a` makes the only outer query `a`, gets `h`,
     computes `ỹ = Enc_pk(M(a; ρ̃); re)` (`simCt`, with `M`'s advice from the input `⟨pk, α_M⟩`) and
     answers `⟨ỹ, h⟩`. Repeated challenges replay the record. The output is `r` flagged entries
     `[flag ∧ c_i = ỹ] ‖ c_i`, then `σ` (`simFin`; a separate branch for `ctLen(n) = 0`, where `chunkMap`
     cannot cut).
   - **Budget.** T2 gives budget `q·1 + 1` (`finCall = 1`, so the budget is at least 1 even when `q = 0`).
     `chalHandler_costBoundedBy` shows the run asks at most one query (`simulate_costBoundedBy_once`).
     The finalization asks none (`simFinish`), so `toCompOn_budget_eq` (the generic budget reduction
     asked for in the brief, `Generic.lean`) gives the run at budget 1.
   - `simComp_abs`: the history oracle composed with the handler is `rImpl … true … ρ ρ̃ (some re)`
     through a state abstraction. `idealView_simOut`: the views agree. The encryption coins are drawn in
     advance (`expect_simulate_rImpl_eager`).
3. **`NM_b = H_b` when `msgLen(n) > 0`** (`NMSim.exists_nmAdversary`, `Reduction`, `Recover`, `IndSim`).
   - `B` is T2's machine of `chalHandler (nmParams …)` with `M`'s advice hard-wired. Seed `ρ ‖ ρ̃ ‖ re`.
   - The first challenge `a` asks `⟨M(a; ρ), M(a; ρ̃)⟩` and answers `⟨y, h(M(a; ρ))⟩`.
   - The output is, for each `c_i`, `c_i ‖ Enc(f^L) ‖ Enc((¬f)^L)` with `f = [c_i = y]`. Then the same pair
     for each bit of `a`, `m = M(a; ρ)` and `σ`, all with one tape `re`. That is `nmLen = 3r + 2(pl + L + sl)`
     ciphertexts.
   - `nmComp_abs`: `NM_b`'s oracles composed with the handler are `rImpl … b … ρ ρ̃ none`
     (`ofFn_drawWith_half` picks `M(a; ρ_b)`).
   - `recDist X` reads the view back. `entF` maps each group of three decryptions to `d_i`, and `bitG` maps
     each pair to its bit (`NMCCA2.guessBit`, imported). `guessBit_encPair`: by correctness the two
     ciphertexts of a pair differ, so at most one is the challenge (`guessBit_valid`/`_refused`).
     `ctLen_pos`: `msgLen > 0` forces `ctLen > 0`.
4. **Glue** (owned): at each `n`, the advantage is `B`'s NM advantage (`msgLen(n) > 0`) or 0
   (`hybAcc_true_eq_false` from `rImpl_eq_of_msgLen_eq_zero`).

Edge cases:
- **Budget 0:** `q = 0` is covered by `finCall = 1`.
- **`r = 0`, `sl = 0`:** generic.
- **`msgLen(n) = 0`:** advantage 0; the simulator is still exact there, including `ctLen = 0`.
- **No challenge:** both experiments use `0^{pl}`; the abstraction maps `none` to the initial states.
- **Repeated challenges:** `chalHandler_impl_some`.
- **Copied or invalid ciphertexts:** `COPY` is read through the flag, and `⊥` as `nmDecrypt`'s answer.
- **Codec timeouts:** every transport is an equality of whole runs.

## Changed files

| File | Lines | Change |
|---|---|---|
| `NonMalleability/Simulation.lean` (owned) | 790 | both bodies; section *The experiments on T2's lengths* (9 lemmas); sketches; title, `## Main results`, `## Contents` |
| `Simulation/Generic.lean` | 450 | budget reduction, eager coins, until-bad, chunk maps, output-length transport |
| `Simulation/Hybrid.lean` | 681 | hybrid and history oracles, views, block lemmas, `realAcc`/`idealAcc`/`hybAcc` |
| `Simulation/SimIND.lean`, `SimINDGap.lean` | 892, 332 | SIM ⇒ IND |
| `Simulation/Rounds.lean` | 345 | round readers, one-call lemmas, one-shot cost bound, seeds |
| `Simulation/Challenge.lean` | 402 | the challenge handler |
| `Simulation/Simulator.lean` | 610 | the simulator, Ideal = `H_true` |
| `Simulation/Reduction.lean`, `Recover.lean`, `IndSim.lean` | 634, 505, 281 | the NM adversary, distinguisher, `NM_b = H_b` |

All files are below 1000 lines. Helpers live in `TCSlib.Cryptography.Composability.NMSim`, and the owned
file imports all ten. The campaign lint is clean on the changed files: 0 FAIL, no WARN on them.

## Duplication (preliminary; final list with the final delivery)

**DL-30–36 overlap** (re-derived from published readers, general form):
- `flatMap_range_drop` (`Generic`, private): `Forward`'s private lemma.
- `fields_input` and the round readers `rdState`/`rdIdx`/`rdQuery`/`rdLog`/`rdAns` (`Rounds`): `Forward`'s
  private readers.
- `ofFn_padFin_eq_padL` (`Rounds`): `AdaptiveCPA/Handler`'s private lemma.
- `polyTimeComputable_guessBit` (`Recover`): the content of `Encrypt`'s private
  `polyTimeComputable_guessFun`.

**Imported, not copied:** `NMCCA2.fwdHandler` and its readers, `exists_withAdviceOn`, `guessBit` and its
lemmas, `finU/finZ/finW/finA`, `fields_finInput`, `AdaptiveCPA.castImpl`/`simulate_eq_of_abs`/…,
`ChallengeSim.expect_sample_*`.

## Evidence (this checkpoint)

- `evidence/logs/dev/cp2-*.log`: every changed module checked in dependency order, one module per
  `scripts/lean_check_tree.sh` call, no warning. `Recover` takes about 100 s; the others take under 15 s.
- `evidence/logs/dev/cp2-axioms.log`.
- From checkpoint 1: the pack, preflight, packages, bootstrap.

Still to come with the final delivery: the sweep with the sorry census, the axioms of every stored constant,
the whole-file seals with controls, the explicit-unfold scan, the lint log, and the patch replay. The
repository's `AGENTS.md` forbids running `lean`; the brief and the addendum require it, and I followed the
brief.
