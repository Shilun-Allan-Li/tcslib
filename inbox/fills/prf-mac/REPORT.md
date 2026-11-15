# Fill `prf-mac` · checkpoint 1 · the distinguisher

**Worker** Claude. **Unit** `prf-mac` (`Authentication.prfMAC_secure`, [PS10, Theorem 135.4]).
**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from
the exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (inputs checked: `evidence/logs/inputs-check.log`,
7/7 input files and 208/208 source files OK). **Proof branch** `fill/prf-mac` (local), one commit
over the base at this checkpoint.

## Status

| Target | Status at checkpoint 1 |
|---|---|
| `prfMAC_secure` | still admitted (`sorry`); its route is complete except steps 4–5 (checkpoints 2 and final) |

Checkpoint 1 (brief: sketch steps 2, 3 and 6) is delivered: the distinguisher is built with T2 and T4,
and its acceptance probability against **any** function `f` is the forger's forgery probability against
the tagging oracle `f` (`PRFMAC.exists_macReduction`, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound`). Applied to `f = f_k` it gives step 3; the game-side reading of the PRF MAC (the
deterministic `.const 0`-coin tag through `hFE`, the key as `Gen`'s coins through `runAt_coinKey`) is
already proved locally and lands at the final with the bound (see *Plan*).

## Changed and new files

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Authentication/MAC/FromPRF.lean` (owned) | 147 → 155 | imports the two helpers; `## Contents` (2 entries). Proof, title and sketch unchanged at this checkpoint. |
| `TCSlib/Cryptography/Authentication/MAC/FromPRF/Handler.lean` (new) | 444 | the handler |
| `TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean` (new) | 325 | the distinguisher |

No other file is edited. Every line ≤ 100 characters, every file ≤ 1000 lines
(`evidence/checks/widths-cp1.txt`). Every new proof of 15 lines or more has a `**Proof sketch.**`
(`evidence/checks/sketches-cp1.txt`; its one `MISSING` line is the base declaration `prfMAC`, untouched).

## The construction

* **Handler** (`PRFMAC.macHandler q ℓ t`, an `InteractiveHandler` with one inner and one outer oracle,
  `ℓ(n)`-bit queries, `t(n)`-bit answers). State: the queried messages, newest first, as blocks `1 ‖ m`
  of `ℓ(n)+1` bits followed by zeros, `q(n)(ℓ(n)+1)` bits (`macState`); no seed; `perCall = 1`,
  `finCall = 1`, `outLen = 1`; empty adversary input.
  - A call forwards the query and shifts its block into the state (`macHandler_impl`, from the encoded
    state of `L` with `|L| < q(n)`).
  - The finalization asks the oracle at the first `ℓ(n)` bits `m*` of the forger's output and returns
    `[⟦y⟧ = rest] ∧ [∀ m ∈ L, ⟦m⟧ ≠ ⟦m*⟧]` (`macHandler_finish`, from `|L| ≤ q(n)`); freshness is read
    block by block with the published chunk map `NMSim.chunkMap` (a zero block starts with `0`, so it
    never matches).
  - Round functions are private (`macRun`, `macFin`, …), polynomial-time from the published readers
    `InteractiveHandler.rU/rS/rI/rX/rL/rAns/finA`, `polyTimeComputable_pairTakePoly/DropPoly`,
    `polyTimeComputable_pairEq`, `NMSim.polyTimeComputable_chunkMap`.
* **Distinguisher** (`PRFMAC.exists_macReduction ℓ t q A`): `D` = T4 ∘ T2(`macHandler`) ∘ companion(`A`),
  budget `macBudget q = q·1 + 1`, and for all `n`, `f`:
  `𝔼_c[D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp (bitCodec …) n q(n) r) ((), [])]`,
  where `fnImpl f` answers `m` with `f m` and `FnForge f w log` is `f m = σ ∧ ∀ e ∈ log, e.2.1 ≠ m` for
  `(m, σ) = splitBits w` (the win test of `MAC.forgeGame`).
  - Proof as `PRFGame.exists_prfReduction`: coins through the three bijections; evaluation with `f` is
    simulation with `fnImpl f` (`simulate_ofComp_pure`); composition (`simulate_comp`); abstraction of
    the composed state to the encoded queried messages along runs of at most `q(n)` queries
    (`simulate_eq_of_abs_bounded`); every final log has at most `q(n)` entries
    (`allOutputs_simulate_withLog_length`); the finalization's test is `FnForge` on lists
    (`decide_fnForge`); output width transported by `expect_toCompOn_outLen`.

**Edge cases.** `n = 0` and `ℓ(n) = 0`: blocks have `1` bit, the empty message is stored as `[1]`;
budget `0`: the state stays `macState []`, the final query is still within `q·1 + 1`; repeated queries
are stored twice (harmless); a queried output message fails the freshness test exactly as in
`forgeGame`; malformed or timeout outputs: the reduction reads the forger's output as a vector, the same
`zeroBits` the game reads (`forgerCodec_timeout`); the extra final query is the `+ 1` of the budget.

## New declarations (namespace `TCSlib.Cryptography.Authentication.PRFMAC`)

*Handler.lean* — public: `finish_of_query_padFin`, `blockLen` (+`blockLen_eval`), `macStLen`
(+`macStLen_eval`), `blocks` (+`blocks_eq`, `blocks_cons`, `length_blocks`), `macHandler` (simps fields
`stateLen seedLen perCall init advIn outLen finCall`), `macState` (+`macState_eq`), `macHandler_stateLen_eval`,
`macHandler_init_eq`, `ofFn_macState`, `macHandler_impl`, `macHandler_finish`; private: `macRun`,
`polyTimeComputable_macRun`, `msgOf`, `sigOf`, `hitEmit`, `hitsOf`, `macFin`, `polyTimeComputable_macFin`,
`hits_nil_iff`.

*Reduction.lean* — `fnImpl` (+`fnImpl_eq`, `fnImpl_apply`), `FnForge` (+`fnForge_iff`, a `Decidable`
instance), `queried` (+`queried_eq`, `queried_nil`, `queried_append`, `length_queried`, `mem_queried`),
`decide_fnForge`, `allOutputs_simulate_withLog_length`, `macBudget` (+`macBudget_eval`),
`exists_macReduction`.

No `@[simp]`. Each public declaration's docstring states its formula; `[PS10, …]` where it comes from the
source.

## Overlap and reuse

| New declaration | Nearest relative | Relation; why not reused |
|---|---|---|
| `finish_of_query_padFin` | `Games/Efficiency.lean:680` `InteractiveHandler.impl_of_query`, `Games/Forwarding.lean:79` `impl_of_query_padFin`, `Efficiency.lean:799` `finish_of_ret` | the finalization analogue of `impl_of_query_padFin` (one outer query then a return); no finalization-with-query lemma exists (searched `finish_of_query`, `finCall := .const 1`). Proof re-follows `impl_of_query`'s published steps. **Promotion request** → `Games/Forwarding.lean`. |
| `macHandler`, rounds | `Games/Forwarding.lean:128` `fwdHandler` | `fwdHandler` has an empty state; freshness needs the queried messages in the state, so a new handler. |
| `blocks`, `macState`, `hits_nil_iff` | `NMSim.chunkMap`/`chunkMap_flatten` (`NonMalleability/Simulation/Generic.lean:78,138`) | reused (imported); the block encoding itself is new (the `blocks*` equivalences of `Asymptotic/*` are `Fin`-vector reshapes, not list encodings). |
| `fnImpl` | `Signatures/Lamport/Planted.lean:256` `tableSigner`, `OracleFromPRF/Reduction.lean:55` `PRFGame.fOuter`, `EncryptThenTag/Reduction.lean:59` | same shape `QueryImpl.ofComp fun _ m => pure (f m)`; those fix a table or pad lengths to a fixed spec, not a generic function on `bitSpec (fun _ => a) (fun _ => b)`. |
| `FnForge` | `MAC/Defs.lean:149` (`forgeGame`'s win test), `HashAndSign/FixedGame.lean:176` `Success`, `ForwardGame.lean:252` `OriginalSuccess` | restates the game's win test for a tag function instead of `Accepts`; the relatives are for signature schemes. |
| `queried`, `mem_queried` | `HashAndSign/ForwardGame.lean:210` `forward_fresh`, `Lamport/Planted.lean:312` `fresh_firstLog_iff` | freshness readers for other logs/oracles; `queried` is the message list the handler state stores. |
| `decide_fnForge` | `HashAndSign/CodecReaders.lean:95,106` `splitBits_append`, `splitBits_pad_concat`; `Complexity/Randomized/Classes.lean:217` | uses the same `List.ofFn_fin_append`/`Fin.append_castAdd_natAdd` step in the other direction (list reading of a split vector). |
| `allOutputs_simulate_withLog_length` | `Games/Simulate.lean:241` `simulate_withLog`, `OracleFromPRF/Collision.lean:249` (a length bound for `lazyImpl`'s state), `Games/Hopping.lean:179` `simulate_allOutputs_bad` | no published bound on a logged simulation's log length; generic statement. |
| `macBudget` | `OracleFromPRF/Reduction.lean:96` `PRFGame.qRed` | same pattern with finCall `1` instead of `0`. |
| `exists_macReduction` | `OracleFromPRF/Reduction.lean:258` `PRFGame.exists_prfReduction` | same proof template (T2, T4, companion, abstraction); different handler and game. Reuses `PRFGame.ofFn_evalFn_toCompOn` and `ChallengeSim.expect_sample_prod` by import. |

Imported and reused: T2/T4/companion, `fwd`-style call lemmas `impl_of_query_padFin`, `NMSim.chunkMap*`,
`Collection.ofFn_padFin_of_le`, `PRFGame.ofFn_evalFn_toCompOn`, `ChallengeSim.expect_sample_prod`,
`simulate_eq_of_abs_bounded`, `expect_congr_of_allOutputs`, `expect_toCompOn_outLen`,
`simulate_ofComp_pure`. Searches: `evidence/overlap/dupsearch-base.log` (script
`evidence/tools/dupsearch.sh`, run on the issue base).

**Imports outside the supplied closure.** `Handler.lean` imports
`Encryption/PublicKey/NonMalleability/Simulation/Generic` (for `NMSim.chunkMap`), whose own imports
(`Games.Efficiency`, `Games.Hopping`) are in `order.txt`; it is checked before the helpers
(`evidence/logs/dev/…Generic.log`) and will be inserted in the final sweep order.

## Scope requests

None.

## Promotion and reader requests

* `PRFMAC.finish_of_query_padFin` → `Games/Forwarding.lean` (beside `finish_of_ret_padFin`).

## Plan (checkpoint 2 and final)

* Checkpoint 2: `expect_fnForge_random_le` — against a uniform random function every forger forges
  with probability `≤ 2^{-t}` (lazy sampling by the published table override `ETTGame.ovr`,
  `expect_sample_ovr`).
* Final: the game side (`accept_forgeGame_eq`: deterministic tag), the generic bound
  `Pr[forge] ≤ prfAdv (F n) (D^{q·1+1}) + 2^{-n}` and `prfMAC_secure`; full sweep, sorry census,
  axioms of every constant, seals A/B (strict and coe, `PolyExpr.eval` excluded and sealed), paired
  controls, unfold scan, lint diff. (All of it already compiles locally.)

## Checks at this checkpoint

* Bootstrap of the base order (208/208 modules, `evidence/logs/bootstrap.tsv`, raw logs
  `evidence/logs/bootstrap/`; the background loop was lost twice to VM restarts and resumed in the
  foreground, `evidence/logs/bootstrap-run.log`).
* Preflight: 4 CPUs, ~15 GiB available; the initial 9.7 GiB free disk was below the 12 GiB floor, so
  my own finished scratch (earlier fills' worktrees and olean tree) was removed, leaving 12.9 GiB
  (`evidence/logs/preflight.log`).
* Checkpoint modules (`evidence/logs/cp1/`): `Handler`, `Reduction`, owned file — exit 0, no
  `error:`/`error(` line (regex `^\S+\.lean:\d+:\d+: error[:(]`); the owned file keeps its one `sorry`
  warning and the base's unused-simp-argument linter warning in `prfMAC.correct`.
* Axioms of every constant of the three modules (`evidence/axioms/axioms-cp1.log`): all within
  `propext, Classical.choice, Quot.sound`, except `prfMAC_secure` (`sorryAx`, still admitted).
* Lint `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 101 WARN, checkpoint
  92 / 101, line-set diff: no new and no removed line (`evidence/lint/`).

## Patches and reproduction

`patches/0001-…patch` (`git format-patch` from the issue base) and `patches/COMMITS.tsv` (hash, author
and committer name/email/date). Checked before pushing: a scratch clone at the issue base applies the
series with `git am`, committer set from `COMMITS.tsv`, and reproduces every hash and the final tree
(`evidence/amcheck/amcheck-cp1.log`).

## Evidence

`evidence/SHA256SUMS` lists every evidence file (inputs, all raw logs, lint outputs, axiom logs and
their Lean sources under `evidence/scratch-src/`, the tools under `evidence/tools/`); the top-level
`SHA256SUMS` lists every delivered file except itself. Both were checked against the delivered paths.
