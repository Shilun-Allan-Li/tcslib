# Fill `prf-mac` · final · Theorem 135.4 proved

**Worker** Claude. **Unit** `prf-mac` (`Authentication.prfMAC_secure`, [PS10, Theorem 135.4]).
**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (inputs: 7/7 files and 208/208 source checksums OK,
`evidence/logs/inputs-check.log`). **Proof branch** `fill/prf-mac` (local), four commits over the base:

| Commit | Content |
|---|---|
| `9ca4e7788c723a435ff3f31c40a9058b2b5bb5cb` | checkpoint 1: the handler and the distinguisher (delivered in exchange `f93d8a02f`) |
| `93d26bcb57fed63152bf80684f1562d31fade057` | checkpoint 2: forging against a random function (delivered in exchange `22b70519b`) |
| `5612cab612125952212c6061ab678aedaff1750a` | final: the game with a deterministic tag, the bound, `prfMAC_secure` |
| `f176a42cda28046762db199a1b82cbf2661c3f5e` | final: a Rule-10 repair found by the seals (see *Rule 10*) |

## Status

| Target | Status |
|---|---|
| `prfMAC_secure` | **proved**; axioms `propext`, `Classical.choice`, `Quot.sound` (`evidence/axioms/axioms-final.log`) |

The statement is unchanged (checked byte for byte, `evidence/final/owned-file-bodies.txt`). The proof gives
the source's bound at **every** `n`, `n = 0` included: for every forger `A` and budget `q` there is a
next-query machine `D` with

`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q(n)·1 + 1)) + 2⁻ⁿ`

(`PRFMAC.exists_forgeGame_le`), and `ε n := prfAdv … + 2⁻ⁿ` is negligible by `PRF.negligible_prfAdv`,
`Negligible.add` and `negligible_two_pow_neg`. No statement was weakened and no escalation was needed: the
maintainer's sketch is sound as written.

## Changed and new files

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Authentication/MAC/FromPRF.lean` (owned) | 147 → 222 | proof of `prfMAC_secure`; title, `## Main results`, `## Contents`, imports of the five helpers; the sketch describes the delivered proof |
| `…/MAC/FromPRF/Handler.lean` (new) | 444 | the reduction's handler |
| `…/MAC/FromPRF/Reduction.lean` (new) | 325 | the distinguisher (checkpoint 1) |
| `…/MAC/FromPRF/Random.lean` (new) | 155 | the random function (checkpoint 2) |
| `…/MAC/FromPRF/Game.lean` (new) | 99 | the forgery game with a deterministic tag |
| `…/MAC/FromPRF/Bound.lean` (new) | 183 | the bound for a MAC whose tag is a keyed family |

No other file is edited (`Games/Efficiency.lean` untouched). All lines ≤ 100 characters and files ≤ 1000
lines (`evidence/checks/widths-final.txt`).

**Owned-file edits.** Title "The PRF MAC (statement phase)" → "The PRF MAC"; `## Main results` now says
"proved", with the bound; a `## Contents` list of the five helpers (the owned file imports each of them
directly, so the facade lint covers them); the theorem's `**Proof sketch**` is rewritten to the delivered
proof (steps 1–5, naming the lemmas used). The statement prose (first paragraph) and the closing paragraph of
the docstring, the statement, and every other declaration of the file (`prfTagFun`, `prfVerFun` and their
readers, `prfMAC` with its `simps` fields) are byte-identical to the base
(`evidence/final/owned-file-bodies.txt`; `decls2` of the owned file: empty, `evidence/final/decls2-owned.txt`).
The base proof `prfMAC.correct` (23 lines, no sketch, and its unused-simp-argument linter warning) is
untouched; it is the one `MISSING` line of `evidence/checks/sketches-final.txt`.

## The proof

1. **The scheme, read through its readers** (owned file). `Gen` returns its coins (`runAt_coinKey` after
   `prfMAC_gen`, through a `G = …` generalization so that the coin type is not rewritten); the key is the
   coin string read at `n` bits (`NUPPT.coinsEquivPoly`, `finCongr (PolyExpr.eval_var n)`). `Tag` returns
   `E ⟨k, m⟩` whatever its coins (`prfMAC_tag`, `NUPPT.runAt_eq`, `runAtL_ofPolyTimeUniform`,
   `prfTagFun_eq`, `NUPPT.inArg_eq`), which is `f_k(m)` by `hFE`; `Ver` accepts `(m, σ)` iff
   `f_k(m) = σ` (`MAC.accepts_iff`, `prfMAC_ver`, `prfVerFun_eq`, `atParam_eq`). Messages and tags have
   `msgLen(n) = tagLen(n) = n` bits (`prfMAC_msgLen`, `prfMAC_tagLen`, `PolyExpr.eval_var`).
2. **The distinguisher** (`Reduction.lean`, checkpoint 1). `D` = T4 ∘ T2(`macHandler q ℓ t`) ∘
   companion(`A`), budget `macBudget q = q·1 + 1`, and for every `n` and every `f`,
   `𝔼_c[D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp … r) ((), [])]`
   (`exists_macReduction`). The handler stores the queried messages as blocks `1 ‖ m` (zeros after them),
   forwards each query (`macHandler_impl`), and finalizes with one query at the output message `m*` and the
   bit `[answer = σ*] ∧ [no stored block is 1 ‖ m*]` (`macHandler_finish`, freshness read with
   `NMSim.chunkMap`). The proof follows `PRFGame.exists_prfReduction`: coin bijections; evaluation is
   simulation with `fnImpl f` (`simulate_ofComp_pure`); composition (`simulate_comp`); abstraction of the
   composed state to the encoded queried messages along runs of at most `q(n)` queries
   (`simulate_eq_of_abs_bounded`); every final log has at most `q(n)` entries
   (`allOutputs_simulate_withLog_length`); the finalization's list test is `FnForge` (`decide_fnForge`).
3. **With `f_k`** (`Game.lean`). For a MAC whose tag returns `g rg m` whatever its coins and whose verifier
   accepts iff `g rg m = σ`, `Pr[forgeGame] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | … fnImpl (g rg) …]`
   (`accept_forgeGame_eq`: each tagging call has the law of `fnImpl`, `expect_simulate_congr`; the forger
   codec is the bit codec, `forgerCodec_eq_bitCodec`).
4. **With a random function** (`Random.lean`, checkpoint 2). `𝔼_R Pr[FnForge R | … fnImpl R …] ≤ 2^{-b}` for
   every forger computation, with no query bound (`expect_fnForge_random_le`): `R` is sampled lazily along the
   run with the table override `ETTGame.ovr` (`expect_sample_ovr` at a new query; a repeated query reads the
   table; every key is queried), so at the end a fresh message is no key and `R m` is uniform
   (`expect_sample_coord`, `expect_sample_mem_le`); a queried message is no forgery.
5. **The bound** (`Bound.lean`). `D`'s acceptance against `F_k` is the forgery probability (steps 2–3, the
   widths moved by `eval_toOracleAdversary_width₂`, the key by `expect_sample_equiv`); against a uniform `R`
   it is at most `2⁻ⁿ` (steps 2 and 4, the function space moved by a private `padFunEquiv`); the PRF
   advantage is the gap (`prfAdv_def`, `distAdv_def`, `Bridge.acceptProb_eq`, `Bridge.acceptGame_eq`,
   `oracleDist_apply`), so `Pr[forge] ≤ prfAdv + 2⁻ⁿ` (`exists_forgeGame_le`, generic in the MAC and the
   family; the owned file instantiates it).

**Edge cases.** `n = 0`: messages and tags are empty, the empty message is stored as the 1-bit block `[1]`,
and `2⁻⁰ = 1` covers an unqueried forger, which wins with probability 1. Budget `0`: the state stays
`macState []`; the final query is the `+ 1` of `q·1 + 1`. Repeated queries are stored twice (the freshness
test is unaffected). A forger whose output message was queried fails both `forgeGame`'s test and the
handler's. Malformed and timeout outputs: the reduction and the game read the same output vector (the
codec's `zeroBits` on a timeout, `forgerCodec_timeout`, through `forgerCodec_eq_bitCodec`). The tag
machine's empty coins: the tagging call is averaged over them and is constant (`expect_const`).

## New declarations (namespace `TCSlib.Cryptography.Authentication.PRFMAC`)

* *Handler.lean* — `finish_of_query_padFin`; `blockLen` (+`blockLen_eval`), `macStLen` (+`macStLen_eval`),
  `blocks` (+`blocks_eq`, `blocks_cons`, `length_blocks`); `macHandler` (simps fields `stateLen seedLen
  perCall init advIn outLen finCall`), `macState` (+`macState_eq`), `macHandler_stateLen_eval`,
  `macHandler_init_eq`, `ofFn_macState`, `macHandler_impl`, `macHandler_finish`; private `macRun`,
  `polyTimeComputable_macRun`, `msgOf`, `sigOf`, `hitEmit`, `hitsOf`, `macFin`,
  `polyTimeComputable_macFin`, `hits_nil_iff`.
* *Reduction.lean* — `fnImpl` (+`fnImpl_eq`, `fnImpl_apply`), `FnForge` (+`fnForge_iff`, a `Decidable`
  instance), `queried` (+`queried_eq`, `queried_nil`, `queried_append`, `length_queried`, `mem_queried`),
  `decide_fnForge`, `allOutputs_simulate_withLog_length`, `macBudget` (+`macBudget_eval`),
  `exists_macReduction`.
* *Random.lean* — `expect_fnForge_random_le`; private `expect_forge_pure_le`, `expect_forge_ovr_le`.
* *Game.lean* — `forgerCodec_eq_bitCodec`, `accept_forgeGame_eq`.
* *Bound.lean* — `eval_toOracleAdversary_width₂`, `exists_forgeGame_le`; private `padFunEquiv`.

97 stored constants in the six files (generated ones included). No `@[simp]`. Every public declaration's
docstring begins with its statement and gives its formula, with `[PS10, …]` where it comes from the source;
every proof of 15 lines or more has a `**Proof sketch.**` (`evidence/checks/sketches-final.txt`), and the long
proofs have step comments. Every new public `def` has `_eq`/`_apply`/`_iff` readers or `simps` fields (lint
check 8: no new WARN).

## Overlap and reuse

| New declaration | Nearest relative (path:line at the base) | Relation; why not reused |
|---|---|---|
| `finish_of_query_padFin` | `Games/Efficiency.lean:680` `InteractiveHandler.impl_of_query`; `Games/Forwarding.lean:79` `impl_of_query_padFin`; `Efficiency.lean:799` `finish_of_ret`, `Forwarding.lean:96` `finish_of_ret_padFin` | the finalization analogue of `impl_of_query_padFin` (one outer query, then a return); no finalization-with-query lemma exists. Proof re-follows `impl_of_query`'s published steps. **Promotion request** → `Games/Forwarding.lean`. |
| `macHandler`, its rounds | `Games/Forwarding.lean:130` `fwdHandler` | `fwdHandler` has an empty state; freshness needs the queried messages in the state. |
| `blocks`, `macState`, `hits_nil_iff` | `NonMalleability/Simulation/Generic.lean:78,138` `NMSim.chunkMap`, `chunkMap_flatten` | the chunk map is reused by import; the block encoding is new (the `blocks*` of `Asymptotic/*` and `Complexity/Randomized/RandomBits.lean:262` are `Fin`-vector reshapes, not list encodings). |
| `fnImpl` | `Signatures/Lamport/Planted.lean:256` `tableSigner`; `OracleFromPRF/Reduction.lean:55` `PRFGame.fOuter`; `EncryptThenTag/Reduction.lean:59` | same shape `QueryImpl.ofComp fun _ m => pure (f m)`; the relatives fix a table, or pad to a fixed spec. |
| `FnForge` | `MAC/Defs.lean:149` (`forgeGame`'s win test); `HashAndSign/FixedGame.lean:176` `Success`; `HashAndSign/ForwardGame.lean:252` `OriginalSuccess` | the MAC win test with `f m = σ` in place of `Accepts`; the relatives are for signature schemes. |
| `queried`, `mem_queried` | `HashAndSign/ForwardGame.lean:210` `forward_fresh`; `Lamport/Planted.lean:312` `fresh_firstLog_iff` | freshness readers for other logs; `queried` is the message list the state stores. |
| `decide_fnForge` | `HashAndSign/CodecReaders.lean:95,106` `splitBits_append`, `splitBits_pad_concat`; `Complexity/Randomized/Classes.lean:217` | the same `List.ofFn_fin_append`/`Fin.append_castAdd_natAdd` step, in the other direction (the list reading of a split vector). |
| `allOutputs_simulate_withLog_length` | `Games/Simulate.lean:241` `simulate_withLog`; `OracleFromPRF/Collision.lean:249` (a length bound for `lazyImpl`); `Games/Hopping.lean:179` `simulate_allOutputs_bad` | no published bound on a logged simulation's log; generic statement. Promotion candidate (`Games/Simulate.lean`). |
| `macBudget` | `OracleFromPRF/Reduction.lean:83` `PRFGame.qRed` | the same pattern with `finCall = 1`. |
| `exists_macReduction` | `OracleFromPRF/Reduction.lean:258` `PRFGame.exists_prfReduction` | the same template (companion, T2, T4, abstraction) for another handler and game; reuses `PRFGame.ofFn_evalFn_toCompOn` and `ChallengeSim.expect_sample_prod` by import. |
| `expect_forge_pure_le` (private) | `EncryptThenTag/Forgery.lean:294` `ETTGame.expect_hitW_le` (**private**) | re-derives, from the published `ovr` readers, `expect_sample_coord` and `expect_sample_mem_le`, the fresh-point case of that private lemma (a value of `R` off the table hits a fixed tag with probability `2^{-b}`), for this fill's `FnForge`. **Disclosed re-derivation of a private lemma.** |
| `expect_forge_ovr_le` (private), `expect_fnForge_random_le` | `EncryptThenTag/Forgery.lean:387` `ETTGame.expect_prob_bad_le`; `OracleFromPRF/Lazy.lean`, `EncryptThenTag/Lazy.lean`; `Pseudorandom/Functions/Asymptotic/Defs.lean` `acceptProb_random_eq_lazy` | the same lazy-sampling induction (`expect_sample_ovr` at a new query) for another game (one final guess, no budget). `acceptProb_random_eq_lazy` works on query trees, while T4 only identifies `D`'s evaluations, not its tree; so the table-override induction runs on the forger's computation. |
| `forgerCodec_eq_bitCodec` | `HashAndSign/CodecReaders.lean:72` `SignatureScheme.forgerCodec_eq_bitCodec` | the MAC analogue (same proof through `MachineCodec.ext_of_fields`, reused by import). **Promotion request** → `MAC/Defs.lean`. |
| `accept_forgeGame_eq` | `HashAndSign/ForwardGame.lean:303` `forgeGame_eq_fixed`; `OracleFromPRF.lean:246` `accept_prf_indGame` (private) | the MAC game with a deterministic tag; the relatives are the signature game with a fixed signer and the IND game of the §3.9 scheme. |
| `eval_toOracleAdversary_width₂` | `OracleFromPRF/Reduction.lean:228` `PRFGame.eval_toOracleAdversary_width`; `EncryptThenTag/Machines.lean:348` `ETTGame.eval_toOracleAdversary_len` | generalization to two independent widths `m₁ = n`, `m₂ = n` (the relatives move both widths to one value; here they are the distinct terms `msgLen(n)` and `tagLen(n)`). Dedup candidate: the three could be one lemma. |
| `padFunEquiv` (private) | `Complexity/Randomized/PPT.lean:266` `coinsEquivPoly` (`Equiv.arrowCongr (finCongr _)`) | an equivalence of function spaces read through `padFin`, so that the transported function is syntactically the one `eval_toOracleAdversary_width₂` produces. |
| owned-file `key`, `hkey`, `hgen` (local `let`/`have`s of the proof) | `Encryption/PrivateKey/OracleFromPRF.lean:131,138` `prfKeyEq`, `ofFn_prfKeyEq` (**private**), and its `gen.runAt` lemma above them | the same coin-to-key equivalence and readings for the PRF MAC, re-derived in a few lines from published readers (`NUPPT.coinsEquivPoly`, `coinsEquivPoly_ofFn`, `List.ofFn_congr`, `runAt_coinKey`); those are private to another scheme's file. **Disclosed re-derivation of a private definition and lemma.** |

Imported and reused: T2/T4/the companion, `impl_of_query_padFin`, `NMSim.chunkMap*`,
`Collection.ofFn_padFin_of_le`, `PRFGame.ofFn_evalFn_toCompOn`, `ChallengeSim.expect_sample_prod`,
`MachineCodec.ext_of_fields`, `ETTGame.ovr*`/`expect_sample_ovr`, `simulate_eq_of_abs_bounded`,
`expect_simulate_congr`, `expect_congr_of_allOutputs`, `expect_toCompOn_outLen`, `simulate_ofComp_pure`,
`expect_sample_coord`, `expect_sample_mem_le`, `Bridge.acceptProb_eq`/`acceptGame_eq`,
`PRF.negligible_prfAdv`. Searches: `evidence/overlap/dupsearch-base.log` (script `evidence/tools/dupsearch.sh`,
run on the issue base). Line references here supersede those of the checkpoint reports (two were off by a
few lines there).

## Scope requests

None. No frozen file was edited; the route needed no reader beside a foreign definition.

## Promotion and reader requests

* `PRFMAC.finish_of_query_padFin` → `Games/Forwarding.lean` (beside `finish_of_ret_padFin`).
* `PRFMAC.forgerCodec_eq_bitCodec` → `Authentication/MAC/Defs.lean` (beside the signature analogue's home).
* `PRFMAC.allOutputs_simulate_withLog_length` → `Games/Simulate.lean` (candidate).
* Dedup candidate: `PRFMAC.eval_toOracleAdversary_width₂`, `PRFGame.eval_toOracleAdversary_width`,
  `ETTGame.eval_toOracleAdversary_len`.

## Imports and order

* Two imported modules lie outside the supplied closure, each with its imports inside `order.txt`:
  `Encryption/PublicKey/NonMalleability/Simulation/Generic` (by `Handler`, for `NMSim.chunkMap`) and
  `Encryption/PrivateKey/EncryptThenTag/Tools` (by `Random`, for `ETTGame.ovr`). No new Mathlib import (the
  narrowed roots are unchanged).
* The final order (`evidence/final/order-final.txt`, 215 modules; `evidence/final/reorder.log`) is the
  supplied order with these two and the five helpers inserted before their consumers; this moves the owned
  file from position 139 to 214 (after the PRFGame modules it now imports) and the `Authentication` facade
  from 186 to 215. All other modules keep their relative order.

## Checks

* **Bootstrap** (base, `order.txt`, 208 modules): exit 0 for all, 0 error diagnostics
  (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`, `evidence/logs/bootstrap-errors.txt`).
  The background loop was lost to VM restarts twice and resumed chunk by chunk in the foreground
  (`evidence/logs/bootstrap-run.log`).
* **Owned module recheck, then the sweep** of the final order: 215/215 exit 0, **0 error diagnostics** counted
  with `^\S+\.lean:\d+:\d+: error[:(]` over every log (`evidence/final/sweep-errors.txt`, raw logs
  `evidence/final/sweep/`, `sweep.tsv`, `sweep-run.log`). After the Rule-10 repair commit `Random`,
  `Bound`, the owned file and the `Authentication` facade were checked again (pass 2); the pass-1 rows and
  logs are kept (`sweep-pass1.tsv`, `sweep-pass1-logs/`).
* **Sorry census**: base 20 declarations in 10 modules, equal to `base-sorries.txt`; final 19 in 9; the only
  change is the removal of `prfMAC_secure` (`evidence/final/sorry-census-{base,final,diff}.txt`).
* **Axioms**: `prfMAC_secure`: `[Classical.choice, Quot.sound, propext]`; all 97 stored constants of the six
  changed and new files: within these three (`evidence/axioms/axioms-final.log`; checkpoints:
  `axioms-cp1.log`, `axioms-cp2.log`).
* **Lint** `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 101 WARN, final 92 / 101;
  line-set diff: **no new and no removed FAIL or WARN line** (`evidence/lint/lint-{base,final}.txt`,
  `lintdiff-final.txt`; checkpoints likewise).

### Rule 10

**Seals** (`evidence/tools/seals.py`; sources `evidence/scratch-src/seal/`, raw logs and
`results.jsonl` in `evidence/seals/{base,final}/`). For each file, a census module with exactly the file's
imports lists every constant of its TCSlib import closure; the requests are every closure definition that is
a matcher or not reducible (instances, private definitions and generated matchers included; reducible
abbreviations are notation). A: `PolyExpr.eval` exempt; B: sealed. Strict: projection coercions sealed;
coe (canonical): `FinDist.instCoeFunForallReal` exempt. The probe is the file verbatim, with `import Lean`
and a harness after its imports that makes every request `local irreducible` by its exact name, and an
end-of-file harness that verifies every request is still irreducible.

| File | requests (strict-A) | strict-A | strict-B | coe-A | coe-B | base (4 variants) |
|---|---|---|---|---|---|---|
| `MAC/FromPRF.lean` (owned) | 2258 | pass | pass | pass | pass | pass (1384 requests) |
| `MAC/FromPRF/Handler.lean` | 2023 | pass | pass | pass | pass | — (new) |
| `MAC/FromPRF/Reduction.lean` | 2227 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Random.lean` | 2238 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Game.lean` | 2251 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Bound.lean` | 2257 | pass | pass | pass | pass | — |

All 24 final and 4 base probes: exit 0, 0 errors, every harness part installed and verified. **The strict and
coe variants agree everywhere**; their request sets differ by exactly the one coercion instance. **No
failing declaration** in any variant, so there is nothing to attribute between A and B either: no proof of
the fill reads `PolyExpr.eval` by unfolding (the widths are moved with `PolyExpr.eval_var/add/mul/const`).

**One finding, fixed.** The first final seal run (pass 1, `evidence/seals/final-pass1/`) failed in all four
variants in one declaration, `expect_fnForge_random_le`: `simp only [ovr_nil] at h` rewrote `ovr [] R` in the
bound but not in the `Decidable` instance argument of its `if`, and `exact h` then closed the goal by
unfolding `ETTGame.ovr`. Commit `f176a42c` rewrites the goal with `ovr_nil` instead (`rw` reaches the instance
argument); the pass-2 seals above pass.

**Paired controls** (`evidence/controls/`, source `evidence/scratch-src/controls/Controls.lean`, tool
`controls2.py`): unsealed, all examples close. Under each of the four variants (2260–2262 requests), the
sealed negatives `rfl`-reading `InteractiveHandler.rAns`, `PRFMAC.macBudget`, `PRFMAC.fnImpl`,
`MAC.forgerCodec` and `PRFMAC.macHandler`'s `perCall` **fail exactly once each**, and their published
readers close; the `PolyExpr.eval` negative closes under A and fails exactly once under B. A recorded
probe (C6) reads `FinDist`'s coercion through its instance by `rfl`: it closes under every variant, i.e.
sealing that instance does not block this reading in Lean 4.25, so the strict seal of the coercion has no
observable effect here (consistent with the variants agreeing).

**Explicit-unfold scan** (`evidence/final/rwids/rwids.tsv`, `scan-*.log`; tools `rwids.py`, `rwids_run.py`):
every identifier passed to `rw`/`simp`/`unfold`/… in the six files resolves to a theorem, a local
hypothesis, or a definition of the same file (`blockLen`, `macStLen`, `macBudget`, the private round
functions, and the base proof's `prfVerFun`): **no foreign TCSlib definition and no core or Mathlib
definition**.

## Patches and reproduction

`patches/0001…0004-*.patch` (`git format-patch` from the issue base) and `patches/COMMITS.tsv` (hash, author
name/email/date, committer name/email/date). **Checked before pushing:** a scratch clone at the issue base
applies the series with `git am`, the committer of each commit set from `COMMITS.tsv`, and reproduces all
four hashes and the final tree (`evidence/amcheck/amcheck-final.log`; checkpoints: `amcheck-cp1.log`,
`amcheck-cp2.log`).

## Notes

* **Environment.** 4 CPUs, ~15 GiB available memory. The initial free disk (9.7 GiB) was below the 12 GiB
  floor; I removed only my own finished scratch (earlier fills' worktrees and olean tree), leaving 12.9 GiB
  (`evidence/logs/preflight.log`). One Lean process at a time throughout; `python3 -I`; no `lake build`; the
  narrowed `lake exe cache get` only (`evidence/logs/cache-*.log`).
* **Exchange.** While delivering I saw the new `prf-long` brief on the exchange (issue base `7b307d62`, additive
  `ℓ`-generic PRF lemmas, no frozen statement change). This fill stays on its issue base and uses only
  `PRF.negligible_prfAdv`, whose statement that brief keeps.

## Evidence

`evidence/SHA256SUMS` lists every evidence file: the inputs, every raw log (bootstrap, checkpoint and
development compiles, the final sweep, censuses, axioms, seals, controls, scans, lint), the probe, seal,
census and control sources (`evidence/scratch-src/`), and the tools (`evidence/tools/`). The top-level
`SHA256SUMS` lists every delivered file except itself. Both manifests were checked to equal the delivered
paths exactly.
