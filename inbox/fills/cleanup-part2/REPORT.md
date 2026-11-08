# Fill `cleanup-part2` — REPORT

**Status: CHECKPOINT 1 (milestones 1–2 complete; J/N inherited reads: explicit lists and C3 clear for
consumers, definitional reads in progress).** Checkpoint 0 (environment and baseline) follows below.

## Identity

| item | value |
|---|---|
| issue pack | `exchange/pass-shelat-ch5-8` at `5b1d70d558542bf491680b4b9ee2379038bbfd3f`, `outbox/fills/cleanup-part2/`; `SHA256SUMS` SHA-256 `078baef661c1152179603b7f1495000fc7287c47164f6fc06baf7b7c855c3e37` (matches the dispatch), all 298 entries OK |
| attachment manifests | `inputs/DELIVERY-MANIFEST.json` `994c8dc0…`, `inputs/INPUTS-MANIFEST.json` `31252c05…`, `external-bootstrap-r1/DELIVERY-MANIFEST.json` `70dd1a40…`, `environment-tools/MANIFEST.json` `40006423…`, `environment-tools/RUNBOOK.md` `4102e174…` — all equal to the brief's pins |
| records snapshot (dispatch) | `0a874231cd3eaa370132970fbf6f5882f5b66e47` on `cryptography/pass-shelat-ch2-4` (cited by the dispatch; not needed for any check) |
| source ancestor | `1aa5506f58f77c215e56d24311ec33bd931cacf1`; `TCSlib/` tree `6ea8b3246478524165b3226c935b12a73853f47b` (verified) |
| fill branch | local `fill/cleanup-part2` in the own clone `/workspace/cp2/src`, created at the ancestor; never rebased/merged; never pushed |
| worker | one Claude session, no subagents or delegated workers |

## Checkpoint 1: milestones 1–2 and the first inherited-read batches

### Commits in this delivery (fill branch `fill/cleanup-part2`, never pushed)

| commit | content |
|---|---|
| `a8a8055ce` | milestones 1–2: canonical block/decoder/state-iterate/average/strategy-next interfaces; DL9–DL17; G7/G10/G18/G25; five M keys; E/F/K/L; PPT relocation (61 files) |
| `34b2f2566` | J batch 1: explicit foreign-definition reads replaced by owner readers (existing and new ordinary readers); Core/Mathlib definitions in simp/rw lists replaced by their lemmas (94 files) |
| `9bcb223ca` | J batch 2a: residual explicit Core/Mathlib/foreign list entries; G23 via `List.count_ofFn`; M `card_QR_prime`/`sq_pow_div_four_succ`; reader dedupe; DL17 tail conversions via `PolyTimeComputable.congr`; long-line wrapping (81 files) |
| `4138d7b7b` | J batch 2b: G13 windows repointed without new general window claims (9 files) |
| `f79962995` | J batch 2a fix: one side condition (`splitAtLastTrue_replicate_succ`) found by the dev pass |
| `2cff020c8` | J batch 2a fix: orientation of the drop-1/tail bridge (`List.drop_one`), found by the dev pass |
| `51c245389` | J batch 2b fix: `dla_blockPos` injectivity spelled through the canonical index equality, found by the dev pass |

The patch series `patches/0001…0007` is the whole `git format-patch 1aa5506f5..51c245389`;
`src/` carries all 221 owned files at `51c245389`.

### Old→new map

The complete source-level declaration map (every removed/moved/header-changed/body-changed and
added declaration of the 221 owned files, with old and new headers/bodies) is
`evidence/maps/old-new-map-checkpoint1.md` (from `tools/surface_diff.py`,
`evidence/logs/surface-cp1.json`, at `2cff020c8`; `51c245389` changes no declaration header). Summary: 162 added (160 public), 23 removed (10 public),
9 moved (all public, same full names), 9 definition bodies changed (6 public), 2 public headers
respelled only by a namespace prefix (`FunFamily.blocks_apply`/`_symm_apply` now declared as
`theorem FunFamily.…` in `namespace TCSlib.Cryptography`; elaborated statements identical).

**Removed public theorems (all on the exception list):** the seven `Complexity.StateLoop`
restatements (X5), `TCSlib.Cryptography.GGMRed.decodeFin_eq_some_iff` and
`TCSlib.Cryptography.negligible_const_zero` (X4), `TCSlib.Cryptography.polyTimeComputable_stateIterate`
(X3; moved as `Complexity.StateLoop.polyTimeComputable_stateIterate`, optional old-name alias not
kept — no remaining user). **Removed private:** `NUPPT.ptc_comp` (Closure), `Collection.ptc_comp`,
`EnsembleLemmas.ptc_comp`, the two file-private `TCSlib.Cryptography.ptc_comp` (Universal,
UniversalLemmas) (X2); `forall_of_uprob_eq_one` (Adversary copy, X4), `FunFamily.decodeFin_eq_some_iff`
(Collections), `Games.eq_ofFn_of_decodeFin` (BitCodec) (X4); `rabin_uexp_le`, `rsa_uprob_pi_eval`
(X8); `dlb_cut` (X7, G10 restriction route); `dlb_count_ofFn` (G23, users call `List.count_ofFn`);
`fac_chunkEquiv` (X1, replaced by `FunFamily.blocks`).

**Moved (same full name and header):** `Complexity.PPT.toNUPPT`, `Complexity.PPT.ofPolyTime`,
`Complexity.PPT.uniform`, `Complexity.PPT.toNUPPT_ofPolyTime` NonUniform → PPT (X10);
`TCSlib.Cryptography.blocksEquivX`, `blocksEquivX_symm_apply` HardCoreGL → Adversary;
`TCSlib.Cryptography.FunFamily.blocks`, `blocks_apply`, `blocks_symm_apply` OneWay → Adversary (X1).

**Public definition bodies changed (all permitted):** `FunFamily.blocks := blocksEquivX q ℓ Bool`
(was the Mathlib curry/fin-product composition, now the generic one specialized); compatibility
one-line aliases `OneWay.blocksE`, `TCSlib.Cryptography.blocksEquiv`, `EnsembleLemmas.blocks`
`:= FunFamily.blocks q ℓ` and `GI.blocksEquiv := (FunFamily.blocks m c).symm` (reverse
orientation kept) (X1); `NUPPT.ofPolyTime` re-expressed through `polyTimeComputable_iff` (same
chosen `M`/`Ct`/`ct` witnesses, same fields; X10). Private: `Ensemble.blocks` (load-bearing
alias for `Ensemble.copies`), `NumberTheory.powOneSubgroup := (powMonoidHom m).ker` (X11),
`dla_blockPos` (G13 named local index, now `finProdFinEquiv (p.1, Fin.castLE hkB p.2)`).

### Milestone 1–2 work packages (routes)

* **DL9/X1 (blocks).** Adversary now owns `blocksEquivX` (generic `Type*` codomain, unchanged
  signature) with readers `blocksEquivX_apply` (block `i`, position `j` reads
  `finProdFinEquiv (i, j)`) and `blocksEquivX_symm_apply` (`p.divNat`, `p.modNat`), and the Bool
  form `FunFamily.blocks` with `FunFamily.blocks_apply`/`_symm_apply`. Aliases keep their
  headers and get `_eq` readers (`OneWay.blocksE_eq`, `blocksEquiv_eq`, `EnsembleLemmas.blocks_eq`,
  `GI.blocksEquiv_eq`, private `Ensemble.blocks_eq`); users read them through the readers, never
  by unfolding. `MultiMsg.take_drop_ofFn_blocks` is a corollary of
  `EnsembleLemmas.take_drop_ofFn_blocks`; `fac_blocks_eq_blocksE`/`blocks_eq_blocksE` go through
  `blocksE_eq`. q = 0 / ℓ = 0 are covered (no positivity hypothesis anywhere).
* **G13 windows (J batch 2b).** The contract of `ColZK.ofFn_drop_take` is relocated, unchanged and
  Bool-valued, to `TCSlib.Cryptography.ofFn_drop_take` in `Asymptotic/CollectionsHelpers.lean`
  (the home X1 names); `ColZK.ofFn_drop_take` keeps its header as a one-line alias and
  `ofFn_drop_eq`/`ofFn_take_drop` are corollaries; Concrete's `dla_take_drop_ofFn`, ColRep's
  `drop_take_ofFn_blockRead` and Primality's `ofFn_chunk` are corollaries of it (Primality now
  imports CollectionsHelpers — acyclic, the latter's closure is contained in the former's plus
  Padding); Concrete's `dla_blockPos` is the canonical index `finProdFinEquiv (t, castLE j)` and its
  injectivity is `finProdFinEquiv.injective` + `Fin.castLE_injective`; Factoring's
  `fac_ofFn_halves` is a corollary of the existing `OneWay.ofFn_block_eq_take_drop` and
  `FunFamily.blocks_apply`; `fac_chunkEquiv` is replaced by `FunFamily.blocks` through a private
  `fac_chunk_eq_blocks` (`chunk_apply`, `blocks_apply`). An earlier draft (commit `9bcb223ca`)
  added generic `take_drop_ofFn`/`take_drop_ofFn_blocksEquivX` window theorems in Adversary; they
  were withdrawn in `4138d7b7b` because X1 makes new general window claims E-API.
* **DL10/X2.** All 26 calls of Closure's private `ptc_comp` and the other private copies go through
  `PolyTimeComputable.comp'`; public `ColMachines.ptc_comp`/`ptcComp` are one-line aliases of it;
  the four `ptc_congr` (GI, ColMachines, ColSimMachine; private GIZK) are one-line
  `hf.congr fun w => (h w).symm` aliases (reversed premise kept).
* **DL11/X3.** `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind` → aliases of
  `Complexity.polyTimeComputable_stateFind`; `Complexity.StateLoop.polyTimeComputable_stateIterate`
  in Repetition after `polyTimeComputable_iterate` (exact X3 type); `dlb_stateIterate_poly`
  derived; `GGMRed.stateLoopFun` untouched.
* **DL13–15/X4.** `PerfectZK.zk` uses `negligible_zero`; Adversary imports
  `HardcoreBit.Basic` for the public `forall_of_uprob_eq_one`; `decodeFin_eq_some_iff` published
  in Adversary (`decodeFin ℓ w = some x ↔ w = List.ofFn x`, all ℓ/w), `ofFn_of_decodeFin_eq_some`
  is its corollary, the Collections/GGM/BitCodec copies are gone.
* **DL17/X5.** Users of the seven restatements call `polyTimeComputable_headD`,
  `polyTimeComputable_isNil`, `polyTimeComputable_not`, `polyTimeComputable_or`,
  `BinArith.polyTimeComputable_xor`, `length_pair_components_le`; the removed `tail_poly` was
  `PolyTimeComputable List.tail` while `Complexity.polyTimeComputable_tail` is stated for
  `fun w => w.drop 1`, so users take `polyTimeComputable_tail.congr fun _ => List.drop_one`
  (StringLoops, which does not import Closure, rewrites with the equality
  `funext … List.drop_one ▸ polyTimeComputable_tail`); StringLoops imports PolyTimeBlockLoop and
  BinaryArith.Basic. `cons_poly` stays. (A first J2a spelling had the orientation reversed; the
  dev pass found it and commit `2cff020c8` fixed it.)
* **D/X6.** PRF: `decodeOracleMove_pairEncode_ofFn` (valid equal-length query),
  `decodeOracleMove_pairEncode_false_of_length_ne` (wrong length → malformed default) and
  `decodeOracleMove_of_ne` (every other word, precisely excluding valid queries and both verdict
  words); with the existing `decodeOracleMove_pairEncode_false`/`_true_two` they partition all
  inputs, ℓ = 0 included; the private `decodeOracleMove_eq` bridge is folded through them.
* **E/F/K/L.** SimulatorMachine imports `Randomized.NonUniform`; the four orbit zero cases use
  `StateLoop.orbit_zero`; Defs D8 paragraph and ModuleHost envelope/`transcriptWith_eq`/`outV_eq`
  prose refreshed (doc-only).
* **G7/G10/G18/G25 (X7–X9).** `permBits_eq` reader, `two_pow_permBits_le`, `two_pow_size_le` via
  `two_pow_size_le_two_mul` (both public statements kept); the three castLE lemmas and the dlb
  restriction via `pushesUniform_restrict`, `pushesUniform_comp_injective` keeps its empty-codomain
  split; `uexp_le_of_statClose` in Sampling with the exact X8 type (no auxiliary lemma), Rabin/RSA
  steps through it; `ColSimMachine.polyTimeComputable_next` in SimulatorMachine before
  `reply_poly`, `ColZK.polyTimeComputable_next` a same-header alias, SimulatorMachine does not
  import ColZKMachine.
* **G23.** `count_true_ofFn` (HardCoreGL) is `List.count_ofFn v true` (TCSlib
  `Programs/Util/List.lean`, now imported by HardCoreGL and DiscreteLogHardcore — the earlier
  "absent at the pin" note was wrong: the lemma is TCSlib's own); `dlb_count_ofFn` removed.
* **M/X11 (all seven keys).** `units_val_mem`, `two_mul_card_le_of_ne_top`, `powOneSubgroup`
  (`(powMonoidHom m).ker`) and `mem_powOneSubgroup` (kernel membership), `fmultNat_eq_mul_prime`
  (Mathlib divisibility), `card_QR_prime` (`QR p` is the range of squaring on the cyclic group
  `(ZMod p)ˣ`: `IsCyclic.card_powMonoidHom_range`, `ZMod.card_units`, `gcd (p−1) 2 = 2`),
  `sq_pow_div_four_succ` (Euler's criterion `ZMod.euler_criterion_units`). Headers unchanged;
  sketches refreshed.
* **PPT/X10.** `PPT.toNUPPT`/`ofPolyTime`/`uniform`/`toNUPPT_ofPolyTime` relocated unchanged;
  owner reader `PPT.toNUPPT_mk`; `NUPPT.ofPolyTime` re-expressed through
  `polyTimeComputable_iff` (the same `Classical.choose` witnesses).

### J/N inherited reads (batches 1, 2a)

* **Explicit lists.** Baseline (`evidence/logs/explicit-scan-baseline-v2.json`, current
  classifier): 668 foreign TCSlib definitions (+6 ambiguous) and 91 Core/Mathlib definitions in
  simp/rw/unfold/dsimp/delta lists of the 97 consumer files (7 more entries are builtin simprocs,
  1 a `let`-bound local). At the head (`explicit-scan-cp1.json`): **0 foreign TCSlib
  definitions, 0 Core/Mathlib definitions** (the 7 simprocs and the local `P` of
  DiscreteLogHardcore remain, correctly classified). Core/Mathlib routes: `Ne` → `ne_eq`,
  `Nat.Coprime` → `Nat.coprime_iff_gcd_eq_one`, `unfold Nat.ModEq` → `Nat.ModEq.eq_of_lt_of_lt`
  (and the RSA step needs no unfolding), `finProdFinEquiv` → `finProdFinEquiv_apply_val`,
  `Function.Injective` → `Function.not_injective_iff`, `List.product` → a `show` step to its
  `flatMap` form (policy: core/Mathlib bodies may reduce in `show`), `Equiv.subtypeProdEquivProd`
  → a `show` step plus `bitsEquiv_val`.
* **New ordinary readers.** 135 generated `<name>_def` equations (rfl, docstring states the
  formula) beside owner definitions that consumers read, plus case/field readers
  (`decodeNat_nil`/`_false_cons`/`_true_cons`, `blockList_zero`/`_succ`, `splitPair_apply`/
  `_symm_apply`, `PPT.toNUPPT_mk`, `pairDecode_nil`, `emitCfg_state`,
  `splitAtLastTrue_of_dropWhile_eq_true_cons`, `polyTimeComputable_iff`, `permBits_eq`, …); the
  complete list with headers is the "Added" part of the map. Three generated readers duplicating
  existing ones (`glPad_def`, `yaoB_def`, `prodFun_def`) were removed in favour of the existing
  `_apply` readers. Provider-only files received only pure insertions (verified: no deleted or
  modified baseline line in any provider file).

### Verification at `51c245389` (checkpoint level)

* **Dev compile of every affected module** (`tools/devrun.sh`, phase `dev`,
  `evidence/logs/checks-dev.jsonl`, log `evidence/logs/devrun-j2.log`): the 528 modules affected
  by J batches 2a/2b (changed + transitive importers of the 81 + 9 changed files) together with
  the 26 J1-affected modules the stopped J1 replay had not reached (554 in current topological
  order). The pass stopped three times on an error of this fill's own edits — module 151
  (`ClassNP/PolyTimePairing`), 382 (`Asymptotic/OneWayLemmas`), 389 (`Candidates/Concrete`) —
  each fixed by the commit named above and resumed at the failing module (logs
  `devrun-j2-part1…3.log`; the first segment's console log was overwritten on the first restart,
  its records are in `checks-dev.jsonl`). Every edit of a resumed run touched only modules at or
  after the resume point, so earlier modules and their objects are unaffected. **Result: all 554
  modules PASS, and for every one the last record's source SHA-256 equals the file at
  `51c245389`** (checked mechanically).
  The stopped J1 replay (`replay-j1-STOPPED`, 240/561 PASS at `34b2f2566`, stopped by the worker,
  module 241 killed — not a failure) is retained; its modules not affected by J2 are unchanged
  since and keep those objects.
* **Root and Checks** (phase `dev`): `TCSlib` PASS (6.8 s); `audits/pass-shelat/Checks` PASS
  (114.4 s, 3,593 MiB). Checks `#print axioms`: 367 records / 364 names, multisets **equal** to
  the baseline (`axioms-checks-cp1-vs-baseline.json`; the same 4 `sorryAx` records).
* **Census at the head** (`evidence/census/j2/`, probe `J2Census`, PASS 287.2 s): 19,962 stored
  constants of the 221 owned modules (baseline 19,932). Axiom comparison by (module, actual Name)
  (`census-axioms-cp1-vs-baseline.json`, `tools/census_axcmp.py`): 179 identities only at the
  base, 209 only at the head, 13 names moved home, **29 = 29 `sorryAx` identities (the same set)**,
  no new identity with `sorryAx`; standard-axiom changes on 5 identities: the private
  `dla_blockPos`, `dla_blockPos_injective`, `dla_take_drop_ofFn` and the public
  `ColZK.ofFn_take_drop` now also use `Classical.choice` (Mathlib's `finProdFinEquiv`/`castLE`
  facts and the relocated window), `NumberTheory.units_val_mem` no longer does (M shortening).
  The removed identities are the removals of the map and their generated equations/auxiliaries;
  the added ones are the new readers/aliases and theirs. **C3**: 102 baseline pairs → **34**
  (68 removed, 0 added); the 34 remaining all have roots in 12 provider-only files (circuits,
  NP, TMSAT, Padding, MathlibBridge, Chebyshev, Programs/Util/List) whose proofs this job may not
  change; **no consumer root references a foreign generated equation** (`c3-cp1-vs-baseline.json`).
* **Whole-file seals at the head, standard variant** (`evidence/logs/seal-j2.json`): the same
  98 files (97 consumers + `ClassNP/PolyTime`), census closure of the head, the standing-rule
  notation `Complexity.PolyExpr.eval` (with its matcher and `_sunfold` auxiliary) left unsealed
  (MAINTAINER-HANDOFF §3 "Notation"). **98/98 valid harnesses** (every request installed, EOF
  reached, no harness diagnostic); 95,177 requests = 94,468 active + 709 already irreducible;
  **365 failing declarations (476 diagnostics) in 73 files**; 25 files without failure
  (`seal-j2-summary.json`; probe sources `evidence/probes/seal-j2-probes.tar.xz`). Of the 506 named J/N work keys, **294 still fail** the seal at this
  head (the strict baseline failed 324 of them); 65 failing declarations are consumer
  declarations outside the key union and 3 are in the provider `ClassNP/PolyTime` (frozen
  proofs).
  **Disclosure:** the checkpoint-0 baseline seal also sealed `PolyExpr.eval`; it is therefore a
  *strict* variant, stricter than the campaign rule, and its 501 failing declarations include
  notation-only failures (≈162 declarations whose every diagnostic mentions `PolyExpr`/`.eval`).
  The final delivery will compare head and base under the same variant(s).
* **Admissions:** lexical occurrences at the head equal the ancestor's per (path, declaration,
  token): 510 `sorry` + 1 `sorryAx` (`tools/admissions.py`, `admissions-cp1.json`).
* **Explicit lists:** 0 foreign TCSlib and 0 Core/Mathlib definitions in the 97 consumer files
  (see above).

### Status of the J/N work and what is in flight

The explicit-list and C3 channels are clear for all consumer files at this head. The remaining
J/N work is the definitional-read channel the seal measures: 294 named keys plus 65 further
consumer declarations still read a foreign TCSlib body by conversion (`rfl`/`show`/`change`,
anonymous-constructor or `rcases` access to a predicate definition, a field of a
structure-valued definition, a foreign `coinLen`/`timeBound` in a type). A J batch 2c is drafted
(39 files, not part of this delivery): predicate `_iff` readers in the providers `Classes`
(`closedUnder*`), `SipserGacs` (`inSigma2`/`inPi2`/`closedUnderShiftOr`), `PPoly`
(`inSIZE_iff`, `inPPoly_iff_inSIZE`), `Adleman` (`verifierHasCircuits_iff`), `PolyTime`
(`polyBound_iff`), `InnerProduct` (`secProb_def`), `GraphIsomorphism/Concrete`
(`prefixLT_apply`/`prefixLE_apply`); field readers (`emitCfg_*`, the GI shadow strategies'
`next`, `giProtocolRep_eq`, `decGraphAt_apply`, …); and the consumer repairs that use them (PPT,
NonUniform, PolyTimePairing, PolyTimeModel, Loops, Machines, HardCore, OneWay, OneWayLemmas,
SoundnessRepGI, Efficiency, …). It is checked next, file by file with sealed probes, then
replayed.

## Checkpoint 0: environment and baseline (complete)

### Mode, paths and preflight

* Default own-clone/own-package mode: one source clone `/workspace/cp2/src` (fresh `git clone` of
  `github.com/Shilun-Allan-Li/tcslib`, branch `fill/cleanup-part2` at the ancestor), its own
  `.lake/packages`, one olean tree `TCSLIB_OLEANS=/workspace/cp2/src/.lake/cleanup-part2-oleans`.
  The exchange checkout `/workspace/tcslib` carries payloads only. A detached drafting worktree
  `/workspace/cp2/draft` (same repository, ancestor commit) held text drafts only; it ran no Lean,
  Lake, cache or package command.
* Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, `memory.limit_in_bytes`
  9223372036854771712 (no effective limit), in use = usage − total_cache + total_shmem =
  38,019,072 B; headroom = `MemAvailable` 16,445,435,904 B = **15.32 GiB** (floor 4 GiB): PASS.
  Clone filesystem ext4 `/dev/vda`, free 19,097,227,264 B = **17.79 GiB** (floor 12 GiB): PASS.
  Clone, `.lake`, olean tree, cache store and `TMPDIR` (unset → `/tmp`) are all on ext4; no tmpfs.
* Toolchain: Lean 4.25.0 (`leanprover/lean4:v4.25.0`, the pin), real binary
  `/root/.elan/toolchains/leanprover--lean4---v4.25.0/bin/lean`, SHA-256
  `8fadc3ed92cc9decb94c96ee9c0876e91e03a3a5e69138f32114f02789e2766c`, already installed under elan
  on this host. The host has no `/usr/bin/time`; the platform equivalent used everywhere is the
  checker wrapper `tools/chk.py`, which records the child tree's peak RSS from `os.wait4`
  (`ru_maxrss`, KiB), the PID, start/end/elapsed, rc, parsed error count, the source SHA-256, the
  direct prerequisites' object paths and SHA-256 (tree, package build dirs, toolchain library),
  and requires a fresh nonempty object (SHA-256 recorded). Ordinary PATH for every check:
  `/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin`.

### Cache and packages

* Cache store before the fetch (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` existed
  with 3,088 files, 148,719,300 B — archives of earlier fill sessions on this host (E-PAD, S2),
  named by hash; not downloaded by this session.
* Narrowed fetch with **all 389 roots** of `external-bootstrap-r1/mathlib-full-union-roots.txt`
  (`evidence/logs/mathlib-roots.txt`), `TAR_OPTIONS=--no-same-owner lake exe cache get <roots>`
  (`evidence/logs/cache-get.log`): the first Lake command cloned the manifest packages
  (PFR, mathlib, LeanAPAP, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq,
  batteries, Cli) at their pinned revisions; "Attempting to download 523 file(s)", 523/523
  downloaded, "Decompressing 3609 file(s)", "Completed successfully!", exit 0. Run alone.
* Package check (`evidence/logs/packages-check.log`): every present package's origin URL and HEAD
  equal `lake-manifest.json`; ABSENT: `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; last
  line "RESULT PASS: every present package matches the manifest". Zero-length package oleans:
  none (`zero-oleans.log`). Cache probe `import Mathlib.Algebra.BigOperators.Field` (first root)
  through the checker: PASS, 24.5 s, 1,662 MiB (`cache-probe.log`).

### External PFR route (31 checks) and owner/identity probe

* Reviewed before use: `environment-tools/prepare_pfr.py`, `pfr_lean.py`, the probe source and
  `RUNBOOK.md` (hashes equal the manifest). `prepare_pfr.py` (`evidence/logs/prepare-pfr.log`)
  verified the 31 source hashes/Git blobs, package pins (all present MATCH, four ABSENT), the
  order and PFR options, and created only `<tree>/PFR -> .lake/packages/PFR/PFR` plus the runtime
  config/entry (config SHA-256 `c0dd0079…`, saved as `evidence/logs/pfr-runtime-config.json`);
  `source_aliases_created: false`, `native_execution_performed: false`.
* **31/31 PFR modules PASS** (`evidence/logs/pfr-bootstrap.log`, per-module logs under
  `evidence/logs/modules/.lake/packages/PFR/…`, records in `checks-checkpoint0-env.jsonl`), in
  `external-bootstrap-r1/bootstrap-order.txt` order, one checker invocation each, the adapter
  PATH scoped to that single invocation (`tools/pfr31.sh` → `tools/chk.py --pfr`); 77.4 s total,
  peak 3,057 MiB; loop stops on the first failure (none).
* **Owner/identity probe under ordinary PATH** (`environment-tools/PFRIdentityProbe.source.txt`
  copied byte-identically to `.lake/cleanup-part2-probes/PFRIdentityProbe.lean`): PASS, 37.0 s,
  2,940 MiB, fresh object SHA-256 `dbfe9657…`; all 31 `PFR-MODULE` headers equal; owners
  `KLDiv` ↦ `PFR.Kullback`, `ProbabilityTheory.entropy` ↦ `PFR.ForMathlib.Entropy.Basic`,
  `ProbabilityTheory.uniformOn_apply_singleton_of_mem` ↦ `PFR.Mathlib.Probability.UniformOn`;
  `PFR-MODULES 31; PFR-PRIVATE 0; EOF` (a zero private count, retained as observed).

### Baseline native replay at the ancestor (complete)

* `inputs/orders/root-prerequisites-order.txt` (1,035 modules) in order, then `TCSlib`, then
  `audits/pass-shelat/Checks` (whose 422 prerequisites are a subset), one checker invocation per
  module (`tools/baseline.sh`, `evidence/logs/baseline-build.log`; per-module logs
  `evidence/logs/baseline/modules/…`; records `checks-baseline.jsonl`; summary
  `baseline-summary.json`).
* Disclosed harness corrections: (1) a first attempt was stopped after 85 modules because the
  wrapper's import parser read a docstring line beginning with "import the" as an import; it is
  kept as `baseline-attempt1-INVALID/` and `checks-baseline-attempt1-INVALID.jsonl` and the run
  was restarted from module 1 with a header-only parser. (2) In the restarted run the wrapper's
  prerequisite resolver did not search the toolchain library, so `TCSlib/Complexity/Formulas/CNF`
  (`import Std.Sat.CNF`) and its 79 dependents were recorded `SKIPPED_MISSING_PREREQUISITES` —
  never compiled, never counted; after the fix `tools/baseline_resume.sh` checked exactly those
  80 modules in root order, then the two aggregates (`baseline-build-resume.log`).
* **Result: all 1,035 root prerequisites, `TCSlib` and `audits/pass-shelat/Checks` PASS** (1,119
  records, 1,037 modules, 82 superseded skip records); peak RSS 4,722,988 KiB; 6,008 s of checks;
  slowest `ClassP/BinaryArith/DetMod` 998.8 s. **No E-BASE.** Checks: 111.3 s, 3,765 MiB.

### Baseline source, admission, axiom, C3, closure and seal data

* Lexical admissions at the ancestor (`tools/admissions.py`, `evidence/logs/admissions-baseline.json`):
  510 `sorry` + 1 `sorryAx` (the quoted Name in `Tactics/Haves.lean`), 0 `admit`/`axiom`
  tokens; the 511 occurrences equal `inputs/lexical-admission-occurrences.json` exactly
  (path, line, column, token), each attributed to its enclosing declaration.
* Census probe (`evidence/probes/BaseCensus.source.txt`, importing all 221 owned modules; PASS,
  289.3 s; outputs in `evidence/census/baseline/`, large tables xz-compressed in the payload):
  name table 374,508 constants (`names.tsv`); **axioms of all 19,932 stored constants of the
  221 owned modules** (private/generated/matcher/axiom-free rows included; `axioms.tsv`):
  6,768 `[propext, Classical.choice, Quot.sound]`, 6,301 axiom-free, 4,969 `[propext, Quot.sound]`,
  1,768 `[propext]`, 72 `[Quot.sound]`, 15 `[Classical.choice]`, 10 `[propext, Classical.choice]`,
  **29 with `sorryAx`**; C3 over the same 19,932 roots: 102 foreign generated-equation reference
  pairs (`c3.tsv`); conservative import-closure seal lists for all 221 owned modules from the
  compiled import table (`closure.tsv`). Earlier census attempts 1–3 are retained as INVALID
  (a misplaced generated command and a shadowing error; a stdout-capture stall; a slow
  per-module closure pass, all killed before completion).
* **Baseline whole-file seals** of the 97 consumer files and the provider `ClassNP/PolyTime`
  (planned reader change) at the ancestor (`tools/mkseal.py`, `tools/sealrun.py`;
  `evidence/logs/seal-baseline.json`, `seal-baseline-summary.json`, probes in
  `evidence/probes/seal-baseline-probes.tar.xz`): seal inserted immediately after the imports;
  constant-AST Name requests (exact components), each checked for existence/home/kind,
  installed-status verified, already-irreducible counted separately, EOF marker; **98/98 valid
  harnesses** (no seal-command diagnostic, EOF reached in all); 90,740 requests = 90,031 active +
  709 already irreducible; **501 failing declarations (688 diagnostics) in 80 files; 18 files
  without failure**. No name/home filter: every non-instance, non-reducible definition (matchers
  included) of the TCSlib import closure is sealed; instances and reducible abbreviations (which
  the attribute cannot seal) are the only kinds not requested.
* Explicit-source baseline (`tools/explicit_scan.py`, `evidence/logs/explicit-scan-baseline.json`)
  over the 97 consumer files: 669 foreign TCSlib definition entries (+6 ambiguous) and 98
  Core/Mathlib definition entries in simp/rw/unfold/dsimp/delta lists; 381 of the foreign ones
  have an existing owner reader (`<name>_def`/`_eq`).

## Work state at checkpoint 0 (historical)

At checkpoint 0 the milestone-1/2 changes were drafted but not yet checked; they are commit
`a8a8055ce` of checkpoint 1.

## Limits of this checkpoint

* The definitional-read channel is open: 365 failing declarations at the head under the standard
  seal (294 of the 506 named keys). Their per-key/per-row dispositions (764 original rows) are not
  yet written; they come with the J/N batches.
* The baseline seal of checkpoint 0 is the strict variant (it also sealed `PolyExpr.eval`); the
  final base/head comparison will state both variants explicitly, and the head is measured here
  under the standard rule only.
* The checkpoint replay is a development pass (`dev` phase, resumed three times after own-edit
  failures) plus root and Checks; the final delivery runs one uninterrupted affected replay.
* Sensitivity controls, the C3 metadata controls, the style/campaign lints and the per-row
  disposition ledger are final-delivery items, not run at this checkpoint.

**Ready for review as checkpoint 1 — all commissioned interface/deduplication/Mathlib/doc targets
implemented and compiled with root and Checks passing (Checks axioms equal to the baseline, no
admission change, C3 clear for consumers); limitation: the inherited definitional-read repairs
(J/N seal channel) are in progress and no per-row disposition ledger is delivered yet.**
