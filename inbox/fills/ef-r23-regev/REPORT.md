# Fill `ef-r23-regev` (EF-R2 + EF-R3, efficiency wave 1): final

**Head `324c5de20c4b5fe1e0ee95a07612d3fa2ffd4b1a`** on the local branch `fill/ef-r23-regev` (not pushed), three
unsigned commits on base IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`. All three series are complete: every target
of the brief is proved, with no `sorry`, no new axiom and no efficiency hypothesis. This payload replaces
checkpoint 1 (head `daaf5e65f753100afc75d8180625c83b8f60e895`, series 1–2; exchange commit
`cad5c7c873d8a0b49d04ead064a59ee10fe284a7`, `fill ef-r23-regev: checkpoint 1`), whose four series-1/2 sources are
byte-identical here.

## Base check

- Inputs: rulings, `COMMON.md` and the brief read at records commit `54dcb3021a389831e7f94c3f82616cb7594fa574`. All nine
  §1 inputs match their SHA-256 (`evidence/logs/inputs-sha256.txt`). The addendum's Part 1 and *Lean parallelism*
  were followed.
- Base: `git rev-parse` of `origin/iO/phase-a-base` gives `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree
  `9155903018d18fbc735791f21485abaaee3e161a`. Both match the brief. No E-BASE.
- `git merge-tree --write-tree 324c5de2… 744441c3a538be2df525b4216b71ff8dbfce6cf5` (records tip at delivery) is clean:
  rc 0, tree `46d49e631456a650549ccd92408775eed8321fc2`. Information only (`evidence/delivery/merge-tree.txt`).

## Heads and commits (`patches/`, `patches/COMMITS.tsv`; signing `none`; `gpgsig` count 0 on each)

| # | Commit | Series | Files |
|---|---|---|---|
| 1 | `c7b2361742bc92d956cbbae438007b37c8070d05` | 1: toolkit | `Encoding/ModularArithmetic.lean` (new, 730 lines), `Encoding.lean` (facade, +3) |
| 2 | `daaf5e65f753100afc75d8180625c83b8f60e895` | 2: Regev symmetric (EF-R3) | `Encryption/Symmetric/Regev/Asymptotic.lean` (new, 310), `…/Symmetric/Regev.lean` (+3) |
| 3 | `324c5de20c4b5fe1e0ee95a07612d3fa2ffd4b1a` | 3: Regev PKE (EF-R2) | `Encryption/PublicKey/Regev/Asymptotic.lean` (new, 423), `…/PublicKey/Regev.lean` (+3) |

`git diff --stat 5ed465f6..324c5de2` lists exactly the brief's six files: 1,463 new Lean lines in the three new files,
within the brief's 1,100–1,900. `TCSlib.lean` is unchanged.

## Environment, pool and memory

- Cloud container (`evidence/logs/preflight.log`): `nproc` 4. No cgroup memory controller, so the headroom is
  `/proc/meminfo` MemAvailable: 15.86 GB of 16.47 GB at preflight. Disk: ext4, 27.4 GB free at preflight. No E-RES.
- Toolchain: elan with `leanprover/lean4:v4.25.0`. Narrowed Mathlib cache, `lake exe cache get` run alone:
  - 92 roots: 2,345 files downloaded (`cache-get.log`, rc 0). The store was absent before (`cache-store.log`).
  - Later one disclosed new root, `Mathlib.Data.Fin.Tuple.Take` (series 3 imports it): 1 file
    (`cache-get-2.log`, rc 0).
- Packages: every present package matches the manifest. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`
  are ABSENT (`packages-check.log`). There are 0 empty oleans. A cache probe importing the first root has rc 0.
- Pool (`evidence/logs/pool.log`): 3 processes, `min(4, 15.5 GB / 4 GB)`. It rose briefly to 4 (3 bootstrap plus 1
  interactive check) with MemAvailable 14.9 GB. The seal runner used 3.
- Peak memory: 3.09 GB per Lean process, measured by wait4 `ru_maxrss` on `Candidates/Rabin` during the bootstrap
  (`evidence/bootstrap/summary.tsv`). No shortage, no OOM, no exit 137.
- Bootstrap: the 220-module import closure, in dependency order with a 3-process pool (`tools/pool_build.py`), all
  rc 0. Final build: the 227-module closure of the facades, the 6 changed modules rebuilt fresh.

## Who did what

- **Lead (this session):** all Lean code, every Lean run (builds, probes, collector, seals, controls, scan), every
  `lake` command (two narrowed cache fetches), every commit, the delivery, and this report.
- **Sub-agent `tools-agent`:**
  - Ran no Lean or `lake` and made no git writes. Wrote only under `tools/agent/` and its log directory.
  - Adapted the bb1-machine seal suite: the Rule-10 driver `rule10_regev.sh`, the runner `runner_regev.py` (no host
    lock, `RULE10_JOBS` processes) and the controls generator `mkctl_regev.py` (rows in `control-rows.tsv`).
  - Wrote the clash scan, the frozen-facade check and the overlap search, each with controls.
  - Log: `evidence/subagents/tools-agent/log.md`, with `files.sha256` over its 221 files.
- **Lead changes to the agent's tools:**
  - Fixed a bug in `rule10_regev.sh` phase `collect-check`: compressed JSON lists `"closure"` before `"module"`.
    The fix is commented in place.
  - Added four series-3 rows to `control-rows.tsv`.
  - All tools used are under `evidence/tools/`.

## Target map

| Brief target | Declaration(s) | File:line |
|---|---|---|
| `addModPoly` | `addMod`, `addMod_eq`, `addMod_pairEncode`, `addMod_length`, `addMod_natToList`, `polyTimeComputable_addMod` | `Encoding/ModularArithmetic.lean:76`ff |
| `vecAddModPoly`, `vecAddModPoly_encodeVector`, `polyTimeComputable_vecAddModPoly` | `vecAddStep` (+`_eq`, `_fst`, `_length_le`, `polyTimeComputable_vecAddStep`), `vecAddModWords` (+`_eq`, `_length`), `polyTimeComputable_vecAddModWords`, `vecAddModWords_encodeVector`, `vecAddModWords_modContext` | `:155`–`:325`, `:688` |
| `subsetSumModPoly`, `subsetSumModPoly_encode` and polynomial-time theorem; the scalar `⟨b, r⟩ mod q` | `subsetSumStep` (+`_eq`, `_fst`, `_length_le`, `_iterate_length_le`, `polyTimeComputable_subsetSumStep`), `subsetSumModWords` (+`_eq`), `polyTimeComputable_subsetSumModWords`, `subsetSumModWords_encodeMatrix` (`= encodeVector w (Aᵀ *ᵥ r)`), scalar: `subsetSumModWords_encodeVector`, `_modContext`, `_modContext_vector` | `:331`–`:640`, `:700`–`:719` |
| (shared context, see *Statement changes*) | `modContext`, `modContext_eq`, `modContext_length`, `listToNat_modulusNumeral` | `:647`ff |
| `exists_shiftMachine` | `exists_shiftMachine` (**equality**, the brief's form verbatim). Ingredients: `shiftAdvice` (+`_eq`, `_length`, `_length_le`), `shiftPre` (+`_eq`), `shiftPre_shiftAdvice`, `polyTimeComputable_shiftPre`, `shiftAdviceBound` (+`_eval`) | `Encryption/Symmetric/Regev/Asymptotic.lean:228`; `:71`–`:202` |
| `singleMessageSecure_of_dlweAssumption` | `singleMessageSecure_of_dlweAssumption` (the brief's form verbatim) | `…/Symmetric/Regev/Asymptotic.lean:284` |
| `encodeView` with `encodeView_eq`, `encodeView_length` | `encodeView`, `encodeView_eq`, `encodeView_length` (injectivity is not used, so not added) | `Encryption/PublicKey/Regev/Asymptotic.lean:73`–`:93` |
| `exists_reductionMachine` | `exists_reductionMachine` (**equality**, verbatim). Ingredients: `encryptAdvice` (+`_eq`, `_length`, `_length_le`), `encryptPre` (+`_eq`), `encryptPre_encryptAdvice`, `polyTimeComputable_encryptPre`, `encryptAdviceBound` (+`_eval`) | `…/PublicKey/Regev/Asymptotic.lean:298`; `:106`–`:268` |
| `singleBitSecure_of_dlweAssumption` | `singleBitSecure_of_dlweAssumption` (verbatim, `hm` as #377 A1) | `…/PublicKey/Regev/Asymptotic.lean:397` |

The full list of 62 new public constants, each with its full name and elaborated type (`#check @…`, `pp.fullNames`),
is the StmtDump in `evidence/axioms/axioms-stmtdump.log`. `decls2.py` reports 62 ADDED, nothing else
(`evidence/statements/decls2.txt`).

## Statement changes

1. **Toolkit names and argument form.**
   - Old: `addModPoly`, `vecAddModPoly`, `subsetSumModPoly`, "polynomial-time string maps on `⟨q, ⟨u, v⟩⟩`".
   - New: `addMod`, `vecAddModWords`, `subsetSumModWords` with the leaf steps `vecAddStep`, `subsetSumStep`. Every
     size is read from words in the input: the context `⟨c, qw⟩`, with width `|c|` and modulus `qw` as an MSB
     numeral of any length, plus the counters `n`/`nT`, `mT`.
   - Reason: in a `Poly` map (the dyadic precedent) the width and counts are `PolyExpr`s of the input length. Here
     `q`, `n`, `m` and the width are the reduction's advice and are not functions of the input length (Q-R-2 A,
     general `q`). The modulus numeral may be longer than the width, so `q = 2^w` is allowed.
   - The correspondence lemmas are the brief's: `vecAddModWords_encodeVector` ends in `encodeVector |c| (u + v)`, and
     `subsetSumModWords_encodeMatrix` ends in `encodeVector |c| (A.transpose.mulVec (fun i => (r i).toNat))`. Each
     also has a `_modContext` form at width `w`.
2. **Subset bits may run longer.** The subset-sum correspondence takes the bits `ofFn r ++ extra`. The PKE machine
   draws `S(κ) ≥ m` subset coins and reads the first `m`. This is a strengthening.
3. **The scalar `⟨b, r⟩ mod q`** is the one-column case `subsetSumModWords_encodeVector`, not a separate map: the
   rows of an `m × 1` matrix are the residues. This avoids a second loop.
4. **New context helper `modContext w q = ⟨0^w, natToList (w + 1) q⟩`.** It has readers `modContext_eq`,
   `modContext_length`, `listToNat_modulusNumeral`, and specialised correspondences. It is written once, public, and
   used by series 2 and 3. Otherwise each series would have built the same word privately.
5. **Pre-processing ingredients are public definitions with readers.**
   - `shiftAdvice`, `shiftPre`, `shiftAdviceBound`; `encryptAdvice`, `encryptPre`, `encryptAdviceBound`.
   - They are the advice encodings and pre-targets that `exists_realizesOn_of_preTarget_id` needs. Each has its `_eq`
     or `_eval` reader, its length, and its correctness and polynomial-time theorems.
6. **Must-reuse items not used.** The four targets are stated exactly as in the brief, `=` rather than `≤`. The listed
   `RealizesOn.runAt_coinsEquivPoly_symm` and `PrivateKeyScheme.acceptProb_distinguisherL_congr` were not needed:
   - the symmetric transport is `RealizesOn.distinguisherL_eq` with `NUPPT.coinsCongr`/`runAt_coinsCongr` and
     `EnsembleLemmas.acceptProb_coins_equiv`;
   - `acceptProb_distinguisherL_congr` needs agreement on every coin string, but `RealizesOn` gives it only on strings
     of the layout's length.

No target was weakened. There is no E-FALSE.

## The reductions: advice and coin layout

| | Symmetric (`exists_shiftMachine`) | PKE (`exists_reductionMachine`, per bit `μ`) |
|---|---|---|
| Reduction advice (inside the reduction function) | `shiftAdvice P w (μ κ)` = `⟨⟨modContext w q, 1^m⟩, ⟨1^{m n w}, encodeVector w (codepoint ∘ μ κ)⟩⟩`. For `singleMessageSecure`, `μ κ` is the worst message at `κ` (an averaging choice), so non-uniform | `encryptAdvice P w μ` = `⟨⟨modContext w q, ⟨1^n, 1^m⟩⟩, ⟨1^{m n w}, natToList w (codepoint μ).val⟩⟩` |
| Its exact length | `2mnw + mw + 2m + 12w + 20` (`shiftAdvice_length`) | `2mnw + 4n + 2m + 13w + 24` (`encryptAdvice_length`) |
| `PolyExpr` bound | `shiftAdviceBound F = 2·S·D·R + S·R + 2·S + 12·R + 20` (`S`, `D`, `R` = `samplesBound`, `dimensionBound`, `residueBits`) | `encryptAdviceBound F = 2·S·D·R + 4·D + 2·S + 13·R + 24` |
| Machine advice | `⟨⟨1^κ, D.advice κ⟩, shiftAdvice …⟩` from `exists_reparam_pre_post` (through `exists_realizesOn_of_preTarget_id`), bound `4·var + 6 + 2·D.adv + b` | that of the realiser `B` (same form, `b = encryptAdviceBound F`). `NUPPT.exists_split` keeps it |
| Coins of `D'` | `D'.coins = D.coins`: all coins go to `D` unchanged (`coinsCongr`) | `D'.coins = S + D.coins` (`samplesBound + D.coins`). The first `S(κ)` coins are the subset string: its first `m` bits are `r`, the other `S(κ) − m` are unread. The remaining `D.coins(κ)` go to `D`. The relabelling `((t, v), u) ↦ t ++ u ++ v` (`Fin.appendEquiv`, `finCongr`) plus `acceptProb_coins_fst` removes the unread bits |
| Machine construction | `exists_realizesOn_of_preTarget_id` with `shiftPre` | `exists_realizesOn_of_preTarget_id` with `encryptPre` on challenges `⟨encodeChallenge pk, s⟩`, then `NUPPT.exists_split B samplesBound` |

The honest algorithms' efficiency and the scheme instances (EF-H5/EF-H6) are untouched. The statements are over the raw
`LWE.Family` (Q11 A). No hypothesis is an efficiency claim.

## Checks

| Check | Result | Evidence |
|---|---|---|
| **C1 Build** | The 6 changed modules and the 2 downstream facades: rc 0, 0 errors in both forms (`error:` and `error(`), 0 `sorry` warnings. Every source's SHA-256 equals `git show HEAD:<path>` | `build/summary.txt`, `build/final/*.log`, `build/downstream/*.log` |
| **C2 Downstream** | Direct importers of the changed facades: `Encryption/Symmetric.lean` rc 0, `Encryption/PublicKey.lean` rc 0. The root `TCSlib.lean` (it imports `Encoding`) was **not built**: its closure needs the PFR package's oleans (`PFR.Kullback`, `PFR.ForMathlib.Entropy.Basic`, …), which the Mathlib cache does not provide and which only a package build (banned) would produce. Recorded as not run, not as a failure; see EF-R23-W1. `Encryption.lean` (which imports the two facades) was not rebuilt either | `build/downstream/`, `logs/roots-root.txt`, `logs/order-root.txt` |
| **C3 Statements** | `decls2.py . 5ed465f6 <6 files>`: 62 ADDED, the facades add no declarations. StmtDump of all 62 | `statements/decls2.txt`, `axioms/axioms-stmtdump.log` |
| **C4 Admissions** | 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque` and 0 `@[simp]` in the new files. Per-file `sorry` counts are identical at base and head | `admissions/admissions.txt` |
| **C5 Axioms** (and **R-P3**) | All 62: a subset of `propext`, `Classical.choice`, `Quot.sound`. The four headline theorems use exactly those three. 0 non-standard | `axioms/axioms-summary.txt` |
| **C6 Rule 10** | Collector over the six owners: 1,592 catalogue rows, `COLLECT_OK 1`. **24 seal probes** (6 owners × strict/coe × A/B, `lean -DmaxErrors=0`): rc 0, 0 errors in both forms, install and EOF records present, **0 failing declarations**. Requests (coe-A canonical): `ModularArithmetic` 1011, `Encoding` 1121, `Symmetric.Regev.Asymptotic` 1131, `Symmetric.Regev` 1134, `PublicKey.Regev.Asymptotic` 1145, `PublicKey.Regev` 1149 (strict and B: +1/+2). **Paired controls**: 13 targets (every new public definition), 26 controls. Unsealed pretest all pass. Strict and coe sealed `ALL_OK True`: each negative (`rfl` read through the body) fails exactly once, each positive (through the reader) passes. **Explicit-unfold scan**: 363 items, **0 foreign**. **Reader census**: 55 foreign definitions referenced, each read through its published reader or only used as a term; **0 MISSING** | `rule10/rule10/seals-{A,B,coe-A,coe-B}.tsv`, `ctlcheck-{strict,coe}.{log,json}`, `pretest/`, raw logs `seal-runs/mods/`, `scan/`, `rule10/reader-census.tsv` |
| **C7 Frozen** | The three facades reproduce the base byte for byte once the allowed import and bullet lines are removed: `RESULT PASS`, 0 declarations either side. Mutation controls `ALL_CONTROLS_OK True` (one altered character gives exactly one difference). `git diff --stat` shows only the six files | `frozen/`, `logs/frozen*.out` |
| **C8 Lint** | `style_lint.py` on the six files: 0 findings. `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 103 WARN over 542 files (the maintainer's IO figure); head 92 / 103 over 545. The FAIL/WARN line sets are identical: no new FAIL or WARN | `lint/` |
| **C9 Sizes** | Lines 730 / 310 / 423 (new); facades 38 / 25 / 27. Maximum width 100 | `lint/sizes-widths.txt` |
| **C10 Clashes** | 62 names, **0 full-name clashes** in `TCSlib/`/`audits/` at the base, at #377 `7563734a…` and at `cleanup/stage2-s2a` `c119a3c4…`. Three short names also exist elsewhere, all in #377's `GSW/Asymptotic.lean`: `encodeView` (:96), `encodeView_eq` (:100), `encodeView_length` (:104). Their unqualified uses occur only in the PKE file itself, inside its own namespace; no downstream module uses them unqualified. Controls `ALL_CONTROLS_OK True` | `clash/`, `logs/clash*.out` |
| **C11 Reuse and overlap** | See below | `subagents/tools-agent/overlap/` |
| **C12 Probes** | **R-P1** (`#eval`, evidence only): `vecAddModWords` and `subsetSumModWords` against `ZMod` addition and `Aᵀ *ᵥ r`, for `q ∈ {2, 3, 5, 7, 8, 12}`, lengths ≤ 3 (all pairs up to the first 400 per length), rows ≤ 3, columns ≤ 2, all bit vectors, with trailing extra bits. 0 mismatches over 4,062 vector and 7,672 subset cases. Malformed inputs are total. **R-P2**: toy family `n = 1`, `m = 2`, `q = 5`, width 3. The machines realise `D.runAtL κ (pre ⟨advice, encoding⟩) …`, so the probe compares each pre-processing on encodings with the encoding of the reduction's input: `shiftPre` against `encodeChallenge (shift μ c)` over all 2,500 (challenge, message) cases, and `encryptPre` against `encodeView (view μ pk r)` over all 5,000 (key, bit, subset) cases. 0 mismatches. The NUPPT itself is not evaluated (`#eval` of its Turing machine would only re-run `D`) | `probes/toolkit-probe.log`, `probes/ToolkitProbe.lean.txt` |
| **C13 Reproduction** | `git am` of `patches/` at the base in a scratch worktree, with `COMMITS.tsv`'s committer data, reproduces all three hashes. `src/` equals the head's files byte for byte | `delivery/git-am-reproduction.txt` |
| **R-P3** | see C5 (R43/R44 become class **M**) | `axioms/axioms-summary.txt` |

## Overlap and reuse

- **Searches**: `evidence/subagents/tools-agent/overlap/search.log` records every command, its hit count and the
  hits. `run-summary.txt` has one line per search, and `overlap.md` summarises. They cover:
  - base `5ed465f6` and #377 `7563734a`, by `git grep`;
  - Mathlib sources, by plain grep;
  - the lead's own name, `exact?`-style and shape searches while writing.
- **No restatement found.**
  - There is no general-modulus vector arithmetic, `addMod`-like or `modContext`-like helper, and no `mod ∘ add`
    composition on encodings, at the base or at #377.
  - There is no `NUPPT`/`RealizesOn` in either `Regev/` folder.
  - Mathlib has no `mulVec` over `ZMod` on encodings.
- **Must-reuse items and where they are used:**
  - `exists_realizesOn_of_preTarget_id`: both machines.
  - `RealizesOn.distinguisherL_eq`, `coins_eq`, `runAtL_eq`: symmetric verdict; PKE `hrun`.
  - `LWE.Family.advantageAt_eq`, `dlweAssumption_iff`, `encodeChallenge_eq`/`_length`: throughout.
  - `shift_fst`/`_snd`, `encryptDist`, `distAdv_encrypt_le` (symmetric).
  - `view_fst`/`_snd`, `realView`, `reduction_eq`, `distAdv_encrypt_le`, `two_extractionError_le`, `encrypt_fst`/`_snd`
    (PKE).
  - `encodeVector`/`encodeMatrix` with `_eq`/`_length`.
  - `BinArith.add`/`mod` with `add_pairEncode`/`mod_pairEncode`, `forLoop`, `forLoop_pairEncode`,
    `polyTimeComputable_forLoop`, `forLoop_bound_of_ctx`, `mulU`.
  - `toLE`, `fromLEPoly`.
  - `negligible_two_pow_neg`, `Negligible.add`/`mono`.
  - `NUPPT.exists_split` (`Complexity/Randomized/Closure.lean:390`) for the subset coins.
  - Not used: `polyTimeComputable_iterate` (`forLoop` is built on it), `normalizeWidthPoly`, `codepoint_eq` and
    `ModularDecode` (no decoding in a machine).
- **Near relatives** (`path:line` at the base unless marked):

| New | Relative | Relation |
|---|---|---|
| `addMod` | `Encoding/DyadicArithmetic.lean:61` `addPoly` | dyadic analogue (mod `2^W`, width from a `PolyExpr`); same adapter pattern (`toLE`, `fromLEPoly`) |
| `vecAddStep`, `vecAddModWords` | `Encoding/DyadicLinearAlgebra.lean:50` `dotStep`, `:120` `dotWords` | same counted-loop host and layout (`⟨ctx, ⟨x, ⟨y, acc⟩⟩⟩`); different operation and modulus |
| `subsetSumStep`, `subsetSumModWords` | `DyadicLinearAlgebra.lean:271` `matVecStep`, `:342` `matVecPoly` | same row-loop pattern; computes `Aᵀ *ᵥ r` modulo a general `q`, with a branch on the selector bit (`polyTimeComputable_ite`). `matVecPoly` computes `A *ᵥ v` modulo `2^W` |
| `subsetSumStep_iterate_length_le` | `ClassP/BinaryArith/Loops.lean:165` `length_iterate_le_of_ctx` | a variant for quadratic per-step growth. The registered lemma covers only linear growth `A·(|ctx| + 1)`, and a subset step may grow the accumulator by `|nT|·|c|`. A local theorem (not private), proved directly; not a host |
| `exists_shiftMachine` (coin transport) | `EnsemblesLemmas.lean:85` `acceptProb_coins_equiv` (used); `Asymptotic/ReductionSupport.lean:221` (a pre-existing duplicate, not used) | reuse |
| `exists_reductionMachine` (coins) | `EnsemblesLemmas.lean:92` `acceptProb_coins_fst`, `UniversalLemmas.lean:273` `exists_ofFn_eq_of_length`, Mathlib `Fin.appendEquiv`, `List.ofFn_fin_append`, `Fin.ofFn_take_eq_take_ofFn` | reuse |
| `singleMessageSecure_of_dlweAssumption` (worst message) | `Encryption/PrivateKey/FromPRG.lean:295` `prgScheme_singleMessageSecure` (`Finset.exists_max_image`, `exists_withAdvice`) | same averaging pattern, cited in the module docstring. The worst message enters the reduction function's advice (`shiftAdvice`), as `Realization.lean` prescribes |
| `encodeView`, `encodeView_eq`, `encodeView_length` | #377 `AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:96`, `:100`, `:104` (the GSW `encodeView`) | analogue in another namespace for the GSW view. Nothing is shared or copied. Short-name overlap: see C10 |
| `exists_reductionMachine` | #377 `GSW/Asymptotic.lean:216` `ReductionEfficient` (hypothesis A4) | the Regev analogue, proved rather than assumed. #377's `ReductionEfficient` would need the same toolkit for GSW (EF-R1) |
| `shiftAdviceBound`, `encryptAdviceBound` | `LWE/Assumption.lean:88` `Family.inputBitsBound` | same style of syntactic polynomial bound with an evaluation reader |

There is no `private` declaration in any new file, and none was copied across files.

## Scope requests

None. No frozen file needed changing. No unregistered host is used: the loops are `BinArith.forLoop`, the branch is
`polyTimeComputable_ite` and the cuts are `pairTakePoly`/`pairDropPoly`.

## Questions for Seyoon

**EF-R23-W1. The root `TCSlib` check of C2.**
- **A (recommended).** Accept the downstream evidence as delivered, and let the maintainer run the root build at
  landing with the PFR package oleans available. The delivered evidence is the two direct-importer facades, rc 0.
  `TCSlib.lean` itself is unchanged; it reaches the new modules only through the `Encoding` facade.
- **B.** Authorize a PFR package build on a host where `lake build` of a dependency package is allowed, and re-run
  the root.

**EF-R23-W2. Toolkit naming.**
- **A (recommended).** Keep the `…Words` names (`vecAddModWords`, `subsetSumModWords`): sizes come from input words,
  not `PolyExpr` schedules.
- **B.** Rename to the brief's `…Poly` names in a landing edit.

## Evidence manifest (`evidence/`, checksums in `evidence/SHA256SUMS`)

- `logs/`:
  - inputs and environment: `inputs-sha256.txt`, `preflight.log`, `pool.log`;
  - cache and packages: `cache-store.log`, `cache-get.log`, `cache-get-2.log`, `mathlib-roots*.txt`,
    `packages-check.log`, `cache-probe.log`;
  - orders and roots: `prefix-order.txt`, `order-final.txt`, `order-root.txt`, `roots-*.txt`;
  - check logs: `bootstrap.log`, `rule10-*.out`, `frozen*.out`, `clash*.out`, `overlap.out`.
- `bootstrap/`: the per-module logs and `summary.tsv` (start, end and `maxrss` per module).
- `build/`: `summary.txt` (C1), `final/`, `downstream/`.
- `statements/`: `decls2.txt`, `new-names.txt`.
- `axioms/`: StmtDump with axioms (`axioms-stmtdump.log`), `axioms-summary.txt`, the probe source.
- `admissions/`, `lint/`, `frozen/`, `clash/`, `scan/`, `probes/`.
- `rule10/`:
  - collector: `rule10/probe-runs/`;
  - seals: `rule10/seals*/`, the raw logs `rule10/seal-runs/mods/` and `results.jsonl`;
  - summaries: `rule10/seals-*.tsv`;
  - controls: `rule10/controls-*`, `ctlcheck-*`, `pretest/`;
  - `statements/touched-after.json`, `reader-census.tsv`.
  - The `seals-flat/` and `seals-coe-flat/` copies made by the driver were left out: they are byte copies of
    `seals/{A,B}` and `seals-coe/{A,B}`.
- `subagents/tools-agent/`: the sub-agent's log, `files.sha256` and overlap search.
- `delivery/`: `git-am-reproduction.txt`, `merge-tree.txt`.
- `tools/`:
  - `pool_build.py`, `closure.py`, `bisect.py`, `width.py` (lead);
  - `agent/` (the sub-agent's tools with the lead's fix);
  - `seal-src/`: the bb1-machine seal suite as fetched from the exchange (`inbox/fills/bb1-machine/evidence/tools/`),
    unchanged.
