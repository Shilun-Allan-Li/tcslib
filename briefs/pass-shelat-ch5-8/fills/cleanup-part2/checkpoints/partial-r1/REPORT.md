# Fill `cleanup-part2` — REPORT

**Status: FINAL DELIVERY — PARTIAL, not final-complete.** Milestones 0–2 and the E/F/K/L items
are complete. The frozen final head `03ead73ab` passes the full affected replay, `TCSlib` and
`audits/pass-shelat/Checks`. Its axioms and admissions equal the baseline. The explicit-list and
C3 channels are clear for every consumer file, and the sensitivity and C3 controls pass.

The J/N inherited-read ledger is **not** closed: **173 of the 509 work keys (152 of the 764
historical rows) still fail the whole-file seal**. Each one is listed with its exact
diagnostic, class and next step. Checkpoints 1 and 0 follow at the end as history.

## Identity

| item | value |
|---|---|
| issue pack | `exchange/pass-shelat-ch5-8`, `outbox/fills/cleanup-part2/`. Pins verified at checkpoint 0: `SHA256SUMS` `078baef6…`, 298/298 OK; manifests `994c8dc0…`, `31252c05…`, `70dd1a40…`, `40006423…`; RUNBOOK `4102e174…` |
| source ancestor | `1aa5506f58f77c215e56d24311ec33bd931cacf1` (TCSlib tree `6ea8b324…`) |
| **final head** | **`03ead73ab38e74621800367c072f6fd3f0f70991`** on the local branch `fill/cleanup-part2`; never pushed, rebased or merged |
| patch series | `patches/0001…0013`: the whole `git format-patch 1aa5506f5..03ead73ab` (13 commits) |
| changed paths | 122 `.lean` files, all in `inputs/owned-files.txt`. 26 of them are provider-only files, changed by pure insertion (no baseline line deleted or modified). No file was added or deleted |
| `src/` | final bytes of all 221 owned paths at `03ead73ab` |
| worker | one Claude session; no subagents or delegated workers |

## Commits

| commit | content |
|---|---|
| `a8a8055ce` | Milestones 1–2: canonical block/decoder/state-iterate/average/strategy-next interfaces; DL9–DL17; G7/G10/G18/G25; five M keys; E/F/K/L; PPT relocation |
| `34b2f2566` | J batch 1: explicit foreign-definition reads now go through owner readers; Core/Mathlib definitions in simp/rw lists now go through their lemmas |
| `9bcb223ca` | J batch 2a: residual explicit entries; G23 (`List.count_ofFn`); M `card_QR_prime`/`sq_pow_div_four_succ`; DL17 tail bridges; line wrapping |
| `4138d7b7b` | J batch 2b: G13 windows, with no new general window claims |
| `f79962995`, `2cff020c8`, `51c245389` | Fixes from the 2a/2b development pass (the checkpoint 1 head) |
| `b37d89d59` | J batch 2c: predicate/field/case readers beside owners, and consumer repairs through them (39 files) |
| `59541f413` | J batch 2d: RSA, Rabin, DiscreteLog, Generators, both Encryption files, HardCoreGLColl/Permutation, SimulatorLemmas, ColMachines, Parties |
| `49e1a868d` | J batch 2e: NextBit, OneWay, Collections(+Helpers), Universal*, Indistinguishability, BlockEncryptor, Encoding, GI Proofs/Efficiency/Soundness, GIZK Simulator, 3COL Language/Protocol/ProtocolProofs, Commitment, HardCore, NP, Extractors |
| `669f3c929` | Proof sketches for three proofs the repairs lengthened past 20 lines (docstrings only) |
| `ea37eb57c` | SoundnessRepGI now reads `Fin.init` in a `show` step instead of a `rw` list entry. Found by the final explicit pre-scan |
| `03ead73ab` | **Final head.** Repairs three foreign reads that the X1 block relocation created in unchanged consumer blocks (`HardCoreGL.glBlocks_apply`, `OneWay.pushesUniform_pbOf`, the `yaoRaw'` block step). Found by comparing the strict seal of the head with the strict seal of the base |

## Work packages: status

| package | status |
|---|---|
| A (DL9/G13, DL10, DL11/G22, DL13, DL14, DL15) | done (routes as at checkpoint 1; see the history section) |
| B (DL17) | done |
| C | verification only: the PPT readers exist and Closure uses them; nothing added |
| D (PRF `decodeOracleMove` readers), E (NonUniform import), F (four orbit zero cases) | done |
| N (G7, G10, G18, G25; `distAdv_sunglassRed`) | done. `distAdv_sunglassRed` reads `distAdv_def`, and Indistinguishability passes the final seal |
| M (seven keys) | done |
| K/L (Defs D8, ModuleHost envelope, `transcriptWith_eq`/`outV_eq` docs) | done (doc-only; headers and proofs byte-identical) |
| **J/N inherited reads** | **partial.** Explicit-list channel: 446/446 historical unfold rows closed (444 repaired, 2 removed by exact mapping); 0 foreign TCSlib and 0 Core/Mathlib definitions remain in any consumer list. C3 channel: 53/53 eqn-term rows closed; 0 consumer C3 pairs. Seal channel: 112 rows repaired, 1 removed, 152 open |
| Milestone 4 (frozen final verification) | done at `03ead73ab` (below) |

## Old→new map and public exceptions

The complete source-level map is in `evidence/maps/old-new-map-final.md`, built by
`tools/surface_diff.py` + `tools/surface_map.py` (raw data: `evidence/logs/surface-final.json`).
It covers the 221 owned files from `1aa5506f5` to `03ead73ab`.

| change | all | public only |
|---|---|---|
| added | 219 | 217 |
| removed | 23 | 10 |
| moved | 9 | 9 |
| definition bodies changed | 9 | 6 |
| headers changed | 2 | 2 |

The removed, moved, body-changed and header-changed sets are **identical to checkpoint 1**, and
each item lies on the exception list (X1–X5, X7, X8, X10, X11), as recorded there. The two
header changes are namespace respellings only. Since checkpoint 1, the only changes are added
ordinary readers (58) and proof repairs.

The readers added since checkpoint 1 are each an `rfl`/`Iff.rfl` equation, iff, field or case
reader beside an existing owner:

* **Providers** (X12, pure insertion):
  * PPoly `Language.inSIZE_iff`, `inPPoly_iff_inSIZE`
  * PolyTime `polyBound_iff`; Reductions `polyTimeReducible_iff`
  * Adleman `verifierHasCircuits_iff`
  * Classes `closedUnder{AnswerIs,Any,Majority,Not,Race}_iff`
  * SipserGacs `inSigma2_iff`, `inPi2_iff`, `closedUnderShiftOr_iff`
  * Convention `splitAtLastTrue_of_dropWhile_eq_nil`/`_false_cons`
  * Wrappers `emitCfg_inputPos`/`_workTapes`/`_workTapePos`/`_output`
  * Adversary `padFin_apply`; InnerProduct `secProb_def`
  * GI Concrete `prefixLT_apply`/`prefixLE_apply`; LeftoverHash `hashPair_eq`
* **Consumer owners:**
  * PPT `runLit_eq`, `computes_iff`
  * Encryption `singleMessageSecure_iff`
  * HardCoreLemmas `finCastEquiv_apply`, `coe_finCastEquiv`
  * Permutations `permTrials_eq`
  * Encoding `decColoring_val_eq`, `decGraph_fst`, `decGraph_snd_apply`
  * Language `edgeOf_eq`, `threeColorable_iff`; ColMachines `argX_eq`
  * GI Proofs: `decGraphAt_apply`, `decGraph_eq_decGraphAt`, `encInstance_eq`, `instanceG₀_def`/`instanceG₁_def`, `samplePerm_def`, `isomorphic_iff`, `mem_Liso_iff`, `mem_Lniso_iff`, `riso_iff`, `gniProver_next`, `giProverRep_next`, `giVerifierRep_next`, `giProtocol_P`/`_V`, `gniProtocol_P`/`_V`, `gniProtocolRep_V`, `giProtocolRep_P`/`_V`/`_rounds`/`_verifierFirst`

None carries `@[simp]`. No PR #232 reader inventory was supplied, so the worker cannot name the
counterparts; the maintainer reconciles them at landing.

## Final verification at `03ead73ab`

### Native replay, root and Checks

* **Full affected replay at `ea37eb57c`** (`tools/replay_affected.sh final`;
  `evidence/logs/replay-final.log`, `checks-final.jsonl`, per-module logs under `logs/final/`).
  * The changed modules plus all their transitive importers, including facades, in the current
    topological order (`order-final.txt`, `affected-final.txt`): **581/581 PASS**, then `TCSlib`
    and `audits/pass-shelat/Checks` PASS.
  * 07:45:53Z–09:00:43Z, uninterrupted. 4,459 s of checks; peak RSS 4,619,264 KiB
    (`Build/ZoneRebalance`); slowest `ClassP/BinaryArith/DetMod` at 1,012.6 s.
  * A first launch at `669f3c929` was stopped by the worker after 21 modules, when the explicit
    pre-scan found the `Fin.init` entry. It is kept as `*-final-attempt1-STOPPED*`.
* **Delta replay for `ea37eb57c..03ead73ab`** (`tools/chain_delta.sh`; `chain-delta.log`,
  `checks-final-delta.jsonl`, `logs/final-delta/`).
  * Two changed modules and their 49 transitive importers (`affected-final-delta.txt`):
    **51/51 PASS**, then `TCSlib` PASS and Checks PASS (115.5 s, 3,602 MiB).
  * The other 530 affected modules have byte-identical sources and prerequisites at both heads.
* **Reconciliation** (`tools/final_post.py`, `evidence/logs/final-summary.json`):
  * For every one of the 581 affected modules, plus root and Checks, the last record is PASS,
    with rc 0, 0 parsed errors, a fresh nonempty object, and a source SHA-256 equal to the file
    at `03ead73ab`.
  * The 454 unaffected modules have the same source as at the ancestor and import no changed
    module, so their baseline objects stand.
  * PFR environment: unchanged since checkpoint 0. The 31 external modules and the guarded
    `<tree>/PFR` alias are as recorded there, and every local check used the ordinary PATH.

### Axioms and admissions

* **Checks `#print axioms`** (`axioms-checks-final-vs-baseline.json`): 367 records at both ends;
  the multisets are **equal**. The same 4 records carry `sorryAx`.
* **Census of all stored constants** of the 221 owned modules (`evidence/census/final/`).
  * Probe `FinalCensus3` PASS. It was rerun after every head change and is byte-identical to the
    runs at `ea37eb57c`.
  * 20,018 identities (baseline 19,932): 180 exist only at the base, 266 only at the head, and
    13 moved home. These are the map's removals, moves and additions, with their generated
    auxiliaries (`census-axioms-final-vs-baseline.json`).
  * **29 = 29 `sorryAx` identities, the same set.** No added identity carries `sorryAx`, and no
    claim gained an admitted dependency.
  * Standard-axiom changes on exactly the 5 identities explained at checkpoint 1:
    * `dla_blockPos`, `dla_blockPos_injective`, `dla_take_drop_ofFn` and
      `ColZK.ofFn_take_drop` gain `Classical.choice` (Mathlib `finProdFinEquiv`/`castLE` facts).
    * `units_val_mem` loses it.
* **Lexical admissions** (`tools/admissions.py`; `admissions-final.json`,
  `admissions-final-vs-baseline.json`): 510 `sorry` + 1 `sorryAx`. The per-(path, declaration,
  token) multiset **equals the ancestor's**. Positions differ only by line shifts.

### C3 and the C3 metadata controls

* **C3**: 102 baseline pairs → **34** at the head; 68 removed, 0 added
  (`c3-final-vs-baseline.json`).
  * All 34 have roots in 12 provider-only files (circuits, NP, TMSAT, Padding, MathlibBridge,
    Chebyshev, Programs/Util/List). Their proofs may not change.
  * **No consumer root references a foreign generated equation.**
* **C3 metadata controls** (`evidence/probes/C3Controls.source.txt`, output
  `evidence/census/c3controls/c3.tsv`). They run the census collector `#cp2c3` over the probe's
  own constants. **PASS:**
  * `cp2_c3_pos` (value `(pairDecode.eq_def []).trans rfl`) gives exactly the row
    `C3 _current cp2_c3_pos Turing.pairDecode.eq_def …Encoding Turing.pairDecode …Encoding`.
  * `cp2_c3_neg` (the published reader `pairDecode_nil`) gives none.
  * For this, the collector's root enumeration was widened from imported constants to all
    constants (`env.constants.toList`). The earlier version is kept as
    `CensusCore-v-final-attempt1.lean.txt`. Its first control run found 0 roots, because
    current-file constants are not in `map₁`.
  * The census rerun with the widened collector is byte-identical in all four tables.

### Whole-file seals

Sources: `seal-final.json`, `seal-final-strict.json`, `seal-final-summary.json`; probe sources
in `evidence/probes/seal-final{,-strict}-probes.tar.xz`.

* Every seal checks the same 98 files (97 consumers plus the provider `ClassNP/PolyTime`) at
  the final census closure.
* **98/98 harnesses are valid in both variants**: every request installed, EOF reached, no
  harness diagnostic.
* Standard variant: 95,177 requests (94,468 active, 709 already irreducible). Strict variant:
  95,408 requests.
* After the last commit, the two files it changed were resealed at `03ead73ab` in both variants.
  The other 96 probe sources are byte-identical at both heads. The superseded entries are kept as
  `seal-final{,-strict}-at-ea37eb57c.json`.

| variant | head failing declarations (diagnostics, files) | comparison |
|---|---|---|
| **standard** (the standing rule: `PolyExpr.eval` with its matcher/`_sunfold` left unsealed) | **225 (321, 41 files)** | checkpoint 1: 365 (476, 73) |
| **strict** (`PolyExpr.eval` sealed too; the baseline's variant) | **348 (515, 56 files)** | **baseline: 501 (688, 80)**; 153 baseline failures no longer fail; **0 declarations fail at the head that did not fail at the base** (`seal-strict-final-vs-baseline.json`) |

### Sensitivity controls (the 11-control family)

`tools/lean/Controls.lean.txt`; probes `ControlsUnsealed.source.txt` and
`ControlsSealed.source.txt`; logs under `logs/controls-final2/`. The sealed probe is PPT's census
closure, with the same notation rule: 518 requests, 3 notation names excluded. **PASS:**

* Unsealed: 0 errors.
* Sealed: no harness error, EOF reached. Each negative N1–N7 fails exactly at its `CP2-SITE`
  line, with no other error:
  * N1 `rfl` conversion
  * N2 `show` conversion
  * N3 anonymous `example`
  * N4 generated matcher
  * N5 definition body
  * N6 field of a structure-valued foreign definition
  * N7 destructuring a foreign predicate
* Positives P1–P4 pass sealed: published case reader, field reader, predicate reader, and
  `PolyExpr.eval` notation.
* N4 was redesigned after its first run. The first form (a matcher applied to a constructor
  discriminant, `Controls-attempt1.source.txt`) is reduced by `whnfCore` without delta, so it
  passed both ways and was no seal control. The new N4 compares the foreign matcher with a local
  one on a free discriminant.

### Explicit-source review

`tools/explicit_scan.py` with the final name table: `explicit-scan-final.json`, 15,367 items in
the 97 consumer files. It finds **0 foreign TCSlib definitions and 0 Core/Mathlib definitions**
in any simp/rw/unfold/dsimp/delta list. The 7 builtin simprocs and one `let`-bound local are
correctly classified. The final pre-scan found one Mathlib `Fin.init` entry, now repaired in
`ea37eb57c`.

### Style

`evidence/logs/style/`: repository `style_lint.py` on the 122 changed files, and the campaign
lint `TCSlib` plain and `--check8b`, each run at base and head.

* FAIL counts are equal (1,238 at both ends). WARN: plain 673 → 663, check8b 725 → 715. Check 8
  lists shrank because readers were added.
* **New findings, reported separately:** four fill-owned files now pass 1,000 lines. All growth
  comes from the added readers and repairs. They are recorded per file under the standing size
  rule, and none is split:

  | file | base lines | head lines |
  |---|---|---|
  | `GGMReduction` | 880 | 1,106 |
  | `HardCoreLemmas` | 999 | 1,056 |
  | `ZeroKnowledge/GraphIsomorphism.lean` | 993 | 1,026 |
  | `ThreeColoring/Machines` | 997 | 1,007 |

* Three proofs that the repairs lengthened past 20 lines received proof sketches (`669f3c929`).
  No other new finding.

## Dispositions (764 historical rows, 509 work keys)

Built by `tools/dispositions.py` from the final evidence alone. Outputs:
`evidence/maps/dispositions-final.json` (with every open key's diagnostics),
`dispositions-keys.tsv` and `dispositions-rows.tsv`.

**How each channel is decided.**

* **Seal channels** (HIST_SEAL, GATE06/GATE08/S2 seal, G06_C2 `show`): does the key's
  declaration have an error in its file's standard-variant seal? The strict variant is
  recorded beside it.
* **Explicit channels** (HIST_UNFOLD, G06_C1, J_CORE_FUNCTION_COMP): does a foreign or
  Core/Mathlib definition remain in the declaration's lists?
* **C3 channels**: is the (module, root, equation) pair present in the final C3 census?
* For any key, a seal failure of its declaration counts as open, whatever the key's channel.
* Canonical names come from the head source (namespace tracking) and are verified against the
  census; 0 are unresolved.
* A key whose declaration moved is checked at its new home. The four PPT relocations are such
  keys.

| | repaired / verified at final | removed (exact mapping) | open | total |
|---|---|---|---|---|
| **509 keys** | **333** | 3 | **173** | 509 |
| 764 rows: unfold channel | 444 | 2 | 0 | 446 |
| 764 rows: eqn-term channel | 53 | 0 | 0 | 53 |
| 764 rows: seal channel | 112 | 1 | **152** | 265 |

**Removed by exact mapping.**

* `FunFamily.decodeFin_eq_some_iff` (Collections) and `GGMRed.decodeFin_eq_some_iff` were
  replaced by the public `TCSlib.Cryptography.decodeFin_eq_some_iff` (X4).
* `negligible_const_zero` was replaced by `negligible_zero` (X4).

**The seven reader-repair candidate rows**: 217, 547, 560, 562, 648, 746 and 750 were rechecked
freshly and are all repaired and verified at final. So are 546 (the PublicKeyLemmas duplicate,
now the public `abs_uexp_sub_le`), and 561/745 (the `distAdv_le_statDist` explicit and generated
references).

**Open keys by class.** Classes come from `tools/classify_residual.py`. It applies mechanical
rules to the full diagnostic texts, per failing declaration (`evidence/maps/residual-final.json`
and `.md`).

| class | keys | rows | meaning / next step |
|---|---|---|---|
| E_API_INLINE_MATCH | 5 | 3 | Blocked: see E-API 1 below |
| OPEN_TYPED_COINS | 42 | 40 | The coin or seed type of a constructed machine or structure (`.Coins n`, `ExecCoins`, `.σ n`, `Fin (… .coinLen n)`) is identified with a concrete type by conversion. Repairable through the published equivalences (`NUPPT.coinsCongr`, `coinsEquivPoly`, `coinsEquiv_ofPolyTime*`, `…_domEquiv`). **Not done** |
| OPEN_MACHINE_INTERNALS | 2 | 2 | Machine-model internals (ModuleHost `stopCfg`/`padTM`/`emitCfg` configurations; the `CodeTM.toFinTM` state type). Not analysed further: it is open whether ordinary field/run readers suffice |
| OPEN_INCOMPLETE | 124 | 107 | Other definitional reads: `rfl`/`show`/`change` through a foreign body, applying or destructuring a foreign predicate, Decidable instances left stale by `dsimp` with rfl readers. Repairable with existing or ordinary owner readers. **Not done** |

Beyond the keys, the head seal has **52 further failing declarations**. These are witnessed
same-consumer observations; `residual-final.json` lists each with its diagnostics. Three are
in the provider `ClassNP/PolyTime` (class PROVIDER_FROZEN: `polyTimeComputable_id`,
`PolyTimeComputable.output_length_le`, `PolyTimeComputable.comp`).

## Escalations

**E-API 1: provider contracts stated over an inline `match`.**

* **Affected contracts:**
  * `Turing.FinTM.computesFunInTime_unaryMul` (provider `Randomized/Primitives`)
  * `computesFunInTime_stripLast`, `computesFunInTime_pairLenCheck` and
    `computesFunInTime_pairMapSnd` (provider `Build/Primitives`)
  * `Complexity.polyTimeComputable_iterateFind` (consumer `Repetition`, public header frozen)
* **Why this blocks the consumer:** each contract states its function as an anonymous
  `match pairDecode z with …` or `match (List.range …).find? … with …`. A consumer's
  `PolyTimeComputable`/`ComputesFunInTime` goal for its own named function can be identified
  with the contract's function in only two ways:
  * by unfolding the contract's compiler-generated matcher, which is sealed;
  * by using that matcher's generated equations (`…match_1.eq_*`), which is a C3 bypass.

  No ordinary reader can expose an anonymous matcher, so this is not reader work.
* **Blocked declarations:**
  * `EncodingMachines.unaryMul_poly`, `OneWayLemmas.polyTimeComputable_unaryMulPair`,
    `GGMRed.unaryMul_poly`, `GI.unaryMul_poly` (EfficiencyRep)
  * `PolyTimePairing.polyTimeComputable_unary`, `polyTimeComputable_lenLe` (and
    `PolyTimeComputable.pairMapSnd`)
  * `OneWay.YaoMachine.yaoRaw_poly`, `GGMRed.stateLoopFun_poly`, `GGMRed.lookup_poly`
  * `IterateFind.polyTimeComputable_find`, which also has machine-internal reads
* **Needed contracts:** the same contracts stated over match-free or named functions with
  complete case readers. Examples:
  * `fun z => List.replicate ((pairFstD z).length * (pairSndD z).length) true` for `unaryMul`.
    It agrees with the match on every input, since `pairFstD`/`pairSndD` are `[]` on non-pairs.
  * A named `iterateFind g acc out R` with `_some`/`_none` readers.

  These are new non-reader provider theorems. For `polyTimeComputable_iterateFind` it would be
  a second public statement next to a frozen header. Neither is authorized here.

**E-FREEZE 1: provider `ClassNP/PolyTime`.**

* `polyTimeComputable_id`, `PolyTimeComputable.output_length_le` and `PolyTimeComputable.comp`
  apply a `ComputesFunInTime` hypothesis as a function.
* The repair goes through `Turing.FinTM.computesFunInTime_iff`. It is a proof edit in a
  provider-only file, which the role forbids. Only the reader `polyBound_iff` was added there.

**No E-RES, E-BASE or E-TRUE.**

## Commands and resources

* One Lean process at a time, always. `scripts/lean_check_tree.sh` runs through the
  wrapper `tools/chk.py`, under the ordinary PATH, in the one tree.
* `tools/chain_final.sh`: replay, census, controls, standard and strict seals;
  07:45–09:54Z.
* `tools/chain_final2.sh`: census rerun, C3 controls, controls; 09:54–10:00Z.
* `tools/chain_delta.sh`: delta replay, root/Checks, census, reseal of the two files;
  10:05–10:19Z.
* `tools/final_post.py`: comparisons, explicit scan, classification, dispositions.
* Census ≈ 295–315 s at 3.1 GiB. Seals ≈ 24 min per variant.
* Development probes (`tools/sealwt.py`, phase `seal-wt`, logs under `logs/seal-wt/`) are
  development evidence only.

## Limits

* **Not final-complete:**
  * 173 work keys (152 rows) and 52 further declarations still fail the standard seal.
  * The E-API and E-FREEZE items above need maintainer decisions.
  * The remaining OPEN classes are repairable within the authorized routes, but this session
    did not finish them.
* **Classification of open failures** is mechanical, from diagnostic texts. Except where a fix
  was attempted, a declaration's first diagnostic can hide later ones in the same tactic block.
  Fixing a first error often uncovered further reads, as in Universal, GIZK Simulator and
  HardCore.
* **Seal coverage:** the standard variant is the campaign rule. The strict variant is reported
  for a like-for-like comparison with the checkpoint-0 baseline. Instances and reducible
  abbreviations are not sealed: the attribute cannot seal them, and they are notation under
  policy.
* **Overwritten log:** the per-module seal logs of the two resealed files at `ea37eb57c` were
  replaced by the `03ead73ab` logs at the same path. Their records remain in
  `checks-seal-final*.jsonl`, and their summaries in `seal-final*-at-ea37eb57c.json`.
* **PR #232:** its reader counterparts are not reconciled. No inventory was supplied.

## History: checkpoint 1 (exchange `8b133945`, fill head `51c245389`)

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

## History: checkpoint 0 — environment and baseline (complete)

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

### Work state at checkpoint 0 (historical)

At checkpoint 0 the milestone-1/2 changes were drafted but not yet checked; they are commit
`a8a8055ce` of checkpoint 1.

### Limits of checkpoint 1 (historical)

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

**Final delivery — PARTIAL, not final-complete. At `03ead73ab`, all commissioned interface,
deduplication, Mathlib and doc targets are implemented. The full affected replay, root and Checks
pass. Axioms, admissions and C3 (no consumer pairs) are clean against the baseline, and all
controls pass. Limitation: the J/N seal channel is still open for 173 of the 509 work keys
(152 rows) and 52 further same-consumer declarations, with one E-API (inline-match provider
contracts) and one E-FREEZE (provider `ClassNP/PolyTime`) escalation. This is not merge
clearance.**
