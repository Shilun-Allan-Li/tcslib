# FH full-boundary preflight: seven current proofs eligible

Actual committed source: `70abd9b3b2d559afded28a413be4676a2dd047d4`, parent `2c85a68a73f74b79ac19ab2f824a17ddf2432962`. Whole MAC8 input: `9b5dcf46408db681bcbc721930ef2203fa6bc47d`. All 14 current source owners were read directly from Git and remain clean. All 895 MAC8 olean hashes equal the earlier frozen adoption inventory.

**Recommendation:** retain current roots 9, 16, 18, 19, 33, 85 and 86 for root-owned final replay/audit. Hold the other ten current implementations. No hypothetical repair is counted in this packet. The final PR scope, trim, replay, canonical record changes and gate readiness remain root/Seyoon-owned.

| ID | Complete proof | Ordinary foreign TCSlib heads | Actual guard | Current disposition |
|---:|---|---:|---|---|
| 9 | `enumCont_first_halt` | 1 | PASS | PASS |
| 16 | `b2_unary_first` | 3 | PASS | PASS |
| 17 | `b2_verify_timed` | 12 | PASS | HOLD |
| 18 | `sat_first_halt` | 3 | PASS | PASS |
| 19 | `sat_call_first_halt` | 1 | PASS | PASS |
| 33 | `clA5_call_first_halt` | 1 | PASS | PASS |
| 47 | `ComputesInTime.of_spaceUsed_le` | 6 | FAIL (1 errors) | HOLD |
| 50 | `call_run` | 30 | FAIL (4 errors) | HOLD |
| 51 | `cleanTM_run` | 10 | FAIL (3 errors) | HOLD |
| 52 | `runFrom_count_eq` | 5 | PASS | HOLD |
| 54 | `clockTM_setup` | 6 | FAIL (1 errors) | HOLD |
| 58 | `startup` | 12 | FAIL (1 errors) | HOLD |
| 82 | `clockStageCfg_captures` | 7 | FAIL (1 errors) | HOLD |
| 83 | `one_work_tape` | 8 | FAIL (2 errors) | HOLD |
| 84 | `dg_all_inputs` | 10 | FAIL (5 errors) | HOLD |
| 85 | `timedCapture_start` | 9 | PASS | PASS |
| 86 | `universalCapture_start` | 7 | PASS | PASS |

All 14 full literal current owner sources compile with appended fresh metadata: actual exit 0, zero errors and zero sorry warnings. The selected 17 root full types, expression representations, universe parameters and axiom sets are retained; their axioms are subsets of propext, Classical.choice and Quot.sound. These are actual selected source elaborations against whole MAC8, not a final merged-tree replay.

The footprint starts each complete root type and proof expression, follows all mentioned constant types, and follows same-owner ordinary-definition values including local helpers. It does not traverse imported theorem proof values, other local theorem proof values or foreign definition values. Only ordinary foreign **TCSlib** definition heads are guarded; kernel abbreviations and projections remain listed but are excluded. Core/Mathlib explicit arguments are reviewed separately. This is the same bounded boundary method as the supplied FE reference; no global opacity claim is made.

Each guard keeps all literal preceding owner source and the complete target scoped-open/doc/header/body, introduces local irreducibility for every captured ordinary foreign TCSlib head, removes registered definition simp/unfold rows, checks the proof, and witnesses that every head is still irreducible with no active definition simp/unfold row. No preceding declaration is stubbed. Later declarations are omitted and only original open namespaces/sections are closed. All 17 guard-state witnesses pass; eight proof/header scopes fail. Two further compiling scopes (17 and 52) are held by static explicit-definition review.

The eligible-seven union has 11 ordinary heads. Twenty-two actual paired controls (pointwise and whole-value identity for each head; nullary pointwise uses Unit-function lifting) are kernel checked unsealed and fail at rfl when the same 11 heads are locally irreducible, with exactly 22 expected errors and both completion markers. The initCfg registered definition-unfold row is removed on both sides. Controls reflect foreign ordinary definition bodies only for this effectiveness check; the footprint never traverses those bodies. No imported theorem values are inspected for the footprint or controls.

Explicit argument review covers the complete 17 proof chunks, including inherited parts. Every simp/simpa/dsimp/rw/unfold/delta-family command found by the bounded command inventory is retained uncapped in EXPLICIT-COMMANDS.json. Local hypotheses/lets and same-owner definitions are permitted. Foreign definition arguments are recorded separately in DISPOSITIONS17.json. No explicit Core/Mathlib definition argument was identified in these 17 chunks; theorem-kind metadata and additional source declaration lines are retained. Guard compilation alone does not excuse explicit simp[Def]/unfold/delta.

The seven eligible proofs use published theorem readers or local facts in all explicit rewrite/simplification arguments. Full ordinary-head lists and same-owner helper footprints are in FOOTPRINTS17.json and FOOTPRINT-SUMMARY.json. Foreign-source map captures all 17 modules cited by the complete 70-head union. All are literal MAC8 source except ConfigCount, whose first-halt proof is touched; its definition code is covered by the prior source preservation evidence. The four modules providing the safe-seven union definitions are literal unchanged MAC8.

The ten holds are specific:

- 17 `b2_verify_timed`: Guard compiles, but explicit simp[VirtualTag, MultiTapeTM.initCfg, Cfg.init] forces three ordinary foreign definitions. HOLD independently of guard success.
- 47 `ComputesInTime.of_spaceUsed_le`: Guard fails at hcard: spaceUsedByTape must be read as visited-card through published spaceUsedByTape_eq_card. Explicit simp[visitedByTapeHead] also forces a foreign definition. Existing-reader repair possible but not included in this safe7 freeze.
- 50 `call_run`: Guard fails at initial positive-time, opaque SimRel introduction and HaltRel elimination. Many explicit foreign definition unfolds remain throughout the complete inherited proof. No earlier read exempted. Missing reader/contracts listed as a hold; no new API implemented.
- 51 `cleanTM_run`: Guard fails at ccfg state/output fields and PB predicate matching. Explicit visitedByTapeHead, ccfg, markI and Cfg.init unfolds remain. Existing runFrom/with_q0 repairs in current proof do not clear these separate boundaries.
- 52 `runFrom_count_eq`: Guard compiles, but explicit simp[MultiTapeTM.visitedByTapeHead] and simp[core] force ordinary foreign definitions. core resolves through scoped open MultiTapeTM.ConfigCount.
- 54 `clockTM_setup`: Guard fails at final rfl through foreign initCfg fields. Existing initCfg_eq and Cfg.init field-reader repair is concrete but untested and excluded from this freeze.
- 58 `startup`: Guard fails at final hostCfg/runCfg equality; explicit simp[bootCfg] independently forces foreign definition. No published reader added or generated equation consumed.
- 82 `clockStageCfg_captures`: Guard fails in literal header: raw clockStageCfg type no longer definally matches opaque obliviousSchedule bundled k/State. Header/API/transport decision needed; no header changed.
- 83 `one_work_tape`: Guard fails at two intro x steps through opaque ComputesFunInTimeVia; existing iff readers identified. Later sweepRevCfg field boundary is not certified. No complete repair claim.
- 84 `dg_all_inputs`: Guard fails at ComputesFunInTime application, final sweepRevCfg field changes, visited membership and spaceUsed sum coercion. Existing predicate/visited/space readers identified; complete proof not certified.

No new API, import, statement, name, home, route, debt waiver, mathematical fill, source edit, Git mutation, canonical mutation, snapshot splice, screen or full downstream replay was performed. The full source contexts compile, but style warnings are retained and this is not a zero-lint claim. Older 710-payload FH evidence stays immutable and bounded as originally described.

Failed metadata/control fixtures are preserved under attempts and are not target-source failures: catalogue reserved-name syntax; control v1 layout syntax, v2 numeral type inference, v3/v4 recursion-limit abort before all negatives. Corrected v5 native and negative controls are the counted final result. This freeze contains no private live package symlink or plain .lean file.

Frozen UTC: 2026-11-08T13:29:20.031326+00:00
