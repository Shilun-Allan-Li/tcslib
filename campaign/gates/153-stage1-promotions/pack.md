# Gate 153 · Closeout stage 1: small promotions and citations (PR #349)

**Not yet clear to merge** · PR #349 is a draft. Seyoon dispatches and merges.

- Lean head: `a1a7c6ec39b515c6babc347e300a21566516a3a8` (branch `closeout/stage1`, two commits).
- Base: campaign Lean `b913bbc9` (the #345 merge). Records: see the dispatch prompt.
- This is the first audit.

## Scope

Stage 1 of `campaign/closeout/STAGES.md`: Seyoon approved items 1–10 of its checklist on 2026-11-16
and dropped item 11. The second commit repairs the four rule-10 seal failures of the first run and
withdraws two items by ruling (STAGES.md, "Gate 153 seal repairs"). All files are bundled.

**New or moved public declarations (all approved):**

1. **TR-1.** `Turing.FinNDTM.AcceptsWithin.iff_of_haltsWithin` in `ClassNP/NTIME`: at a time
   `t` within which every branch halts, acceptance within `t' ≥ t` and within `t` agree. The
   private copies in Nondeterminism (`acceptsWithin_iff_of_halts`), ExhaustiveReplay
   (`xr_accepts_iff_of_halts`) and NTimeHierarchy (`nh_accepts_of_halts`) cite it.
2. **MIG-10.** Relativization's private oracle relabelling moves to `TuringMachine/Oracle` as
   `Turing.OracleTM.relabel` (with `simps` field equations, not simp lemmas),
   `relabel_wellFormed`, `queryString_mapState`, `relabel_step`, `relabel_runFrom` and
   `relabel_computesInTime`. Oracle imports `CfgFacts` (approved) for `Cfg.inputSymbol_congr`.
   Relativization's five `oracleRelabel*` privates are deleted.
   - **Reader (approved 2026-11-17):** `Turing.FinOracleTM.computesInTime_iff` in
     `TuringMachine/OracleFinite` (`Iff.rfl`). `exists_finOracleTM_enumeration` compares two
     bundled machines through it; the first run's seal failed there.
3. **F6-1(d).** `Turing.scanTM_run_preserves` in `Build/CfgRecord`, general in the tape count,
   replaces the private `recordStep_scan_preserves`. RecordTable's `rt_find_scan` cites it.
4. **SD-1.** `Turing.pairEncode_drop` moves from `Build/InputDevice` to `Encoding` (same name).
   `Codec.pe_drop` is a citation and PathWalk's private `drop_pairEncode` is deleted.

**No new API:**

5. **RS-1:** carried (Seyoon); not in this PR.
6. **F6-1(c).** NotTimeConstructible's `ntc_codeBitsNat_eq_ofDigits` cites
   `Turing.foldr_bit_eq_ofDigits`. UHaltMachine's lemma states a different fact.
7. **WL-1.** `walkLe_succ_iff` moves from ISCountMath to PathWalk as `Complexity.walkLe_succ_iff`.
8. **TC-1.** KarpLiptonPrefix's `transduce_drop_true` and MeyerVerifierGlue's `transduce_fT_copy`
   cite `transduce_of_copy`. **CK-1 is carried** (Seyoon, 2026-11-17): touching the codec deciders
   exposed older reads of Codec/Machine's `CA` table, so Checks and Deciders are back at base.
9. **CC7-1's base half.** CodeSimulator's private `skipAction_consumes` serves `skipTable_consumes`
   and `canonStageBlock_consumes`. C1E-1(d) is carried.
10. **G147-01: carried** (Seyoon, 2026-11-17). Editing the two notes seals two public proofs that
    read `NTIME`/`NEXP` directly, and `NEXP` has no reader; Nondeterminism keeps them at base.

**Seal repair in the second commit:** Oracle's `queryString_mapState` rewrites the work tapes at
function level (`Cfg.mapState_workTapes` under `funext`), so the `dite` condition's instance is
rewritten too.

Statements: `SOURCE.json` has no `header_changed` and no `definitions_changed`. Net: **−5 Lean
lines** (+267/−272) across 18 files. The promotions add documented public lemmas, and the carried
items were the larger savings.

## Brief for the auditor

1. **Statements.** Confirm that every pre-existing declaration keeps its statement byte-identical
   and that the moved ones (`pairEncode_drop`, `walkLe_succ_iff`) keep theirs up to binder names.
2. **New public declarations.** Check each one's statement, docstring, attribution and proof
   sketch: `iff_of_haltsWithin`, the six `OracleTM.relabel*`/`queryString_mapState`,
   `FinOracleTM.computesInTime_iff` and `scanTM_run_preserves`. Check that `relabel` is
   well-formed exactly when the source is, and that `relabel_computesInTime` is the bundled
   enumeration's transport.
3. **Citations.** Check that each retired private copy stated the fact its citation now supplies.
4. **Carried items.** Confirm that Checks, Deciders and the two Nondeterminism notes are at base.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below).
6. **Copy screen** (population: the 18 changed files): `evidence/PAIR-DISPOSITIONS.json`.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the 18 owners' downstream closure on
  `oleans-cb913b` (the #345 merge's snapshot). 336 modules replayed: 336 passed, 0 failed, 28
  inherited admissions (pre-existing). There are 874 objects in and 874 out.
- **Seals:** all 25 changed or added proofs pass with every other-file definition they reach made
  irreducible (50 heads).
- **Controls:** 27 definitions' 54 paired controls close natively and fail when sealed (two
  parts).
- **Proof-syntax sweep:** 25 roots, 11 read candidates, all false resolutions in
  `OracleTM.relabel_computesInTime`. Ten are `rw [initCfg]`, resolved to `NDTM.initCfg`. One is
  `unfold ComputesInTime`, resolved to `FinOracleTM.ComputesInTime`. Inside `namespace OracleTM`,
  both names are Oracle's own `OracleTM.initCfg` and `OracleTM.ComputesInTime` (same file). The
  sealed check passes.
- **Lean-backed sweep:** 194 identifiers. The only flagged constants are outside TCSlib
  (`Nat.bits` from Mathlib, and core `decide`, `Functor.map`, `reduceIte`, `reduceDIte`).
- **Citation homes** (G147-02 procedure, `defsweep/CITATION-HOMES.json`): Transducer
  (`transduce_of_copy`), Build/Catalog (`ScanPhase`, `scanTM_run_ofCfg`), Build/CounterLoop
  (`foldr_bit_eq_ofDigits`), CfgFacts (`Cfg.inputSymbol_congr`), CodeParser (`codeBitsNat_eq`),
  Configuration and StateRenaming (field equations), Nondeterministic (`runWith_append`,
  `runWith_of_halt`). The scope pass's namespace errors (`StepBlock`, `LogProg`) affect one scope
  block each in CodeSimulator and Parse.
- **Lint:** no style change and 0 campaign FAIL. OracleFinite's check-8 warning narrows from
  `ComputesInTime, DecidesInTime` to `DecidesInTime`.
- **Copy screen:** 310 → 305 directed pairs, 1 new and 6 gone; 94,921 → 93,700 characters.
  - **Moved:** `walkLe_succ_iff`'s 73% match with `walkLe_succ` reappears inside PathWalk.
  - **Retired:** the `skipTable_consumes`/`canonStageBlock_consumes` pair (both directions) and
    the `nh_accepts_of_halts`/`acceptsWithin_iff_of_halts` pair.
  - **Generalized:** two CfgRecord lemmas no longer match the renamed, tape-general
    `scanTM_run_preserves`.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate153-stage1-promotions-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
