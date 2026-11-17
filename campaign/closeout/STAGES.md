# Closeout stages for the remaining cleanup (Seyoon, 2026-11-16)

Rebuilds and gates happen only between stages. Agreed plan:

1. **Stage 1, small promotions and citations.** One PR, one gate. The maintainer does it.
2. **Stage 2, medium structural work.** One PR, or two PRs on disjoint files gated together:
   - IR-1;
   - RC-4's first-halt row;
   - F6-1(b);
   - WS-1;
   - RN-1, narrowed to CodeSimulator's part;
   - MIG-7.

   Fills are delegated to outside workers, with briefs written by the maintainer during stage 1.
3. **Stage 3, carry and sync.** First, records: the carried-debt register. It covers R5,
   MIG-24, U-1/MIG-2, MIG-9, DT-1, F7-1(b), SG1 kind 6 and item 13, SH-1, MIG-8's merge half, and
   the MIG migration rows outside the closeout (including MIG-16 and F6-1(f) with it). Then sync
   `main` (W4) with a full replay as its gate.
4. **Stage 4, wrap-up.** The blueprint (W5, delegated one module per worker), the final audit
   (W6) and the integration PR (W7).

## Stage 1 checklist (approved by Seyoon on 2026-11-16: items 1–10 yes, item 11 dropped)

**New or moved public declarations:**

1. **TR-1.** Publish `FinNDTM.AcceptsWithin.iff_of_haltsWithin` in `ClassNP/NTIME`, which gains
   the import `NTIME ← ChoiceWords`. The three private copies (Nondeterminism, ExhaustiveReplay,
   NTimeHierarchy) cite it.
2. **MIG-10.** Promote Relativization's private oracle relabelling (`oracleRelabel`, its
   well-formedness and run transport) to `TuringMachine/Oracle`.
3. **F6-1(d).** Make CfgRecord's `recordStep_scan_preserves` public. RecordTable's `rt_find_scan`
   cites it.
4. **SD-1.** Move `Turing.pairEncode_drop` from `Build/InputDevice` to `Encoding`, with the same
   name. `Codec.pe_drop` becomes a one-line citation and PathWalk's private copy is deleted.

**No new API:**

5. **RS-1.** CodeSimulator, ExhaustiveReplay and NTimeHierarchy import `Build/UniversalParts` and
   cite `MultiTapeTM.initCfg_eq_mapState`.
6. **F6-1(c).** NotTimeConstructible and UHaltMachine cite `Turing.foldr_bit_eq_ofDigits`.
7. **WL-1** (ruled 2026-11-06). Move `walkLe_succ_iff` to `PathWalk` as `Complexity.walkLe_succ_iff`.
8. **CK-1 and TC-1** (FYI line for Hydroxyi). Re-point the codec deciders to `acceptChk_iff` and
   `initChk_iff`, and the two transducer instances to `transduce_of_copy`.
9. **Private leftovers.** CC7-1's per-record bound, and C1E-1(d)'s optional merge of the
   one-bank update lemmas.
10. **G147-01.** Fix the two stale historical notes in Nondeterminism.

**Dropped:**

11. **F6-1(f)** (`oracleEmbed_updateTape`). There is no second copy today, so it goes with MIG-16
    to the stage 3 register.

## Stage 1 build notes (2026-11-16)

- **Oracle import.** Seyoon approved `TuringMachine/Oracle ← CfgFacts` for MIG-10: the step
  proof reads the input symbol through `Cfg.inputSymbol_congr`.
- **TR-1** needed no new import; NTIME proves the lemma from `NDTM` equations it already sees.
- **RS-1: carried** (Seyoon). The three sites compare against constructed configurations, not
  `(A.initCfg x).mapState f`, so a citation would save almost nothing and add three imports.
- **CK-1: two lemmas approved** (Seyoon): `Codec.acceptChk_def` and `initChk_def`, beside
  `edgeChk_def`. The published `_iff` characterizations do not fit the deciders' proofs.
- **C1E-1(d)'s optional merge: carried** (Seyoon); it needs a bank-indexed layout redesign.
- **F6-1(c)** applies to NotTimeConstructible only; UHaltMachine's `bits_foldr_bit_one` states a
  different fact.
- **F6-1(d)** is published general in the tape count, as `Turing.scanTM_run_preserves`; RecordTable
  uses two tapes.
- Net −2 Lean lines across 19 files. The approved promotions add documented public lemmas, and
  the carried items were the larger savings.

## Gate 153 seal repairs (2026-11-17)

The first run (head `ceece3a0`) passed the replay (336/336) and failed the rule-10 seal in four files.
The second head `a1a7c6ec` repairs or withdraws each:

- **Oracle `queryString_mapState`:** now rewrites the work tapes at function level, so the dependent
  condition's decidability instance is rewritten too.
- **Relativization `exists_finOracleTM_enumeration` (MIG-10):** Seyoon approved a public reader,
  `Turing.FinOracleTM.computesInTime_iff` (`Iff.rfl`, in `TuringMachine/OracleFinite`); the
  proof cites it.
- **CK-1: carried** (Seyoon). The deciders and Checks return to the base, and `acceptChk_def`/`initChk_def` are
  dropped. Repairing the touched tails would need new `CA` table lemmas in Codec/Machine.
- **G147-01: carried** (Seyoon). The two notes return to the base. Editing them seals two
  public proofs that read `NTIME`/`NEXP` directly, and `NEXP` has no reader.
