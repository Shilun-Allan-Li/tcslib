# Gate 130 — configuration and sweep readers

Prepared for Codex. **Not yet clear to merge: #252 — external audit open.**
Source: 04b0b07d4ea836f52cb645f480b67cdc9e99ea59, codex/ab34-space-readers, PR https://github.com/Shilun-Allan-Li/tcslib/pull/252, target complexity/arora-barak-ch3-4. Baseline Lean: 9b5dcf46408db681bcbc721930ef2203fa6bc47d (whole MAC8). Exact publication records and exchange pins are in the exchange README and dispatch prompt. Seyoon alone dispatches, rules and merges.

## Exact change

Seyoon approved these five non-simp equations, grouped them, and selected Codex. Only the following three owner files change; removing the five complete declaration chunks recovers the old files byte for byte. There are no new or changed definitions, imports, attributes, existing headers/proofs, or admissions. The proof consumers remain separate.

| New public reader | Contract and boundary |
|---|---|
| Turing.MultiTapeTM.ConfigCount.core_eq | Beside core in ConfigCount: state, input position, work tapes and work-head positions, in that order. Output is omitted. No counting bound or halt property. |
| Turing.ClockHost.bootCfg_of_halt | Beside bootCfg in NDClockHost: for a halted yardstick configuration, enter rewind, preserve input position and yardstick work bank, blank the attempt bank and put the yardstick output at the extra tape with its length as head. The host output is empty. |
| Turing.ClockHost.runCfg_initCfg | Beside runCfg in NDClockHost: retain the supplied yardstick bank and head position j, use input position 1, the initial attempt control, blank attempt tapes and zero attempt heads, with no captured or host output. The yardstick content is yard m. |
| Turing.FinTM.sweepRevCfg_state | Beside sweepRevCfg in Sweep: the state is the supplied option, including none. No statement about the work tape or movement. |
| Turing.FinTM.sweepRevCfg_output | Same owner: output equals the supplied word, including empty. No run or reversal theorem. |

The producer proof roots are interface equations, not independently stated textbook results. Review their meaning against the adjacent owner definitions. The three historical consumer packets are preserved for the exact authorization and API motivation; they are not part of this PR or substituted for current native checks.

## Checks

- Actual full 335-module replay on the exact pushed Lean tree from a complete MAC8 clone: all pass, zero static mismatches and 59 inherited direct admissions in the replay population. All 895 input objects remain unchanged; the output keeps all 895 and changes exactly the three owners. Current prospective merge is clean and has the exact replayed 1,003-file Lean tree. The umbrella is a screen input, not a replay module.
- Fresh three-owner native checks, no warnings or admissions. Two full producer metadata runs agree byte for byte. All five facts are non-simp and non-unfold, with axiom sets respectively empty, propext/Quot.sound, propext/Quot.sound, empty, empty. No new axiom.
- Ordinary foreign footprints are 0/1/3/0/0; the two nonzero complete owner-prefix proofs pass their opacity guards. Union: FinTM.bufferTape, NDTM.initCfg and Cfg.init. All six point/equation controls pass unsealed and fail at their intended sealed goals. No vacuous seal is claimed for the zero-head proofs. Foreign definition RHSs and encountered theorem proof values stop at their boundary. The 11 explicit nonlocal rewrite/simp arguments are resolved and checked.
- Declaration freeze: ConfigCount 24→25, NDClockHost 48→50, Sweep 22→24 public, no private changes or removals. Campaign lint: 0 FAIL and the same 84 SpaceComplexity / 73 TuringMachine warnings. Owner style lint preserves the four pre-existing Sweep doc/sketch issues; line offsets shift.
- Full 53-file pair coverage: actual baseline 2,872 rows, 2,424 pairs. The first head run was interrupted and discarded. Current head preserves all 2,872 old scored rows exactly in kind, normalized body and grams; the sole new scored row is runCfg_initCfg. The unchanged official parser/tiler considered all 5,744 ordered pairs incident to it, ran 56 actual tilings, and found no new reported pair. The complete 2,424 reported pairs and scores are byte-identical after the count line. This is exact reuse of unchanged pair inputs plus fresh scoring of all affected pairs, not a claimed fresh quadratic run. Both complete source populations and raw consideration rows are included.
- Bounded 587-ref/391-head prepared and delivery census retains 1,035 complete candidate chunks and all dispositions. The refreshed open snapshot checks all 18 heads; the changed #251 and new #253 deltas are captured and inspected. No independent public twin was found in this population. Old core/step/run and sweep/boot contracts have different statements; the owner equations do not introduce another copy or a debt acceptance.

## Audit request

Check the exact five formulas, owner boundaries, lack of new attributes/definitions, statement freeze and metadata/axiom/control claims. Check that the replay and complete screen are bound to this source, that the copy census includes the recorded open/prepared/delivery inputs, and that all cited evidence is recoverable. Independently restate the equations and consider at least three boundary instantiations (zero work tapes, an empty output, a nonzero or negative yardstick position, and halted versus live control are useful). Flag any actual duplication or missing hypothesis at the supplied severity. Do not infer any consumer adoption, mathematical fill, route approval, debt acknowledgment or merge.

Use the findings table and a verdict with blocker/major/minor/note counts from the bundled standards. **Deliver your findings as a downloadable file named gate130-space-reader-prerequisites-findings.md** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply. Do not push or edit any branch.
