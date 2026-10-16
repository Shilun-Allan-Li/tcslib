The SHA-256 matches `91f96cf5fea0a6d2f07040ebeaeb423362dc26a298dad58e5c53beda5a19dca1`; the bundle contains **52 distinct sections**. Reversing the patch reproduces all six recorded base blob hashes.

**The 85 generated equations are faithful, but G4’s E1 is not completely discharged. F3’s three named E1 requirements are covered.** This is a source-and-evidence audit; I did not independently run Lean or the downstream replay.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `Build/Contract/Seam.lean` · `ReturnContract.release`, `RoundContract.release`; `Build/Contract/Basic.lean` · `Contract.ofSegment` | G4’s iteration interfaces remain incomplete under the no-unfolding rule. | G4’s review explicitly requires the release adapters’ field equations, and its brief names `RoundContract.release`. Neither adapter has equations for `pre/time/post/lo/hi`; the existing positivity lemmas do not supply them. The alternative `Round.iterate` route points to `Contract.ofSegment`, whose fields likewise lack equations. | Publish the five field equations for both release adapters and `Contract.ofSegment`, without `@[simp]`; add consumer probes for the prescribed iteration routes. |
| 2 | **major** | `Build/Contract/Catalog.lean` · `sweepMapWrite` | The mapped-copy endpoint API does not expose the value written into destination cells. | `copyMapTM_contract_post` and `transferMapTM_contract_post` retain `sweepMapWrite`. Applying `sweepPost_workTapes` reaches that helper, but no published equation exposes its `bufferTape`/`extract`/`merge` formula. G4 needs precisely that formula for column preservation and constant-symbol writes. The field equations themselves are correct; the advertised endpoint-reading interface remains incomplete. | Add a public application equation for `sweepMapWrite`, or equivalent destination-cell lemmas. Verify the constant-merge and `zoneSlotOf`/`zoneSlotSet` uses without unfolding specification definitions. |
| 3 | **minor** | `SpaceComplexity/WindowClock.lean` · `exists_configWindowRunnerTM` appendix | The consumer documentation contradicts the current ruling. | The bundled appendix says `RecordAt`, `recordLength`, and `posWidth` “may be unfolded”; the pack and `NOTES.md` record the subsequent API-only ruling. | Mark the earlier permission superseded and name `recordAt_iff`, `recordLength_eq`, and `record_pos_lt`. |
| 4 | **minor** | `Build/CfgRecord.lean` · `recordAt_iff`; `Build/RecordTable.lean` · `recordLength_eq` | These docstrings describe purpose rather than the asserted mathematics. | “As an equivalence” omits the cell interval and equality; “the record length’s formula” omits the formula. These are the bare-label style excluded by `policy.md` §2. | State the relative cell interval and layout equality, and the record-length formula, in the respective docstrings. |
| 5 | **note** | `audits/evidence/spec-api/` · replay evidence | The downstream replay remains unverified by this packet. | The bundle contains an order of 89 distinct modules and the replay script, but no completed replay log. The pack explicitly acknowledges this. | Record the completed replay against the final stacked head before claiming downstream verification. |

Answers to the seven questions:

1. **Generated-equation fidelity.** I checked all 85 printed statements against their definitions, including binders and hypotheses.

   | Definitions | Equations checked | Result |
   |---|---:|---|
   | `Contract.trans`, `seq`, `inPhase`, `branch` | 20 | Correct preconditions, state transport, times, endpoints and envelopes; linking and redirect hypotheses retained. |
   | `framedContract` | 5 | Supplied fields retained; untouched heads receive singleton envelopes. |
   | `seekPost`, `sweepPost` | 10 | All five configuration fields match their record definitions. |
   | `sweepContract`, `clearTM_contract`, `copyMapTM_contract`, `transferMapTM_contract` | 20 | Correct word premises, two-pass times, endpoints and touched-head envelopes. |
   | `walkTM_contract` | 5 | Natural-index premise, delimiter-inclusive time and displacement preserved. |
   | `skipTM_contract`, `skipBackTM_contract` | 10 | Correct premises, asymmetric times, endpoints and envelopes. |
   | `seekEndTM_contract`, `seekStartTM_contract` | 10 | Nonemptiness, current-cell and boundary hypotheses preserved exactly. |
   | `scanTM_contract` | 5 | Correct accumulator-dependent exit, rewritten interval and envelopes. |

   **Not every reduced right side is definitionally equal to the unreduced field.** For example, `skipTM_contract_lo` simplifies
   `if j = i then d.workTapePos j else d.workTapePos j`
   to `d.workTapePos j`; this uses propositional simplification. The same observation applies to `skipBackTM_contract_hi`, `seekEndTM_contract_lo`, and `seekStartTM_contract_hi`.

   For the walk premise, `FinTM.bufferTape_nat` converts the row’s `bufferTape` form to the printed `w[p]?` form. Thus `simp only [FinTM.bufferTape_nat]` supplies the bridge using an existing public lemma. No new hypothesis or new bridging theorem is needed.

2. **No behaviour change.** Confirmed from the patch: every generation attribute specifies `isSimp := false`; no hand-written addition has `@[simp]`. Existing definition bodies and statements are unchanged. `record_pos_lt` retains its exact statement and proof; only visibility and documentation change. The supplied elaboration logs contain zero errors and unchanged warning counts.

3. **Hand-written lemmas.** All ten entries—including the promoted theorem—are correct and appropriately small. Specifically:
   - `fieldsTape_of_length_le` includes equality at the layout length, correctly making the first cell beyond the list blank.
   - `z < 0` and `0 ≤ z` partition all integer cells.
   - `recordAt_iff` preserves the exact inclusive interval `[-1, (joinFields fs).length]`, without constraining cells farther away.
   - Over naturals, `n + 1 < 2 ^ posWidth n` supplies exactly `n + 2 ≤ 2 ^ posWidth n`.

   Adversarial boundary checks passed: the empty layout; a singleton empty field; a layout containing an internal empty field; and an empty walk ruler. In particular, an empty walk still costs one step, and `RecordAt` for an empty layout constrains only its two delimiter positions.

4. **E1 coverage.** F3’s record-cell access, record-length arithmetic and position-width bound are covered. `recordAt_iff` supports both introduction and elimination, including state transport through the configuration’s unchanged tape/head fields.

   G4’s named layout facts, ten row-contract interfaces, and four listed composition interfaces are covered. Findings 1–2 prevent complete closure.

   Additional interfaces remain uncovered **if a continuation chooses them**: `Contract.mapState`, `Contract.lockstep`, `RoundContract.returning`, `RoundContract.escaping`, and `ReturnContract.toRound`. The structure `Lockstep` itself already exposes its proof fields; the missing data-field equations concern **`Contract.lockstep`**.

5. **Naming and placement.** The `<definition>_<field>` names are consistent and placed in their defining modules. Generation by `simps` is acceptable for these technical equations: no independent source attribution or nontrivial proof sketch is needed. All six module headers list their additions. Finding 4 concerns statement prose, not the generation mechanism.

6. **Duplication.** The supplied 350 pair entries are identical before and after, and their reproduced-character counts sum to **116,080**. Independently extracting the screened declarations reproduces **711 → 712**; the sole newly screened declaration is `fieldsTape_of_length_le`. The scanner does not enumerate the 85 attribute-generated declarations, so these counts are not a complete public-API inventory. Inspection found no new duplicated construction or substantive proof family.

7. **Records.** The probes and printed statements match exactly: **5 + 15 + 65 = 85** names. The ten hand-written axiom entries contain only standard axioms. The lint warning set is unchanged after accounting for line counts. Freeze evidence agrees with the reconstructed patch, but its textual declaration counts omit generated names. The substantive record correction is finding 3; the outstanding verification limitation is finding 5.

**FAIL — 0 blockers, 2 majors, 2 minors, 1 note.**

