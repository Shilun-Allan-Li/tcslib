# External audit pack — the brief-inventory API (PR #118)

Campaign: the Arora-Barak chapters 3-4 plan.
- **User (2026-10-16), "Everything":** every definition a brief's route reads gets a published
  equation before the brief is dispatched, found by a pre-ship inventory per brief.
- **The rule's standing form** (`policy.md` §1, *Definitions land with their lemmas*).
- Earlier API PRs, both gated and merged: #112 (the specification API) and #116 (the core API,
  with the zone layer).
- This PR fills the gaps that the inventories of five briefs found: U2-S, the B6 F3
  continuation, B6 F5, the canonizer's continuation 6 (first commit `277735f2`), and the §13d G4
  continuation (second commit `36325650`). **It gets its own gate before it merges.**
- G4's continuation resumes the landed partial (PR #115) on its original brief's route
  (`briefs/s13d-fill-g4.md`); its continuation brief is drafted after this PR.

| File | Additions |
|---|---|
| `Simulation.lean` | `FinTM.bufferedCompTM_k`, `FinTM.bufferedCompTM_State`; `FinTM.VirtualTag_iff` |
| `UniversalStartup.lean` | `universalPrefixTM_k`, `universalPrefixTM_State`; `prefixCanonTM_eq` |
| `Build/VirtualInput.lean` | `vhostBuffer_eq`, `vhostBank_eq` |
| `Build/CfgRecord.lean` | `RecSym.digitEmb_apply`, `binDigits_eq`, `posWidth_eq` |
| `Build/CounterLoop.lean` | `counterLoopBody_{state,inputPos,workTapes,workTapePos,output}`; `decFixed_nil`, `decFixed_true_cons`, `decFixed_false_cons` |
| `Build/Loop.lean` | `stateWord_eq` |
| `Build/Contract/Basic.lean` (second commit) | `Cfg.sameOutside_iff`, `headBox_iff`, `segment_iff`, `round_iff`, `Contract.traj_iff`; `roundOrbit_zero`; `RoundContract.hullLo_eq`, `hullHi_eq` |
| `Build/Contract/Seam.lean` (second commit) | `Cfg.bindState_{state,inputPos,workTapes,workTapePos,output}` |

- **Evidence:** `audits/evidence/brief-api/`:
  - `NOTES.md`, with the inventory method and the judgment table;
  - the patch and the logs;
  - the inventories (`inventory/`) and the inventory elaborators (`scripts/`).
- **The bundle** also contains:
  - the four drafted briefs, and G4's original brief with its partial's delivery review and
    import probe;
  - the eight files;
  - the consumers the routes read the new lemmas through: `UniversalK`, `Build/InputDevice`,
    `SpaceComplexity/WindowClock`, `CodeSimulator`, `Build/ZoneRebalance` (G4's partial),
    `Build/Contract/Catalog`, and `Build/Contract/Counter` (#117's `decFixed` consumer).

## Brief for the auditor

1. **Faithfulness.** Each lemma states exactly its definition: the generated `k`/`State` and
   field equations, the case lemmas of `decFixed` (all three constructors), and the `rfl`
   equations.
2. **The inventory.**
   - The main question: is the inventory complete for the five routes? Read the judgment table
     in `NOTES.md` and the inventories; challenge any "not needed", "opaque" or "covered"
     judgment.
   - For G4, check the route of `briefs/s13d-fill-g4.md` against the contract layer: does it
     read any definition of `Build/Contract/*`, `Build/Catalog` or the zone layer that still has
     no published lemma?
   - Name any definition outside the worker's file that a route would still have to unfold,
     other than the model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
     `Cfg.mapState`).
3. **No behaviour change.** Only declarations are added (`isSimp := false`; no `@[simp]`), and no
   existing statement or definition changes.
4. **The rule.** Every new declaration is beside its definition, its docstring states its
   formula, and lint check 8 lists none of the covered definitions.
5. **Duplication:** the screen of the six files, before and after.
6. **Records.** Check `NOTES.md` and this pack against the evidence.

## Repository-side attestations (verify or challenge)

- Built on #117's head `1358ff73` (stacked), against `oleans-lm11a`. #117 has merged, and the
  head `4ae686be` merges the tip. Its Lean differs from the replayed `36325650` only in #117's
  gate-corrected docstring (`Contract/Counter`).
- **Elaboration:** 0 errors; warnings equal to the base. **Axioms:** standard only. **Freeze:**
  publics added only.
- **Lint:** 0 FAIL. Check 8 adds no name: the first commit drops 10 names, the second 6.
- **Screens:**
  - first commit, the six files: `logs/screen-delta.log`, 0 new pairs;
  - second commit, the two files: `logs/g4/screen-delta.log`. Its 9 new pairs are all a
    segmentation artifact of the `variable` lines (`logs/g4/screen-pairtext.txt`).
- **Replays:**
  - `replay-lbapi.log`, 311 of 311 at `277735f2`, static-equal;
  - the chained `replay-lbapi2.log`, 86 of 86 at `36325650`, static-equal (56).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/brief-api-findings.md`. The gate closes when it has zero blockers and zero majors.
