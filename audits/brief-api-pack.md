# External audit pack — the brief-inventory API (PR #118)

Campaign: the Arora-Barak chapters 3-4 plan.
- **User (2026-10-16), "Everything":** every definition a brief's route reads gets a published
  equation before the brief is dispatched, found by a pre-ship inventory per brief.
- **The rule's standing form** (`policy.md` §1, *Definitions land with their lemmas*).
- Earlier API PRs, both gated and merged: #112 (the specification API) and #116 (the core API,
  with the zone layer).
- This PR fills the gaps that the inventories of the four drafted briefs found: U2-S, the B6 F3
  continuation, B6 F5, and the canonizer's continuation 6. **It gets its own gate before it
  merges.**

| File | Additions |
|---|---|
| `Simulation.lean` | `FinTM.bufferedCompTM_k`, `FinTM.bufferedCompTM_State`; `FinTM.VirtualTag_iff` |
| `UniversalStartup.lean` | `universalPrefixTM_k`, `universalPrefixTM_State`; `prefixCanonTM_eq` |
| `Build/VirtualInput.lean` | `vhostBuffer_eq`, `vhostBank_eq` |
| `Build/CfgRecord.lean` | `RecSym.digitEmb_apply`, `binDigits_eq`, `posWidth_eq` |
| `Build/CounterLoop.lean` | `counterLoopBody_{state,inputPos,workTapes,workTapePos,output}`; `decFixed_nil`, `decFixed_true_cons`, `decFixed_false_cons` |
| `Build/Loop.lean` | `stateWord_eq` |

- **Evidence:** `audits/evidence/brief-api/`:
  - `NOTES.md`, with the inventory method and the judgment table;
  - the patch and the logs;
  - the inventories (`inventory/`) and the inventory elaborators (`scripts/`).
- **The bundle** also contains the four drafted briefs, the six files, and the consumers the routes
  read the new lemmas through: `UniversalK`, `Build/InputDevice`, `SpaceComplexity/WindowClock`
  and `CodeSimulator`.

## Brief for the auditor

1. **Faithfulness.** Each lemma states exactly its definition: the generated `k`/`State` and
   field equations, the case lemmas of `decFixed` (all three constructors), and the `rfl`
   equations.
2. **The inventory.**
   - The main question: is the inventory complete for the four routes? Read the judgment table
     in `NOTES.md` and the inventories; challenge any "not needed" or "opaque" judgment.
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

- Built on #117's head `1358ff73` (stacked), against `oleans-lm11a`.
- **Elaboration:** 0 errors; warnings equal to the base. **Axioms:** standard only. **Freeze:**
  publics added only.
- **Lint:** 0 FAIL; check 8 drops 10 names and adds none.
- **Screen and replay:** `logs/screen-delta.log` and `replay-lbapi.log` (311 modules).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/brief-api-findings.md`. The gate closes when it has zero blockers and zero majors.
