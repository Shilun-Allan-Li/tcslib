# The brief-inventory API gate (PR #118): resolutions

**Gate:** PR #118, the brief-inventory API: the equations that the pre-ship inventories of five
briefs (U2-S, B6 F5, the B6 F3 continuation, the canonizer's continuation 6, the §13d G4
continuation) found missing.
- Pack: `audits/brief-api-pack.md`.
- Round 1 bundle SHA-256: `ea12197afca2ee4fd21d1187a279629622f58a8218f9b362650b02f36e7ad6bf`
  (100 sections; folder `infra_local/gate-dispatches/34-brief-api-gate/`; Lean `4ae686be`).

## Round 1

The findings are in `audits/brief-api-findings.md`, verbatim. **FAIL: 0 blockers, 2 majors,
1 minor, 0 notes.**
- The auditor could not run Lean. It found every new equation faithful (19 hand-written, 14
  generated).
- It reproduced the patch reversals, the lint drops, both screens and the replay arithmetic.
- It found no gap for U2-S, F3, F5 or G4.

The maintainer's review sub-agent verified every finding at `9872634e`
(`audits/evidence/brief-api/r2/gate-review.md`). All three are true, at the auditor's severities.
Its re-run of the inventory, with the auditor's method fix, found one more gap (N1).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `codeSkipRepeat` has no published zero or successor equation, though cont6's generic link (a counter loop deciding `codeSkipRepeat r (counterValue c)`) needs both. **The method flaw:** the inventory scanned each cited name's *type*, never the cited definition itself. | **True.** `codeSkipRepeat` is structurally recursive, so both laws are `rfl`. `MathlibBridge.codeSkipRepeat_iter` is the iterate form and lies outside `CodeSimulator`'s import context. `canonSkipRepeat_add`/`_mul` are private composition laws.<br>**Fixed in round 2 (`88fb25f3`):** `codeSkipRepeat_zero` and `codeSkipRepeat_succ` beside the definition, with a Main-results entry.<br>**The method is fixed:** the seed-inclusive elaborator (`r2/probes/DefInventorySeeds.lean.part.txt`) also checks the cited names themselves, lists every lemma mentioning each definition, and flags structure-valued definitions whose fields lack equations. It was re-run for all five briefs (below). |
| 2 | major | `RoundContract.counterLoopDone` and `counterLoopEscape` publish `_traj` theorems but no field equations; cont6's round-contract route reads the fields. Check 8 passes them on the `_traj` names. | **True.** They are the only contract-valued definitions with missing fields across the five briefs.<br>**Fixed in round 2 (`88fb25f3`):** `simps!` (`isSimp := false`) on both gives their `pre`, `time`, `post`, `lo` and `hi`, 10 equations.<br>The review's consumer probe reads every field of both without unfolding. Its `post` goes through `counter_cfg_eq` at the Bool alphabet. |
| 3 | minor | NOTES.md counts 15 hand-written theorems in the first commit; there are 11. | **True; fixed.** `NOTES.md` now says 11 (the 9 generated equations stand). |

### The re-run inventory (the review; `r2/review-out/seedinv*`)

All five probes elaborate (0 errors).
- **cont6:** `codeSkipRepeat` is finding 1.
- **Every other new hit is judged:**
  - the worker's own file (`EffectiveCodeK.toFinTM`, `NativeAt`, `oneTapeMachineFormat`);
  - a machine read through its run lemmas (the seams, `decrementTM`);
  - covered (`fieldOffset`'s case equations, `sweepContract`'s fields, `Action.apply` as a model
    primitive);
  - not on the route (the StepBlock hazard references; `codeSkipPair`, `codeSkipWork` and
    `optStateBits` inside the proved record step C2).
- **The field sweep's results:**
  - **N1, major for F5 and U2-S:** `Cfg.mapState` and `Action.mapState` have no public field
    equations. Check 8 passes both on `mapState_apply`. The two drafts cited `mapState_state`, a
    private lemma of `Build/Contract/Seam`, which does not resolve from their files. Every seam
    and phase-host run lemma is stated through `Cfg.mapState`.
    **Fixed in round 2 (`4624fc05`):** `simps` (`isSimp := false`) on both, 9 equations. The
    renamings were on the drafts' list of model primitives "read through their existing lemmas";
    those lemmas did not exist publicly.
  - **N2, conditional:** outside the Bool alphabet, `counterLoopCfg`'s layout is private. Only
    F3's fallback Route B would meet it. **Recorded in F3's draft:** Route B needs an escalation
    for it.
  - **N3, optional:** `counterLoopOrbit` is an `abbrev`, so `rw [roundOrbit_succ]` does not fire
    on it, though `exact` and `simp only` do. **Recorded as a pitfall** in cont6's draft; no
    lemma is added.

## Round 2

- **The repair:** `lean/brief-api`.
  - It fast-forwards to `9872634e`, **MIG-12's API**, which was waiting for this gate:
    - `Action.liftSymbols`'s fields, and `Cfg.liftSymbols`'s input position, cells and output;
    - `incFixed`'s three cases and `incFixed_length`;
    - `decFixed_length`.

    MIG-12's pre-ship inventory found these, and its replay passed (user, 2026-10-16: 160 of 160,
    static-equal 80; `r2/mig12-api/`).
  - `88fb25f3` (findings 1 and 2) and `4624fc05` (N1) are the review's two patches, applied
    unchanged.
- **Tested** (the review, then the maintainer, against `oleans-lm12api`):
  - `CodeParser`, `CounterLoop` and `StateRenaming`: 0 errors, 0 warnings;
  - the 21 new names resolve, with standard axioms or none (`r2/logs/`);
  - the freeze adds publics only and changes no statement;
  - lint: 0 FAIL, 67 WARN before and after;
  - the screens: no new pair.
- **Replay:** `replay-lbapi3.sh` covers the three files' downstream closure at the round-2 head
  (274 modules), from `oleans-lm12api`.
- **The drafts** are updated for the new lemmas: cont6 cites `codeSkipRepeat_zero`/`_succ` and the
  counter-loop contracts' fields, and F5 and U2-S cite `Cfg.mapState_state` and its siblings.
  Their probes grow by those names.
