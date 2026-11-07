# Precisely scoped generated-matcher limitation

The generated constant `Turing.FinTM.rewind_scan.match_1` is not counted as an effective seal. Its compiled value hint is `abbrev`, its actual initial reducibility status is `semireducible`, and `isMatcher = true`. Lean accepts `[local irreducible]` and reports status `irreducible` afterwards. This distinguishes it from the fourteen actual reducible projection/`Cfg.Halted` exclusions, whose attributes Lean refuses.

`MatcherUsage.lean.txt` and `matcher-usage.out` locate exactly two direct occurrences among the forty covered roots and fifty-six descendants:

| Covered compiled root | In type | In proof value | Descendant occurrence |
| --- | --- | --- | --- |
| `_private.TCSlib.Complexity.TuringMachine.Build.Loop.0.Turing.FinTM.loopHost_input_rewind` | false | true | none |
| `_private.TCSlib.Complexity.TuringMachine.Build.Wrappers.0.Turing.FinTM.timed_ledger` | false | true | none |

No landing source names this generated constant or one of its generated equations. The public types of `Turing.FinTM.timed_rewind`, `rewind_heads`, `rewind_from_any` and `rewind_scan_heads` directly contain it: their scan-table premise is literally

```lean
∀ inp work, tm.tr scan inp work = match inp with
  | some _ => controlAction .neg (some scan)
  | none => controlAction .pos dest
```

Those statements are in `Simulation.lean` (the checked `simulation-dep-1.lean.txt` source; `timed_rewind` starts at line 598 and `rewind_heads` at 655). The loop endpoint constructs that premise by cases on `inp`, using the unchanged same-home `loopControl_idle` equation. The timed ledger constructs it by cases, normalizing the actual controller's dispatch through `branchTM_k` and `branchTM_State`. The actual host table obligations are proved, rather than introduced as new premises.

## Actual controls

The variable-discriminator point equation against the compiled defining value and the fully abstracted whole-head equation both fail **already unsealed** (`matcher-controls-unsealed.out`, two diagnostics). They provide no successful positive control and are not seal evidence.

`MatcherConstructorControls-{unsealed,sealed}.lean.txt` instead specialize the discriminator to `none`, `some false` and `some true`, with arbitrary motive and branch functions. For each constructor there is a point equation and a complete specialized-function equation. All six are kernel checked and pass **both** before and after the accepted attribute (`matcher-constructors-{unsealed,sealed}.out`). Thus the accepted attribute does not block these constructor reductions. These results are recorded as non-discriminating controls, not as six successful negative controls.

The actual source copies also pass with that attribute added: `wrappers-new-seal-v3` and `loop-new-seal-v11`. Their other operational definitions retain their effective controls and the default `simp` unfoldings remain removed. The matcher is listed separately from the thirty effectively controlled definitions.

## Existing endpoint reuse assessment

The currently imported generic native-input rewind endpoints all retain the same literal scan-table premise. `timed_start` is an unchanged opaque same-home timed-conditional endpoint, but its arrival fact alone supplies no all-prefix head ledger; replacing that ledger proof with it would require a further argument. A source inspection of the separately published `Build/InputRewind.inputRewindTM_run` found a closed machine with a different state type and the extra premise `1 ≤ d.inputPos.val`. The two covered contracts permit input position zero; no such lower-bound premise is available in their headers. That closed endpoint is therefore not a drop-in replacement without transport and additional proof work. It is not imported or used by the repaired source, and no such alternative was elaborated here.

These observations identify constructor reduction of the literal published contract as the scoped validation phenomenon. They establish no new API requirement or general matcher exemption. The external gate should assess this exact limitation alongside the raw controls and source-with-attribute outcomes; no unresolved semantic/interface leaf has been identified by this bounded review. If the gate pack cites the optional closed-endpoint comparison above, include `Build/InputRewind.lean` in its source population as well.
