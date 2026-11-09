# Approval-only CfgFacts import proposal

The proposed frozen-file change adds exactly `import TCSlib.Complexity.TuringMachine.CfgFacts` to Hardness and re-points two existing proof bodies to the already published `Cfg.mapState_eq_of_fields`. It does not add a declaration, private generic bridge, statement, name, host, route or new reader design.

For Prepare, the existing public characterization identifies the configuration before its right-state renaming; the existing `Cfg.mapState_apply` and `controlAction_apply` then read the stationary action. For the comparator, the same characterization replaces its existing local five-field identity proof. `Option.map_id` is a function equality; its required pointwise instance is `congrFun Option.map_id cfg.state`. The exact original suggested `Option.map_id _` does not elaborate, and its actual failed full-owner native is retained.

The source import graph grows from54 to55 TCSlib modules including the owner; the sole added module is CfgFacts, whose full existing source is captured. The proposal preserves every literal theorem header/docstring/definition/name/attribute and all other source bytes after removing the single import and reversing the two proof edits.

This proposal is separate from the already frozen nine no-import repairs and the EXP absorb repair. It does not solve or acknowledge Fresh/Prepared's arbitrary-right seam reading gaps, promote the existing private seam step theorem, adopt API129/controlAction_def, fill mathematics, close a gate or clear a merge. The import ruling remains the user's; root owns any source integration and current-tree replay. No approval is inferred from private probe success.

Use only the exact final patch named in ADOPT.json. Historical source/native HYP v1 and the incomplete default-simp guard04 remain evidence of actual failures/limits, not current validation. The final guard must remove every actual unfold-simp entry (Action.apply, MultiTapeTM.initCfg, Cfg.init); its receipt and all36 controls are bound before final freeze.
