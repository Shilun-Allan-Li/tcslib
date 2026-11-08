# Instance projection sealing: pinned-source analysis

R1 is **not a valid instance-body sensitivity control**: both native files returned rc0/error0/fresh object. Its sealed source checks catalog/reducibility only before the attribute, then proves `(default : Turing.Cfg 0 Bool Unit []) = constructor` by term rfl. It neither verifies post-attribute status nor explicitly records the synthesized instance expression. Those experimental gaps require a fresh pilot, but pinned Lean source independently exposes a structural projection blind spot in ordinary local-irreducibility sealing.

The relevant primary code is Lean4.25.0 under the installed pinned toolchain:

| Source | Mechanism |
|---|---|
| `Init/Prelude.lean:292` | Term `rfl` is the polymorphic Eq reflexivity definition; accepting it invokes definitional equality. |
| `Lean/Meta/Tactic/Rfl.lean:67–99`, `Tactic/Refl.lean:25–39` | Tactic reflexivity also uses Meta definitional equality. |
| `Lean/Meta/GetUnfoldableConst.lean:15–26` | `.default` refuses irreducible names; `.instances` unfolds a registered global instance even when it is irreducible. |
| `Lean/Meta/ExprDefEq.lean:2105–2108,2152–2156` | Definitional equality normalizes projections with `.yesWithDeltaI`. |
| `Lean/Meta/WHNF.lean:697–705`, `Basic.lean:2059–2062` | Projection reduction invokes whnfAtMostI, which maps default transparency to `.instances`. |
| `Lean/Meta/WHNF.lean:775–798` | Class-projection unfolding also expressly uses reducible-and-instances reduction. |
| `Lean/Meta/ExprDefEq.lean:67–99`, `Basic.lean:145–147,739–743` | Structure eta can compare a whole instance to a constructor through its fields; whole-instance equality is therefore not automatically a safe alternative negative. |

Thus, **if the intended registered global instance is selected and is confirmed irreducible**, unification of its class-field projection can still unfold its body. Explicitly naming that same instance does not by itself close this path. This is a blind spot for global-instance projections, not a claim that every possible instance use ignores the seal. The R1 result alone does not prove its exact elaborated selection/status; the source mechanism is an independent explanation and prediction for the explicit fresh pilot. No new native experiment was run here. The existing thirteen-control InstanceBody fixture must not be counted as successful negative sensitivity on these results.

There is a distinct, public environment-state API suitable for a fresh **uncompiled** harness-only masking pilot. `Lean.Meta.globalInstanceExtension` (`GlobalInstances.lean:15–26`) stores only the Name-to-Unit membership used by unfolding. `Lean.Meta.instanceExtension` (`Instances.lean:72–98`) separately stores the search discrimination tree, instanceNames entries and erased set. `addInstance` updates both (`Instances.lean:232–239`); candidate lookup reads the latter (`SynthInstance.lean:203–216`). This Command-level snippet edits only the former current scope state:

```lean
-- UNCOMPILED proposal; n is the already verified actual Name.
modifyEnv fun env =>
  Lean.Meta.globalInstanceExtension.modifyState env (fun s => s.erase n)
```

`ScopedEnvExtension.modifyState` (`ScopedEnvExtension.lean:213–217`; SimpleScoped alias:237) updates only that extension's top state. It does not invoke instance-attribute removal, edit a public definition, create aliases or reorder search entries. This is a plausible additional sealing mechanism, not a checked theorem or approved native result. Ordinary whole-file verification must remain separate and unchanged.

Required pilot invariants were sent to the route author:

- Before/after/EOF record actual Name/home, semireducible→irreducible status, global membership true→false and isInstanceCore remaining true. Check the exact class target, candidate order and synthesized Expr with no alias replacement.
- Compare full lookup entry fields: keys, val, priority, globalName?, synthOrder and attrKind. `InstanceEntry.BEq` (`Instances.lean:61–62`) compares **only val**; its ToFormat prints only a name. Neither alone certifies preserved priorities/order/metadata.
- Use fresh MetaM states or resetCache (`Basic.lean:638`) before each before/after synth/defeq sample. withNewMCtxDepth alone does not clear caches. `resetSynthInstanceCache` is at666; the synthesis cache key (`SynthInstance.lean:791–801`) lacks the changed global-membership state.
- Require actual unsealed body pass, masked sealed sole-body rfl failure, and published-reader/TC-only positive passes. Confirm status/state again at EOF. Test section/namespace push/pop and scoped activation/re-registration: the top-only edit can be restored or a membership flag re-added by later scope operations. No dropped names or notation exceptions.

Unchanged lookup data does **not** establish universal typeclass-feasibility/selection preservation: synthesis itself uses `.instances` transparency (`SynthInstance.lean:787–790`), so changing unfolding can affect unification during candidate checking. Exact positive selection tests are bounded evidence; future normalization/body-dependent failures are review-required candidate observations, not passes or automatic source violations. Scoped-instance activation and temporary re-registration require explicit guards/review. The proposed mask does not block explicit `.all` reduction; this report grants no tactic/transparency waiver or general completeness claim.

The source/input hashes and raw R1 receipt facts are retained in `primary-inputs.json`. This reviewer only read source/data and generated ignored notes; no Lean/cache/build/app command, proposed-program import/execution, public-source edit or Git mutation occurred. R1 is preserved unchanged. Root owns all fresh native pilots and any later harness version.

**Not yet clear to merge — instance projection sensitivity and the masked variant require actual controlled validation.**
