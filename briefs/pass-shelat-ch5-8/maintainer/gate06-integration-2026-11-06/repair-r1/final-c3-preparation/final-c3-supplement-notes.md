# Unrun final C3 metadata supplement

**Prepared, not run. C3 remains NOT_MEASURED.** Source `final-c3-supplement.source.txt` has 250 lines, SHA256 `4708dbb41f710acaf373e0eff6bf5631969f6f515a293fa20f629fff7b4175fd`. It imports exactly the 54 final math modules at base `eee107e92a7db11f1f8c98a5c2867304f57ddc54` / HEAD `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. All earlier audit artifacts remain unchanged.

## Coverage and cost

Every stored constant of every target module is a separate root, selected by actual imported-module identity from `env.constants.map₁`; private/generated constants and roots that are themselves equation theorems are not filtered. Each root seeds **both TYPE and VALUE**. `value? (allowOpaque := true)` includes opaque values too; the Gate08 helper's default `value?` omits those, so this is a deliberate coverage extension. Referenced TCSlib TYPES are traversed recursively, as are unknown-home TYPES and same-owner `.defnInfo` VALUES. Foreign theorem/definition VALUES are not followed. This is the requested Gate08 traversal boundary, with explicit opaque initial values.

A separate visited set per root records every owned-constant/reference pair, including pairs shared by several roots. Work uses Array push/pop. Extracted type/value reference arrays are cached by actual Name across all roots, while the ownership decision remains per module. There is no repeated append to a growing list and no per-owner expression rescan. For a fixed environment, each reached constant is expanded at most once per root. Cost is proportional to the reachable TCS type/same-owner-value graph per root plus boundary references; no native timing is claimed.

Non-TCS type traversal stops only after a complete runtime dependency guard: every direct dependency of every imported non-TCS module must itself be imported and non-TCS. By induction on import paths, none can depend on a TCSlib module; a well-formed constant TYPE cannot mention a downstream module outside its dependency graph. This uses actual imported `ModuleData.imports` / `Import.module`, not filename guesses. Missing graph nodes or a non-TCS→TCS edge throw an error before controls or census. Unknown-home types are always followed. A failed guard is an incomplete harness result; root would need a separately reviewed full-traversal fallback, never a zero claim. Static source inspection also found no TCSlib import in the pinned Lean/Init/Mathlib source roots.

## Detector and controls

The detector reads actual Name suffixes `.eq_N` / `.eq_def` / `.eq_unfold`, resolves the actual definition parent first and then a private-wrapper fallback, and requires a foreign TCSlib `.defnInfo` parent plus actual `.thmInfo` reference. It records actual root, reference, definition parent, parent home and reference home. It stops at the first actual parent, preventing a local private definition from being reinterpreted as an unrelated public definition. It preserves every reducible, instance, matcher and notation parent; there are no `PolyExpr.eval` / `glNeed` exclusions or root-equation exclusions.

No equation getter is called and no name is reconstructed from strings. Inverse equation registration is not a filter: imported `.eq_def` / `.eq_unfold` or matcher equations may not be registered there. The conservative reported set includes every actual theorem with the compiler-reserved suffix and an actual foreign TCSlib definition parent; any unexpected pattern is retained or fails validation rather than silently disappearing. Unknown/missing reached constants, unhomed equation references, and non-theorem foreign equation-style references fail the probe.

The positive control aliases actual imported `BoolCircuit.TreeCircuit.size.eq_def`, already used by LayeredCircuit:249; the public-reader negative aliases `BoolCircuit.TreeCircuit.size_node` (Basic:218). Presence as imported theorems is checked **before alias elaboration**, so the control cannot synthesize an absent equation. The aliases' stored values must retain the exact reference. The same detector must find exactly one `(size.eq_def, size)` pair for the positive alias and zero for the reader alias. Both controls must pass before any audit BEGIN. They test C3 metadata sensitivity only, and do not replace the eleven seal controls.

## Launch interface

Root should first read the complete source and manifest. Place the exact source bytes at fresh ignored target `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/rule10-final-c3/G06C3Supplement.lean`; do not overwrite an earlier scratch module or attempt. After all active native work finishes, launch serially with cwd `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`:

```text
python3 -I /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/check_probe_v2.py /Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/rule10-final-c3/native .lake/ps-maintainer/gate06/rule10-final-c3/G06C3Supplement G06C3Supplement
```

The expected native tree is `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/oleans-gate06-r1` via the existing G06 checker/setup. No launch or source-copy helper is added; the standard one-module checker remains the sole execution interface.

## Required result reconciliation

`G06-C3-PRUNING` records the successful dependency guard. Two `G06-C3-CONTROL` markers precede `G06-C3-BEGIN`. Every audited module emits MODULE-BEGIN/END with its complete root count; every actual stored root emits one ROOT row, even with zero hits. Every owner/reference pair emits one REF row. Module and final pair counts must equal the raw rows. Control pairs are separately labelled and excluded only from the library-census totals.

Root must compare the **exact per-module actual Name sets** in ROOT rows with the completed Gate06 final `evidence-rule10-final-r1` `AXIOMSID` census (2,881 actual identities across 54 modules); a numerical count alone is insufficient. The Name fields are exact: pinned `Lean/Message.lean:713` selects `MessageData.ofName`, and `Lean/Data/Format.lean:52–53` formats a Name via `n.toString`, preserving private/generated identities. Then validate the global/module end markers, all pair counts, source hash/stability, rc0/no diagnostics and fresh object. This supplement does not consume an in-progress collector log, and its manifest does not pretend to bind an unfinished result.

For the hardened scanner bridge, publish **all 54** `{module}.eqn.txt` files, including a zero-byte file for each verified zero-hit module. Each nonempty row is `[module, owner, parent, eqnref]`, tab-separated: map `G06-C3-REF m | root | ref | parent | parentHome | refHome` to `m TAB root TAB parent TAB ref`. Preserve every library REF row, including notation references; sensitivity-control rows stay separate. Empty files may be produced only after complete successful collection and exact census reconciliation, never for absent/partial inputs. The extractor remains a separate root step.

A successful native invocation means the census completed. Any nonzero REF rows remain findings for source/owner review, including inherited and exact-notation cases. They are not source-failure exclusions, waivers, or a rule10 pass. Until root runs and reconciles this probe, C3 remains NOT_MEASURED. Earlier explicit-list/C2/seal claims remain separate.

Only read-only source/Git inspections and ignored proposal writes were performed. No Lean/cache/native process or received program was run; no library, Git or campaign evidence was mutated.
