The one-reader hypothesis closes the complete existing MARMTime proof. It remains a private proposal requiring Seyoon's public-API decision; no repository or public source was changed.

The exact proposed non-simp reader is `Turing.MultiTapeTM.ConfigCount.core_eq`, beside the unchanged `core` definition in `TCSlib/Complexity/SpaceComplexity/ConfigCount.lean`. It states the existing four-field constructor equation, excludes the output tape exactly as `core` already does, and is proved by `rfl` in its owner. Its full elaborated type/universes and empty axiom closure are in `SELECTED-TYPES.md` and the three raw metadata runs. `API-only.patch` is separate from `consumer-only.patch`; their SHA-256 values are in `SOURCE-FREEZE.json`.

```lean
/-- The core records exactly the state, input position, work tapes and work-head
positions of a configuration, in that order; it omits the output tape. -/
theorem core_eq (c : Cfg k Bool S x) :
    core c = (c.state, c.inputPos, c.workTapes, c.workTapePos) := by
  rfl
```

The original complete `TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean` is byte-exact at both MAC8 `9b5dcf46408db681bcbc721930ef2203fa6bc47d` and FH13 `f3c8c050ef98375bc237c72bde74f83d33833374`. The consumer candidate preserves its complete docstring, local open command, header, imports, definitions, attributes and every other declaration. It replaces the local Nat.find first-halt derivation with existing `MultiTapeTM.exists_first_halt`, uses `mem_visitedByTapeHead_iff` in `hwin`, uses the proposed `core_eq` in `hcore`, and retains the canonical first-halt endpoint equality. All finite-code/cardinality and growing-tape mathematics remains the existing proof. No gate129/three-reader API is used.

| Check | Actual result | Evidence |
|---|---|---|
| Complete ConfigCount candidate owner | PASS, exit0, errors0, admissions0 | `runs/core-owner-native1/` |
| Complete MARMTime candidate owner | PASS, exit0, errors0, admissions0 | `runs/marmtime-owner-native1/` |
| Complete literal target guard | PASS, exit0, errors0, admissions0; all5 live guards effective | `runs/marmtime-full-target-sealed1/`, `GUARD-SCOPE.json` |
| Selected type/universe/AX | Consumer exact MAC8 type/universes, standard3 AX; reader AXempty/nonsimp;2 HEAD raw outputs byte-exact | `SELECTED-CHECKS.json`, all3 metadata raw outputs |
| Paired controls |10 kernel-checked positives;10 intended sealed failures; no unexpected error | `CONTROLS-CHECKS.json`, both raw outputs |
| Explicit simp/rw arguments | All20 nonlocal arguments resolve to theorem declarations; only local `code`/`cnt` definitions are simplified | `EXPLICIT-ARGUMENT-CHECKS.json`, full source rows |
| Import/source context | No import addition; existing51-node TCSlib closure acyclic; all closure sources except freshly compiled ConfigCount are MAC8/f3 exact | `IMPORT-ROUTES.json`, `IMPORT-GRAPH.json`, `SOURCE-PROVENANCE.json` |
| Physical objects | Original895 MAC8 hashes unchanged; private895 changes exactly ConfigCount and MARMTime | `OBJECT-CHECKS.json`, complete before/after maps |

The fresh complete-target footprint guards `runFrom`, `initCfg`, `visitedByTapeHead`, `ConfigCount.posCode` and `ConfigCount.core`. The active definition simp-unfold row for `initCfg` is removed. Both originally problematic definitions are guarded; explicit foreign-definition arguments are absent, so the check does not rely on `simp [Def]` bypassing opacity. The reader itself reaches no ordinary other-file definition: only record projections plus its own `core`. The scope includes the entire target header/body with the exact preceding owner source as context. Earlier `step_last_cell`/`last_tape_run` and other theorem proof-values remain unsealed boundaries; their implementation is not cleared here.

The prerequisite search preserves all current1003 source hits and all9699 raw hits across captured428 available refs/298 distinct commit heads (including current prepared branches and prospective final-eight). Relevant existing `core_step`, `core_runFrom`, `core_injOn` transport/exclude equal cores; `coreCode_inj` starts from another opaque finite code and does not provide this field introduction without reading it. No named constructor/equality-iff reader was found. This is candidate enumeration plus source inspection, with no remote fetch or semantic completeness claim.

All9 own Lean helper invocations completed sequentially under the shared local3/machine5 locks with nice10/j4. There were no failed native/sealed source drafts. Three read-only preparation reads used absent guessed filenames; `preparation/READ-DISPOSITIONS.json` preserves those preparation errors. The negative control run exits1 with exactly its10 intended errors and is not a failed candidate. No screen or downstream replay was launched.

If Seyoon approves this one exact API, root can adopt the API-only patch and then the complete consumer patch through the usual source PR/gate/current-tree validation. This proposal does not close gate122, clear its other held sites or enlarge accepted debt. The physical temporary project/compiled clone live outside this evidence packet and remain private validation context; source captures, exact helpers, raw logs, input/output hashes and three independent MAC8 anchors are inside. Helper paths record their actual execution locations and require rebasing to reconstruct a different temporary layout; no self-contained external snapshot distribution is claimed.
