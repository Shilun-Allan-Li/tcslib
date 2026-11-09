Two non-simp field-reader hypotheses close both complete held SingleTape proofs, with no work-head equation or further API/header/import gap needed. They remain private proposals requiring Seyoon's public-API decision. No repository or canonical source was changed.

The exact existing definition home is `TCSlib/Complexity/TuringMachine/Sweep.lean`, already directly imported by SingleTape. There is no `Robustness/Sweep.lean`; the initial failed read using that path and its resolution are preserved. The two equations expose only the supplied state and output of `sweepRevCfg`; both are own-definition `rfl` proofs, AXempty/nonsimp, with zero ordinary foreign definitions in their full type/value/own-helper footprint. No separate empty-opacity execution is claimed or needed for those zero obligations.

```lean
/-- The reverse-sweep configuration has the supplied control state. -/
theorem sweepRevCfg_state {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepRevCfg q p z l r out).state = q := by
  rfl

/-- The reverse-sweep configuration has the supplied output word. -/
theorem sweepRevCfg_output {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepRevCfg q p z l r out).output = out := by
  rfl
```

The complete producer and consumer originals are byte-exact at both MAC8 `9b5dcf46408db681bcbc721930ef2203fa6bc47d` and FH13 `f3c8c050ef98375bc237c72bde74f83d33833374`. Every old definition, machine, import, name, attribute, other declaration, and both complete target docstrings/headers remain unchanged. The public `one_work_tape` and private `dg_all_inputs` use existing `computesFunInTime_iff`/`computesFunInTimeVia_iff`/`computesInTime_iff` for predicate readings/introduction, and canonical `exists_first_halt` for their strict cuts and state/output endpoints. The two new field equations replace final reverse-sweep state/output conversions. The demand-grown proof uses `mem_visitedByTapeHead_iff`, `spaceUsed_eq_sum` and `spaceUsedByTape_eq_card` for the existing visited-cardinality calculation. Its existing `DGSpan` already carries the final head bounds, so no work-head field reader is introduced. All simulation, arithmetic and window mathematics remains the previous proof.

| Actual check | Result | Evidence |
|---|---|---|
| Complete Sweep producer native | PASS, errors0/admissions0 | `runs/sweep-owner-native1/` |
| Final complete SingleTape owner native | PASS, errors0/admissions0;2 warnings in exact unchanged preceding helper source | `runs/singletape-owner-native2/`, `WARNINGS-DISPOSITION.json` |
| Both literal complete consumer declarations sealed | PASS,8 and11 fresh ordinary foreign heads, live witnesses; exact control options | `runs/both-complete-targets-sealed1/`, `SingleTapeSealed.lean.txt` |
| Guard effectiveness |24 fresh kernel-checked positive identities,24 intended sealed failures;0 unexpected control error | `CONTROLS-CHECKS.json`, both complete raw outputs |
| Exact selected metadata | Both old full types/universes exact BASE, standard3 AX unchanged;2 new APIs absent BASE/AXempty/non-simp;2 HEAD raw runs byte-exact | `SELECTED-CHECKS.json`, `SELECTED-TYPES.md`, all3 raw queries |
| Explicit rewrite arguments |18 nonlocal arguments are theorems; only2 owned private definitions (`sweepStart`/`dgStart`) and2 owned local lets are explicitly read | `EXPLICIT-ARGUMENT-CHECKS.json`, all full source rows |
| Source/import context | Existing9-file TCSlib closure acyclic and BASE/f3 exact; no import change or129/core/ND API dependency | `IMPORT-GRAPH.json`, full3-phase captures |
| Physical input/output | Original895 MAC8 hashes unchanged; private895 changes only Sweep and SingleTape | `OBJECT-CHECKS.json`, full maps,3 independent MAC8 anchors |

The12-head union is `ComputesFunInTime`, `ComputesFunInTimeVia`, `ComputesInTime`, `sweepAct`, `indexedVisit`, `runFrom`, `initCfg`, `sweepRevCfg`, `spaceUsed`, `Action.mapState`, `visitedByTapeHead` and `spaceUsedByTape`, with complete qualified names and per-root8/11 membership in `GUARD-SCOPES.json`. In particular, `sweepRevCfg` itself stays opaque throughout both full targets. The actual `initCfg` definition simp-unfold row is removed. Explicit TCSlib/Core/Mathlib foreign-definition arguments are absent. The only new local field reading is `hk_one : (dgTM M a₀).k = 1 := rfl` on the unchanged same-source private machine; it survives every foreign guard.

The initial full SingleTape native attempt failed at the last space-cardinality step: the public sum equation exposed `(dgTM M a₀).k` as a multiplier, while the old raw `change` had written the binder as `Fin 1`. Its whole source, exact patches, raw error and disposition are retained in `preparation/attempt1-owned-tape-count/` and `runs/singletape-owner-native1/`. Naming that already-owned field equality in the simp list resolves the issue without another API, frozen-header change or mathematical argument. The initial failed attempt had1 error and no admissions; the final native and guard have0 errors. The negative-control run exits1 with exactly24 intended errors. All10 own Lean wrapper invocations completed sequentially under local3/machine5 locks, nice10/j4. No screen or downstream replay ran.

Metadata traverses the selected full type/value, all reached constant types and recursive own definition-helper values (29 and34 for the consumers). It stops at other theorem proof-values, including same-owner/private/generated theorem boundaries, and foreign definition values. Earlier/later source and existing simulation theorem implementations remain unsealed context; no unrestricted theorem-value closure or clearance of those implementations follows. Accepted debt kinds and other held fronts remain unchanged.

The prerequisite search preserves every current1003-source hit plus all25344 raw matches across captured428 available refs/298 commit heads, reducing to188 distinct path/line/source rows in Sweep/SingleTape. Named existing candidates are the reverse configuration and published/private action lemmas, with no standalone state/output field reader found. This is source-shape enumeration plus inspection, without remote fetch or a semantic completeness claim. The executed complete route certifies that exactly these2 proposed field equations suffice here.

`API-only.patch`, `one_work_tape-only.patch`, `dg_all_inputs-only.patch` and `both-consumers.patch` are separated exact diffs; `SOURCE-FREEZE.json` records their hashes and complete body/header bindings. Root can bring the exact2 reader statements for Seyoon's decision, then handle any source/gate/replay adoption. The physical private project/whole clone remain outside the evidence packet; full sources, actual requests/logs/helpers, object/source maps and toolchain/package provenance are inside. `REPRODUCTION.md` distinguishes the historical initial preparation script from the final exact captures and explains path/snapshot requirements. This is not a gate closure, dispatch or global debt-retirement claim.
