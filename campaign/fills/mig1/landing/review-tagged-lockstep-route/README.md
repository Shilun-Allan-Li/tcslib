# Tagged lockstep: existing invariant route

A viable **existing-API, no-new-import route** passed isolated exact-body consumer probes for both unchanged public headers. No actual source was edited, and this report does not close T7 or acknowledge duplication debt.

## The shared scaffold

For either consumer, let `P u` be its exact desired correspondence at time `u`: an existential arrival tag, validity of that tag for the source configuration, and equality between the host run and the encoded source run. The published one-step theorem proves `Set.MapsTo (fun u : ℕ => u + 1) P P`. The published `runFrom_zero` proves the initial membership. Existing **`Set.MapsTo.iterate`** propagates that invariant, and **`add_right_iterate`** normalizes `t` iterations of `u ↦ u + 1` from zero to `t`.

Neither consumer contains an induction after this replacement. Each proves only its concrete one-step closure and invokes the same general Mathlib invariant iterator. The remaining existential unpacking and equality rewrites are the instance premises supplied to that iterator. This creates no new TM-specific host, source carrier, public API, transition table, runtime definition, or import. It preserves arbitrary completed outputs, absorbing halts, the initial tag, empty buffered words, and every time including zero through the unchanged step contracts and theorem headers.

Primary source locations: Mathlib `Data/Set/Function.lean:152` (`MapsTo.iterate`) and `Algebra/Group/Basic.lean:184` (`mul_right_iterate`, whose published additive companion is `add_right_iterate`). Both were confirmed available from a Simulation-only import. The ordinary run readers are existing Deterministic exports.

## Actual checks

- `Simulation-invariant-sealed-v1`: complete Simulation source copy; only `bufferedSecondCfg_run`'s body replaced. Exit0/errors0, 2.39s; standard three axioms.
- `VirtualInput-invariant-sealed-v1`: complete VirtualInput source copy; only `vhostEmitTM_runFrom`'s body replaced. Exit0/errors0, 1.55s; standard three axioms.
- Both guards precede the complete unchanged docstring/header. `MultiTapeTM.runFrom`, `MultiTapeTM.step` and `FinTM.VirtualTag` are irreducible; the three existing model definition-simp unfoldings are suppressed. Instrumentation removal and restoration of the old body recover every captured source byte.
- Three control pairs are calibrated with **only their respective definition opaque**. All six positive goals pass; exactly one `rfl` failure occurs in each negative goal, no extras. A same-total duplicate-first/drop-second diagnostic set is rejected (`control-coverage.json`).

All runs used the managed plain wrapper, one Lean process at a time, against the read-only complete current2 context. Exact inputs, raw logs, commands, timing and hashes are preserved. Source hashes were rechecked unchanged at completion. The branch's running replay was not altered.

## The separate zero-reader issue

The original zero cases use `⟨b, hb, rfl⟩`. This implicitly reduces `runFrom ... 0` in **both** the valid-tag field and the configuration equality. The independent small repair uses `runFrom_zero` in both fields; it is retained as `zero-reader-only-proposal.patch`. That separate patch has not had its own Lean invocation, although those exact zero-reader subgoals pass inside both invariant probes. Repairing the zero reader alone would retain the old tagged induction and would not disposition the substantive factoring finding.

## Scope and alternatives

`runFrom_comm_of_step` and Contract/Basic's `Lockstep.runFrom` use a fixed encoding. A source configuration can admit different valid initial tags, and the required result chooses an endpoint tag, so a fixed encoding does not directly supply these contracts without extra carrier/choice work. Contract/Basic also imports Simulation; importing it back is unavailable. The lower Deterministic file does not publish a direct `runFrom = iterate` reader in the inspected source.

Mathlib's product iterator and semiconjugacy iterator are available, but the successful time-indexed route avoids needing a product/runFrom bridge. No impossibility claim is made. `Nat.succ_iterate` and `Order.succ_iterate` were unavailable under current imports; the two failed availability logs are preserved. The already imported additive iteration equation removes that obstacle without an import change or a new arithmetic induction.

`proposed-invariant-consumers.patch` contains only the two checked body replacements; any production update should also adjust VirtualInput's old “Induct on t” proof sketch. It would extend the actual changed-file population to VirtualInput and requires explicit parent gate/replay accounting. The parent/auditor must judge whether the existing generic invariant reuse satisfies the tagged-family factoring requirement; this bounded probe does not infer that the old ledger exclusion applies, approve debt, or commission a new shared interface.
