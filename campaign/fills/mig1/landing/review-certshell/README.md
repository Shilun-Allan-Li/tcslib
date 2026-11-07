# CertShell changed-region audit repair

**Applied and checked; stable for integration.** Only `wt-epad/TCSlib/Complexity/TuringMachine/Build/CertShell.lean` was edited. The sole changed binding from the handoff is the body of private `Turing.cert_prepare_exists`; all public/private headers, declaration order, imports, public proof bodies, executable definitions and tables, and every other declaration's bytes are unchanged. No admission, API or host was introduced. No commit or push was made.

Received source SHA256: `d792722cc144ae92dc32071b9406025264bd057f132577941cc962ca67daa84c` (includes the root maintainer's four `Cfg.ofWords_state` premise repairs). Applied/final SHA256: **`7e291596dd6af5173af437ae20eca7d35b1d75f6a6f9d501c3372ecb00b68f40`**. `CertShell-start.lean.txt`, `CertShell-final.lean.txt`, `certshell-repair.diff` and `application.json` preserve the exact handoff, milestone and freeze.

The complete changed proof now reads foreign structures through their existing public equations:

- Layout arithmetic uses `vhostBuffer_eq`, `vhostBank_eq`, and `vhostCap_eq`, including the formerly implicit capture-index `rfl`.
- The closing `cert_silent_words` state/input/output premises use `vhostCfg_state`/`_inputPos`/`_output` and the corresponding `Cfg.ofWords_*` readers. Selected tape/head premises use the generated pointwise `vhostCfg_workTapes`/`_workTapePos` equations, then canonical-seam field equations and the existing Fin block case lemmas. No foreign configuration is unfolded to expose those fields.
- The four framed copy/transfer state premises already repaired at handoff remain `Cfg.ofWords_state`; their tape/head premises retain their public equations.
- The proof-local witness explicitly records its existing initial label, and runs are transported using public `MultiTapeTM.runFrom_with_q₀`. This avoids reading the opaque seam/copy controller initial states. The local transition table is unchanged.

The proof-local witness is changed from

```lean
let D : FinTM Bool := ⟨K, _, M₅⟩
```

to

```lean
let D : FinTM Bool := ⟨K, _,
  {M₅ with q₀ := .inl (.inl (.inl (.inl (.inl SweepPhase.sweep))))}⟩
```

The maintainer authorized this bounded initializer annotation after the first strict attempt exposed the hidden initial-state read. The separately executed **unsealed diagnostic** proves the explicit label equals the old `M₅.q₀`, the whole new `D.tm` equals `M₅`, and `D.tm.tr = M₅.tr`, all by `rfl`. Thus the original carrier, initializer and transition function are preserved. Those diagnostic foreign reductions are **not in production**; the production transport uses the published run equation. No initial-state API was added.

## Executed checks

All checks used the repository's plain managed `leanelab.sh`, local Lean slot budget 3, one sequential Lean and no outer lock. A private **complete** hard-linked overlay of `oleans-mra2` was used; offline verification finds the same 895 file paths and hard-link identities as the snapshot. No compiled output was requested or written.

| Check | Result |
| --- | --- |
| Exact full applied source | Exit 0, zero errors |
| Exact full source with target-only strict guard | Exit 0, zero errors; guard before the target docstring and header |
| Target axiom print | `propext`, `Classical.choice`, `Quot.sound` only |
| Initializer / whole machine / transition-table diagnostics | Exit 0, zero errors |
| Final unsealed controls | 82 examples, exit 0, zero errors |
| Final sealed controls | Exit 1; exactly one intended `rfl` error in each of 82 examples, no extras |
| Checker negative tests | Duplicate diagnostic, missing diagnostic, exit-0-with-errors all rejected |
| Source freeze / exact applied–sealed identity / receipt hashes | Pass |

The strict guard covers **41 ordinary definitions**: model 14; Simulation five; additional simulation/pair primitives retained from the reviewed shared controls; `Cfg.ofWords`, `Cfg.mapState`, all four virtual-input layout/configuration definitions, `vhostEmitTM`, the silent configuration/forwarding embedding, seam/copy/transfer controllers and `stateWord`. `seal-inventory.json` lists exact names. Default-simp unfolding is disabled for `Action.apply`, `Cfg.init` and `MultiTapeTM.initCfg`. The final controls include both pointwise and abstracted equations for every guarded definition.

`cert_silent_words` and the other unchanged legacy helpers are defined **outside** the guard and remain opaque theorem dependencies of this changed region; their implementation is not rewritten or newly certified here. Primitive field projections are read on variables/local records or through the cited public equations. The general reducible-abbreviation convention is recorded in the inventory; no unsafe reducibility or abbreviation-based bypass is used in this proof. The only full-file warning is the pre-existing unnecessary `simpa` at line 184.

`argument-inspection.json` retains tactic lines and verifies no guarded foreign definition is explicitly supplied as a simplification/rewrite/unfold argument. The remaining `change` statements expose no foreign representation: they occur after field equations and Core/Mathlib Fin case reductions, with buffer tapes still opaque. The final strict input is checked byte-for-byte to be the applied source plus only the section/guard and axiom-print insertions.

## Preserved attempts and limits

`CertShell-strict-v1` failed at two uses of the old implicit controller initializer. The explicit proof-local start annotation repairs that boundary; v2 and the final axiom-print v3 pass with all 41 guards retained. All failed and passing sources, raw outputs, commands and exit/hash receipts are archived.

The first 82-example negative control input produced only 80 failures: its `embedEmitTM.q₀` pair used `Unit`, whose singleton eta made both equations definitionally true despite the guard. It is explicitly rejected by the offline checker. V2 changes only that pair to Boolean state, yielding all 82 intended failures. The final v4 also strengthens the inherited `moveInputPos` control into its complete abstracted clamping-function equation over positions and moves. Its intermediate v3 used the mathematically true zero-move identity, which is not definitionally equal for arbitrary positions and therefore failed the positive `rfl` check; that failed input/output is retained. V4 uses the exact existing definition equation and both final control runs pass their intended results. These were control repairs, not permission to exempt an ordinary definition. Synthetic checker-negative logs are not Lean runs.

This checks the changed CertShell region and actual source against the complete mra2 import context. It does **not** claim the uncommitted multi-agent MIG-1 landing or downstream closure has been replayed, that unrelated legacy reads are sealed, or that a gate has closed. The maintainer integrates the disjoint source repairs and runs that closure. No screen, cache update, shared-snapshot change, other source edit or Git operation was performed. `results.json` verifies the receipts and controls; `SHA256SUMS` covers every archived file except itself.
