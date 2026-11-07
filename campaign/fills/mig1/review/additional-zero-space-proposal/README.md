# Two additional zero-space facts — unapproved proposal

Both proposed facts are absent from the compiled interface and pass in their exact existing owner prefixes. This is a bounded API proposal, **UNAPPROVED** and not an implementation or acceptance of MIG-1. Gate 117's scope remains its existing 23 additions; these two facts belong in a separate follow-up if Seyoon approves them.

Proposed in `TCSlib/Complexity/TuringMachine/Encoding.lean`, namespace `Turing`, immediately after the existing `pairDiagTM` definition (frozen source line 323):

```lean
theorem pairDiagTM_spaceUsed (x : List Bool) (t : ℕ) :
    pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t = 0 := by
  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl
```

Proposed in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`, namespace `Turing.FinTM`, immediately after the existing `incFixedTM` definition (frozen source line 486):

```lean
theorem incFixedTM_spaceUsed (x : List Bool) (t : ℕ) :
    incFixedTM.tm.spaceUsed (incFixedTM.tm.initCfg x) t = 0 := by
  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl
```

`incFixedTM` is nullary; there is no width argument. Both proofs consume the existing public `MultiTapeTM.spaceUsed_zero_tapes_eq_zero` (`Deterministic.lean:313`). Only the owner-local fact that the machine has zero work tapes is discharged by `rfl`. Neither machine definition changes. No imports, simp attributes, tape-count readers, or other API additions are proposed. The mathematical proof sketch for each is: there are no work tapes, so the public zero-tapes theorem makes the total work-space sum zero.

The motivating cp07 Catalog rows are `computesFunInTime_pairDup_spaceUsed` (line 2158) and `computesFunInTime_incFixed_spaceUsed` (line 2259). Their bounds are the constant `c`, respectively witnessed by 6 and 3; a factor of the opaque tape count cannot be absorbed into an input-dependent bound. The two proposed operational equations suffice for their space inequalities, without exposing machine representations.

Actual checks, all against complete `oleans-mac3` using the managed plain elaborator with local slot budget 3, one sequential Lean and no outer lock:

| Check | Result |
| --- | --- |
| Compiled availability | Both requested names absent; existing prefixed constants and generic zero-tapes theorem recorded |
| Exact Encoding owner prefix + fact | Exit 0, zero errors; `spaceUsed` and `initCfg` sealed before theorem header |
| Exact Primitives owner prefix + fact | Exit 0, zero errors; same seal |
| Two hypothetical constant-bound consumer shapes | Exit 0, zero errors; both machines, `spaceUsed`, and `initCfg` sealed before headers |
| Paired controls | Eight unsealed pass; eight sealed fail exactly once each with the intended `rfl` error |
| Offline checker negatives | Duplicate diagnostic, missing diagnostic, and exit-0-with-errors all rejected |

The controls cover each machine's tape-count projection and complete constructor equation, plus pointwise and abstracted equations for `spaceUsed` and `initCfg`. Machine constants are nullary. Definition-level `initCfg` simp unfolding is disabled in sealed probes. All four checked theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

`Consumers.lean.txt` takes the proposed interfaces as theorem parameters: these are **hypothetical sealed consumers**, checked separately from the owner proofs, not imports of published new constants or an integrated Catalog repair. No Catalog proof, whole migration, gate, or source-tree replay is claimed here.

`context.json` records the maintainer-supplied API worktree head `1160c18f03fd318f0dec25738790935fa61379d4`, the complete snapshot adoption receipt, and exact owner-source/compiled-module hashes. `results.json` independently verifies all input/output/request receipts, diagnostic multiplicities, axiom lists, and unchanged hashes. Raw logs, request/run JSON and every actual input are retained; no failed proof attempts occurred in this bounded proposal. Synthetic checker-negative logs are explicitly not Lean runs.

No source, Git state, snapshot, or compiled cache was changed. Runtime copies were temporary `/private/tmp/*.lean` files; records contain only `.lean.txt`. `SHA256SUMS` covers every file here except itself.
