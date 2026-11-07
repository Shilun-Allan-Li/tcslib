# Proposed redirect space-fact home move

**Not yet clear to merge — Seyoon's public-home/order-freeze exception is required.** No actual Wrappers/Catalog source, Git state, shared snapshot or prior Composition/Wrappers/Loop evidence was changed.

Recommend moving **`Turing.FinTM.redirectTM_spaceUsedByTape`**, with its exact existing docstring, public name, complete header and proof body, from Catalog into Wrappers immediately after `redirectTM_runFrom`. Remove the Catalog declaration. The exact two-file proposal is [proposed-home-move.diff](proposed-home-move.diff), with complete before/proposed `.lean.txt` copies and `move-freeze.json`. It introduces no public name, cast, k reader, import or machine/table change. Every other public relative order is preserved.

The reason is the frozen binder `i : Fin M.k`: elaborating that index in `(redirectTM M b)`'s per-tape measure requires the owned definition's tape-count equation. Wrappers owns `redirectTM`, so this is a legal same-home read there. Its intrinsic per-tape space fact belongs beside its published run correspondence; the existing six-line reader proof remains literal.

## Tests actually run

All runs used managed wrappers and one Lean process at a time. The base was the complete `oleans-mig1-preflight-current1` snapshot. Native publication checks used a new complete private copy (895 oleans), with only proposed temporary source copies and their two output oleans changed.

| Check | Result / receipt |
| --- | --- |
| Actual Wrappers owner prefix plus exact theorem, guard **before doc/header**, all 24 available foreign model definitions irreducible, three default simp unfoldings removed | PASS, `owner-prefix-sealed.json`; recursive axioms are exactly the standard three |
| Full proposed Wrappers native elaboration | PASS, `proposed-wrappers-native.json` |
| Full proposed Catalog native elaboration with this sole block removed | PASS, `proposed-catalog-native.json` |
| Real importing public-constant consumer, taking the equation's symmetry with redirect/model definitions opaque | PASS, `imported-pointwise-consumer.json`; standard-three axioms |
| Import Catalog and inspect actual exported owner/type/axioms | PASS, `published-api-through-catalog.json`: the unchanged name is exported from Wrappers and remains available through Catalog |

The imported pointwise consumer has an inferred result type; it proves propositional reuse of the published equation. It does **not** claim arbitrary new raw-index headers typecheck. The deliberate `ImportedFrozenHeader` boundary check still fails at `Fin M.k` versus `Fin (redirectTM M b).k` before its body. This limitation is retained, rather than hidden by an invented conversion.

Fresh paired controls cover the 24 foreign owner models plus `redirectTM` for consumer opacity: all **50** point/whole-function positives pass with kernel-checked proofs and all 50 sealed counterparts fail with exact diagnostic identities. `control-check.json` also rejects four corrupted evidence variants. The owner probe deliberately leaves same-home `redirectTM` unsealed. No unsafe reducibility setting is used. Native Catalog logs retain unrelated existing warnings; these checks are not a combined landing replay or a global Catalog seal.

## Alternative and decision scope

The alternative would add a new public `redirectTM_k` and change the frozen header to use `Fin.cast (redirectTM_k M b).symm i`. Its header typechecks under opacity, but the unchanged proof and a simple public-k normalization leave the casted-head trajectory equality displayed in the two retained `alternative-cast-header*` failure logs. That alternative was not completed or proved impossible. Its failed theorem's recovery `sorryAx` output is not validation evidence. It would require both a new API decision and a statement change; neither is part of this patch.

There are **no current Lean proof callers** to update. Imports remain acyclic and unchanged; the precise source/registry/public-order implications are in [references.md](references.md). The exception requested is only the one theorem's home and per-file order, not permission to change its public statement or proof. Root should record the ruling in the current registry/MIG-1 records and the forthcoming gate pack, leaving historical issued inputs intact.

All raw sources, outputs, actual exit/error receipts and failed attempts are retained. `SHA256SUMS` covers the finalized proposal folder. The actual source before-images still match at final verification. These are proposal tests in isolated scratch data; no source move has been applied and no merge/replay/gate clearance is claimed.
