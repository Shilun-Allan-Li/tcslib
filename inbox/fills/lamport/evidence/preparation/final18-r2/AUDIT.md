# Frozen final 47ced: fresh eighteen-inventory preparation

This attempt targets `47ced271090f45918645c842cd358c5079092754`. It prepares fresh
`FinalR2*` phases and never replaces the eighteen historical `Final18*` phases for candidate
252ec. **Preparation invokes no Lean or Lake command and edits no TCSlib source.**

The machine-readable `queue.json` names every target, its root/evidence paths, source hash,
phase, snapshot module, collector module, immutable preparation log, and planned native
collector attempt/log. It is runnable only after the root releases the compiler slot and
the complete 177-module final R2 sweep establishes canonical products.

## Tool and source version map

`tools/prepare_seals.py` is copied byte-for-byte from the preserved R1 preparation tool;
`plan.json` and `queue.json` record its origin and SHA-256. The R2 orchestrator is copied
beside it. `sources/` retains all eighteen exact final Git blobs, each checked against the
current working bytes and the final-R2 sweep's pinned source audit. Raw preparation logs
are in `evidence/logs/final18-preparation-r2/`; every path is fresh.

`helper-source-audit.json` refreshes all sixteen helper header/options/reference checks,
immediate declaration docstrings, line counts, declaration lists, and hashes. Every helper
is below 1000 lines. The largest is Planted at 452 lines; Machine is now 340 lines; the
owned file remains 973 lines. This is source evidence, not an axiom or Rule-10 result.

`mathlib-root-audit.json` recomputes direct imports from all 177 frozen modules. They remain
exactly the issued 82 Mathlib roots, with no additions. No cache fetch is needed.

All sixteen helper paths are ABSENT at the issue base. Fresh `git cat-file -e` diagnostics
and nonzero exits are retained in `issue-base-helper-absence.log` and its JSON. Their base
comparison is explicitly not applicable; no empty/fake base compilation was prepared.

## Public-prefix duplication resolved

`public-prefix-reuse-resolution.json` records the source-level fix. Machine directly imports
`Asymptotic.ReductionSupport` and consumes its public `takeLen_poly` and `dropLen_poly`.
The duplicate local `take_poly` and `drop_poly` declarations have been removed completely.
The provider module was already in the issued order; the fix adds no module or Mathlib root.

There is no remaining promotion request for those two FP prefix facts. The earlier Machine
wrapper implementation and its preparation remain historical evidence rather than being
silently rewritten. The final source uses the existing public API.

## Three overlap-history notes

1. **overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.
   The table serialization development rederives the private two-block identity using
   published `FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`. No private proof was
   copied. The general serialization reader is disclosed for maintainer promotion review.
2. **overlap: TCSlib/Cryptography/Authentication/Signatures/Lamport.lean lamportVerFun_sign.hflat**.
   `MachineSpec.publicWord_flatten` independently reads the same local encoding identity
   from public `encodeList_eq_flatMap` and list equations. The old local fact is not a public
   provider; the new general reader remains a promotion candidate.
3. Removed-wrapper history: the earlier independent FP wrappers also matched private
   `ClassNP/TMSAT.lean tmsat_pt_take`, `CookLevin/Hardness.lean clA5Drop_native`, and
   `Candidates/DiscreteLogHardcore.lean dlb_take_poly/dlb_drop_poly`. The final Machine file
   contains none of those redundant wrapper declarations. Public provider reuse closes
   that duplication issue; their raw search/history remains in the R1 preparation evidence.

## Remaining promotion candidates

- Shared cryptographic list-encoding injectivity/equality readers.
- Generic cost-zero OracleComp return characterization and generic codec extensionality.
- General list-window, flatten/update, and finite-word serialization facts; Lamport's
  actual table/seed layouts remain construction-specific.
- Favorable-pair counting, optional-query/fair-bit averaging, finite best-position selection,
  and the generic coordinate-invariant reduction bound.
- `MachineSpec.publicWord_flatten` and `headD_drop_ofFn` as shared encoding/bit-list readers.
- Binary bounded-index encoding and the parameter-aware binary-to-unary advice wrapper.
- Nonnegative polynomial-loss negligibility and generic signature reduction closure.
- A generalized nonabort/safety reader if a second consumer needs it; the current statement
  remains specific to the typed Lamport oracle.

Existing public probability bridges are imported; no replacement expectation/`uexp` bridge
was introduced. Lamport machine realization and inversion comparison remain in this helper
directory because their contracts reference the typed table and planted experiment.

## Native pipeline still pending

For each queued phase, check Snapshot0 then Inventory through the guarded single-module
checker, using unique planned attempt names. Use the preserved tool's `prepare` with the
complete collector log to generate whole-file A/B probes and paired controls; run them with
`run_seals.py`. Preserve every raw result, source, request manifest, scan and axiom census.
The explicit-unfold scanner is conservative; manually resolve its ambiguous suffix matches.
Every actual sealed negative must fail exactly once at its recorded proof line. A genuinely
empty TCSlib import closure is recorded as empty rather than fabricating a foreign control.

The direct target axiom probe at Reuse01 is separately reported by the coordinator; this
preparation does not claim that any new collector, seal, control or complete census has run.
