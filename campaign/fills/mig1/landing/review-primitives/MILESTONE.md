# Primitives audit-repair milestone 1

Codex maintainer subagent; 2026-11-07. **Not yet clear to merge.** This is a reproducible proof-repair checkpoint before the approved remaining T1/T2/T2b factoring. It closes neither the MIG-1 gate nor the combined replay.

Exact passing source: `milestone.lean.txt`, SHA256 `58655bb1665d43f33ce1c2a03f26ad4353170d9463fcead43533191ebcd3de02`. It is also preserved by `milestone1-source.lean.txt`. The starting shared landing head was the verified full commit `af3273f75d7602c079169f321e4536a58c7bb034`; `baseline.lean.txt` preserves its owned source.

## Completed proof repairs

`milestone1-source-freeze.json` and `milestone1-proof-repair.diff` record 22 existing proof-body changes. All declaration names/order/visibility, complete headers and imports are preserved; every executable definition, inductive and instance declaration chunk is byte-identical. `emitter_first_entry` is byte-identical and remains outside this repair. There are no source admissions, new axioms, unsafe declarations or new public/private declarations.

- Polynomial preservation and space proofs now consume public live/halted-step, action-field, run-zero and scan equations. Named `SignType.cast` unfolding is replaced by published coercion equations. The zero-degree public space proof uses the already approved `constTM_spaceUsed`, eliminating an additional hidden foreign count read.
- Forwarding administrative actions, block traversal, suffix buffering, both rewinds, emission, initialization, payload forwarding and setup head/run/launch proofs now use the published field/step/run/control-action interfaces.
- `fwdMap_parse` splits the opaque decoder result. Successful input uses `eq_pairEncode_of_pairDecode`; failure uses the one-way `pairDecode_eq_none` shape theorem with its supplied failure premise. Native execution is then proved by induction on the doubled prefix using `dbl_cons`/`dbl_nil`, the local block ledger and finish theorem. No recursive decoder equation, new decoder reader or converse failure-shape implication is used.
- `fwdMap_finish` and the public forwarding time theorem use `pairEncode_eq`. All frozen time/space coefficients and forwarding contracts are unchanged.

## Actual strict check

`Full-sections-sealed-v1.lean.txt` wraps all 42 inventoried new/moved delivery declarations in individual sections. Its manifest proves deleting only those wrappers restores the complete exact milestone source. The full module elaborated through the managed `leanelab.sh` wrapper: **exit 0, zero errors**. See the actual `.out`, `-run.json` and `-manifest.json`.

The seal marks 28 foreign definitions irreducible, adding nine omitted/reached definitions to the supplied 19-name set: `tapeBlocks`, `VirtualTag`, `virtualMove`, `virtualNextTag`, `pairEncode`, `pairDecode`, `dbl`, `constTM`, `pairDiagTM`. The three definition simp attributes (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`) are suppressed locally. `milestone1-argument-scan.json` records 302 rewrite/simplification argument lists and their inspected entry heads: no listed foreign definition or `SignType.cast` is passed as a rule. Two opaque operations occur as parameters of `fwdMap_block` theorem applications; those are operation values, not unfolding rules. This check does not claim all legacy Primitives proofs are sealed or debt-free.

`Controls-unsealed-v1` passes all 56 goals. `Controls-sealed-v1` produces exactly 56 expected rfl failures. `controls-coverage.json` independently maps one failure to every pointwise/abstracted control, confirming all 28 pairs and no unmapped error. The existing 19 pairs were read and reused as source data; nine further pairs were written and read before running. No delivered script ran.

## Dependency chain and limitations

The private complete overlay was hard-linked from `oleans-reading-preflight2`; each replaced output was unlinked first. It freshly compiles, in sequence, read-only Simulation, the peer's stable Composition, Encoding and TimeConstructible. Every source stayed unchanged during its compile and every compile exited zero; their source/olean hashes and actual outputs are in `Dependency-*.json/.out`. No shared snapshot was written or composed from independent PR snapshots.

One earlier public-time prefix failed because the starting Simulation olean lacked the producer's approved Mathlib Fin import, so `Fin.sum_univ_add` was not visible in an untouched preceding proof. Fresh compilation of current Simulation resolves that import mismatch; the subsequent complete 42-section check passes. No source workaround was applied to that preceding space proof. `diagnostic-count-errata.json` supplements the early runner's count with its `error(lean.unknownIdentifier)` diagnostic; the failed receipt and raw output remain unchanged.

Wrappers and Loop still come from the starting snapshot until the peer supplies stable current versions. Consequently no final combined dependency-axiom census, full source replay or campaign replay is claimed. The full seal retains ordinary warnings, including unused arguments that will be pruned during source polish. Failed focused attempts and unrun drafts are retained and labeled; none is represented as a pass.

## Continuing work

Root requested the approved remaining Primitives factoring: T1 retire `catalogRewind` and repoint its four callers to public `timed_rewind`; T2 factor the mirrored emitter directions within this home; T2b factor the common two-machine replay argument. These follow this immutable fallback. Cross-file `emitter_first_entry` remains pending the user's separate API ruling. No commits, Git mutations, source push, cache operation, screen or independent fill execution occurred.
