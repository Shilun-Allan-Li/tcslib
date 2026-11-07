# Primitives proof repairs and local factoring

**Not yet clear to merge.** This finishes the bounded Primitives repair/factoring assignment. The maintainer owns the final combined replay, compiled before/after census and external gate.

The actual owned source is frozen at SHA256 `483ab96b55b400c3c1d4df9796b38cfec20b09f0360c68fe97a560212b1d0b80`: 415,623 bytes, 7,834 lines. `milestone3-source.lean.txt` is the exact inert copy. `final-receipt.json` pins the evidence and the six freshly compiled upstream source blobs. No actual source edits are planned after this handoff.

## Result and preservation

The original 18 reported poly/fwdMap seal errors are repaired. The parser now consumes public decoder success/failure-shape contracts; encoder reads use `pairEncode_eq`, doubled-prefix reads use `dbl_nil`/`dbl_cons`, and machine/configuration/space reads use published equations. Explicit `SignType.cast` rules were replaced by published coercion equations. No new interface was required.

All 303 surviving declaration headers are byte-identical, including 54 public headers and the statements containing `let` bindings (`literal-header-freeze.json`). Visibility, old declaration order, imports, public forwarding contracts and coefficients are unchanged. All original executable/inductive/instance chunks remain byte-identical except the two explicitly authorized private embedding `inj'` proof fields. `proof-field-exact-mask.json` masks only each exact final proof field and independently preserves its entire prefix and following documentation suffix. Both `toFun` functions and all data fields are unchanged. There are seven new private proof lemmas, no public source additions, and only private `catalogRewind` is removed. `emitter_first_entry` remains byte-identical.

## Factoring dispositions

- **T1:** retire `catalogRewind`; the four callers `lenStart`, `splitRestore_run`, `splitBody_rewind`, `emitterP2_prepare_run` each differ by exactly one callee identifier, now public `timed_rewind`. Their otherwise unchanged legacy bodies are outside the whole-region strong-seal claim; the exact substitutions and complete module typing are checked. This is the bounded scope confirmed by the maintainer.
- **T2:** one proof per direction/variant family now serves candidate/suffix rewind, bank frames, small/pair administrative frames, embedding injectivity, and left/right erasure. The erase proof uses one existing eraser first-return witness and one existing guarded phase transfer; its strict return guard and exact bound are retained. Both split-finder wrappers share `splitOrbit_find` and read the existing public generated `solveSplit.eq_def` / `solveSplitWith.eq_def` equations. Their exact formulas/axioms were printed in `Find-reader-metadata-v1.out`; these are existing compiler-generated APIs, not new source additions.
- **T2b:** `extract_replay` and `rawStrip_replay` consume one `bufferReplay_run` induction. The other proposed pairs have different contracts or already share their applicable scaffold: `lenParse_first`/`lenSuffix_run` use `lenAction_apply`; `fwdMap_block` consumes `fwdMap_first`; token doubling advances and selects control from an input bit while separator emission keeps input fixed. The independent read-only assessment is `../review-composition-loop/plan.md`; no new debt acknowledgment is inferred.
- The cross-file first-entry pair remains pending the separate user/API ruling. Existing same-home frame/update/phase lemmas are reused opaquely; their unchanged legacy proof bodies are not newly certified here.

## Executed evidence

`Final-Primitives-compile.json`: exact actual source compiled through `leanelab-o.sh`, exit 0/errors 0, stable before/after SHA, in this agent's complete private overlay. Six upstream modules were freshly compiled from their current blobs into that same overlay; no independent PR snapshots were spliced.

`Final-sections-sealed-v2-*`: complete source elaborated with **63 individually scoped sections, 37 opaque foreign definitions and three definition-simp attributes suppressed**, exit 0/errors 0. Removing only the recorded wrappers restores every actual source byte. The 42 delivery regions and 21 additional factoring regions are explicitly enumerated. Actual compiled inventory found 33 directly referenced foreign ordinary definitions, all covered by the 37 seals. `unaryTokenSplit` was added conservatively after this inventory; its definition and all generated equations were checked absent from the default simp set.

`Controls-37-*-v1`: **74/74 goals pass unsealed; 74/74 fail by `rfl` sealed**, exactly one mapped diagnostic per goal, no extras. `controls37-check.py` and `controls37-coverage.json` independently reject a duplicate-first/drop-second diagnostic set even though its total stays 74. Earlier ineffective embedding start-state controls and the invalid whole-constructor draft are preserved and explicitly rejected; the final embedding controls test transition input movement.

`Final-metadata-v1.*`: unfiltered owner census **1,462 constants**; **63 roots plus 165 descendants**, all 228 axiom closures restricted to `propext`, `Classical.choice`, `Quot.sound`. Every new helper root is private, theorem-valued and non-simp. This is a final-only compiled inventory, not a before/after public-census comparison.

`final37-argument-scan.json`: 1,041 rewrite/simplifier argument entries inspected; no forbidden foreign-definition rule head or named forbidden Core definition. The two `pairEncode`/`dbl` occurrences are opaque arguments to `fwdMap_block`, not unfolding rules. `Fin.reduceEq` is the toolchain's registered built-in simplifier procedure (`Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.lean:85`), not a mathematical definition supplied for unfolding.

## Failure and claim boundaries

All actual Lean attempts retain inert input, raw output and receipts. `diagnostic-count-errata.json`, `preparation-errata.json`, the sandbox interruption note, and rejected-control receipts explain corrections. Warnings remain in raw logs; only zero errors is claimed for passing checks. Immutable milestones 1 and 2 remain intact as fallbacks.

No admission was filled in this maintainer assignment. No source header, public API, runtime host/table, import, proof coefficient, or pending first-entry route was changed. No Git mutation, commit, push, screen, cache fetch, shared snapshot write, external dispatch, or gate closure occurred. The parent must adopt the records and run/finish its final merged-tree checks before making any merge claim.
