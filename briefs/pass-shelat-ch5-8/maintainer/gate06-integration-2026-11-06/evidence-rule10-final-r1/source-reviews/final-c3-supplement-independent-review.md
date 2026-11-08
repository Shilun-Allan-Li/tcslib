# Final C3 supplement: independent static review

**0 blockers / 0 majors / 0 minors found.** This is a source/API review, not a native collection or rule-10 clearance result.

Reviewed all 250 source lines, SHA-256 `4708dbb41f710acaf373e0eff6bf5631969f6f515a293fa20f629fff7b4175fd`. Current accompanying manifest/notes hashes are `41bc9d3e1a672faba56df70bbed76c7e44b6411bb72c3e97c7f6b97a0b673942` / `c1f49d7d71ea3e6d1e8f8e40154d8f889c4873a454c722d965877d1f9b81fb18`. The known Gate08→Gate06 reconciliation prose correction is present in that version.

Pins: base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`, head `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Source imports and manifest modules equal the exact fresh 54-module list. All eleven declared primary-source hashes and the full-library fingerprint-list hash were verified without executing a repository tool.

## Coverage and API assessment

- Lines 96–109 extract only cached reference arrays; ownership and visited state are not cached. Lines 122–133 seed every stored root's TYPE and available VALUE, unconditionally. Pinned Lean `ConstantInfo.value?` includes definition/theorem values and includes opaque values with `allowOpaque := true` (Declaration:470–475). Private/generated/equation roots are never filtered from grouping.
- Lines 134–156 use a fresh visited set per root. They follow referenced TCS/unknown-home TYPES and exactly same-owner `.defnInfo` VALUES, as specified. `isDefinition` is exactly `.defnInfo` in Lean 4.25 (Declaration:507–509). Foreign proof/definition values remain outside the stated traversal boundary. Shared references survive as separate `(module, root, reference)` pairs across roots; extraction caching cannot suppress them.
- The actual-Name suffix/parent detector checks raw definition parent before private-to-public fallback. It stops at the first actual definition, avoids reinterpreting an owner's private parent as another public definition, retains matcher/instance/reducible/notation cases, and records both parent and reference homes. Lean Meta/Eqns:63–115 confirms the reserved suffix family and private-wrapper shape. The intentionally conservative detector does not require inverse-registry membership and invokes no equation getter/generator.
- The graph-pruning guard is sound for well-formed imported constant types: every imported non-TCS module is checked for a complete direct-dependency list with no TCS dependency. Hence no non-TCS import path can reach TCS, by induction on path length. Types of non-TCS constants cannot introduce a hidden downstream TCS reference. TCS references supplied as application/binder/let subterms are independently visited by `Expr.getUsedConstants`. Unknown-home types are never pruned. Missing graph nodes, bad edges or missing reached constants abort collection.
- The used EnvironmentHeader/moduleData/import/index, NameMap/NameSet, String/Char and sorting APIs exist in the pinned Lean 4.25 sources. `ModuleData.imports` and `moduleNames` describe the imported graph with the documented ModuleIdx alignment. No source-level API mismatch was found; native elaboration may still fail.
- Controls check actual imported theorem presence before aliases, assert the aliases retain their exact stored references, and run through the same detector/traversal. The generated control must emit exactly the intended pair; the reader control must emit none. These metadata controls remain distinct from the eleven seal controls.

Name output is also appropriate: `ToMessageData Name → ofName → format n → n.toString` (Message:233,713; Data/Format:52–53). ROOT/REF names are not shortened to user-facing private names. `privateToUserName?` is used only for detector parent fallback.

## Required fresh runtime reconciliation

I independently read the completed fresh Gate06 collector, which has **2881 unique `(module, actual Name)` AXIOMSID rows across 54 modules**, matching every MODULE stored-constant count. Result SHA-256: `7e671fcd21f64a57e8f60fce2dbbf50365121c61e622bc63b4679c4a199fb508`; log SHA-256: `f8b1311c6e47f5168dc292fc54ef86835867144c10d0be8ea2da9aa66358285b`.

Canonical expected-root digest is `2cca5fe890d669856c1b4a829b04f38d12c99b1f6bed317503a3aebb794c876e`, computed by sorting the actual `(module, Name-string)` pairs and concatenating `module + TAB + name + NEWLINE`. Per-module counts are in the JSON. This fingerprints expected roots only; no C3 output has been compared yet.

Before treating the supplement as completed collection, root must validate:

1. Exact source/HEAD/library/checker/setup pins, matching START/source/END markers, rc0, zero errors and a fresh correctly hashed object in the intended G06 tree.
2. One successful pruning marker and exactly the two sensitivity outcomes before a single global BEGIN; one matching global END.
3. Exactly the expected 54 unique module BEGIN/END pairs. ROOT rows, including zero-hit roots and private/generated/equation/opaque roots, must be unique and equal the **exact per-module AXIOMSID actual-Name sets**, totaling 2881. Do not use `display=` strings or private-stripped names, and do not substitute a count-only comparison.
4. REF uniqueness keys must be `(owner module, root constant, referenced equation theorem)`, preserving legitimate repeated references under different roots. Parent/parent-home/reference-home payload must be consistent. Root hit counts, module pair totals and global pair totals must equal the raw REF rows; metadata controls stay separate.
5. Every nonzero REF remains a source/owner finding, including inherited and exact-notation/matcher/instance cases. Successful execution means collection completed, not zero C3 or merge clearance.

The manifest's imprecisely named `module_list_sha256` was clarified with its author and independently checked: it hashes `repairs/final-explicit-files.txt`, the 54 repository-relative Lean paths with final newlines, SHA-256 `e027117c0810eabb2cf743e19517ab36ce57ca171a700a510547aaeb966d8d35`. That file equals the fresh modules mapping's source-path list. It is not the dotted-name array or modules JSON; the provenance addendum/extractor will bind both representations. No scope mismatch was found.

No C3 source, library, Git, native scratch or evidence was changed; no collector, native/cache/build/app command or received program was executed. Only read-only source/text/hash analysis and separate ignored review artifacts were produced. The JSON records primary API references and runtime requirements. Runtime failure or nonzero findings remain possible.

**Not yet clear to merge — C3 is still unrun/unreconciled in this review; source approval does not establish collection or rule-10 clearance.**
