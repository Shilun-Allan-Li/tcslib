# Cleanup part 2: static issue inputs, round 1

These are data-only internal issue-preparation inputs at source ancestor `1aa5506f58f77c215e56d24311ec33bd931cacf1`. They are not a fill execution, native check, external dispatch, gate closure, or merge clearance. Current records may advance; the source tree and every local source byte were rechecked against this fixed ancestor.

## File roles and freeze

`owned-files.txt` lists 221 finite existing editable paths: 97 consumer files and 124 provider-only paths. It is not blanket proof ownership. `role-manifest.json` is authoritative: consumer permission is limited to the listed tasks; provider-only paths permit solely new public owner reading lemmas and their formula docstrings, with no existing definition/statement/proof changes. `consumer-files.txt`, `provider-only-files.txt`, `primary-owner-files.txt` and `check-only-files.txt` separate the roles. The 13 explicit shared-provider homes are flagged; four are outside the consumers, giving 101 primary homes. No new module is allowed. All audits paths and root `TCSlib.lean` are immutable worker inputs; the root and Checks aggregates are check-only.

`scope/named-targets.json` identifies exact current A/B/D/F/L/M/N declaration keys and E/K import/prose tasks; its 89 target rows are task annotations and may overlap. Future move/promote names are explicit unimplemented work targets, not available APIs. Existing public helper aliases must remain when deleting a copy would otherwise change an unlisted public algorithm body. Optional G12/G14 operations and G25 seed_to_coins remain excluded even where their files have other mandatory work.

One source-key correction is explicit: F's EncodingMachines zero clause at 572 belongs to `TCSlib.Cryptography.EncodingMachines.CountLoop.orbit_eq`, range 568–575. The original scope-review JSON is copied verbatim; it is not silently rewritten.

`public-definition-freeze.json` contains exact baseline raw source/header/body strings and SHA-256 fingerprints for the three approved public-definition exceptions. PPT.toNUPPT and PPT.ofPolyTime may move unchanged to PPT.lean. NUPPT.ofPolyTime permits reader/proof reexpression while preserving the exact chosen M/Ct/ct witnesses, coins, advice fields, bounds and full-input behavior. The JSON records all eight constructor field RHSs. It does not authorize another chosen machine, algorithm or cost bound. The raw source headers of proposed theorem moves retain their source namespace/variable context; they are not fully elaborated replacement types or preflight proof claims.

## Source graph and orders

The graph covers 1,071 local source modules: all 1,069 TCSlib child sources plus root and Checks. Every live byte matches its Git blob at the ancestor. Source import parsing found no local cycle, missing local import or unsupported source import form. All 450 directly imported external source module names resolve uniquely to installed primary source paths and have bytes/SHA-256 recorded. Directly used mathlib, PFR and batteries Git HEADs match the tracked package pins (`external-package-bindings.json`). No package object freshness or external package replay is claimed.

Every order is independently topologically checked against the recorded graph; none uses a remembered S2/Gate06 count. Files under `orders/` contain source paths without `.lean`, suitable as data for root's serial checker orchestration:

- consumer-owner-order: 97; primary-owner-order: 101; provider-upstream-order: 124; editable-union-order: 221.
- planned-affected-downstream-order: 408, from the 101 planned homes.
- affected-downstream-order: 810, conservatively allowing reader additions at any of the 221 permitted paths; includes facades and affected check-only aggregates.
- affected-prerequisites-order: 242 additional local prerequisites, excluded from that downstream order. Together these give a complete local bootstrap set for the conservative affected scope; sort their union via the graph if combining them into one run.
- root-prerequisites-order: 1,035 local modules, with root excluded.
- checks-prerequisites-order: 422 local modules, with Checks excluded.

`order-manifest.json` records ordered path sets and all direct local prerequisites outside each individual order. Recompute after import changes, approved home relocation, or a changed ownership scope. Future final replay should derive the affected subset from the actual touched paths, while retaining the complete permission/coverage boundary.

`mathlib/` lists direct narrowed Mathlib imports for primary (46), editable (100), affected (226), root (368), Checks (144) scopes and their all-needed union (375). No list contains bare Mathlib. These are source-import boundary lists, not cache commands or a claim all external PFR/toolchain/transitive objects are present. Nonlocal prerequisites remain in local-import-graph.json and require root's normal environment validation.

## Historical rows and admissions

`historical/` and `observations/` are byte-for-byte copies of the immutable original rows, source-disposition tables and 509-key bounded work inventory. No row is filtered, reclassified as repaired, or added to an old count. The separate distAdv_sunglassRed observation is copied separately. The 509 are source work keys, not fresh failures or accepted retirements. Old scope/design prose is data; explicit roles, named targets, exclusions and the issued brief govern permission.

`lexical-admissions-by-source.json`, `lexical-admissions-by-declaration.json`, and `lexical-admission-occurrences.json` retain every baseline token and source location, including private declarations. The library has 510 lexical sorry tokens and one literal sorryAx token; the aggregates have none. All tokens now have a source declaration attribution. The one literal sorryAx at TCSlib/Tactics/Haves.lean:458 is a quoted Lean Name in Haves.analyze's metadata inspection, not an asserted proof or axiom declaration. `admission-baseline-interpretation.json` keeps this distinction and marks kernel/transitive axiom dependencies unmeasured. This static source census does not justify a zero-axiom or proof-completion attestation.

The own preparation helper was AST parsed and run only as Python3-I; it runs read-only Git operations and writes this ignored directory. Its corrected #command boundary prevents Finset cardinality expressions from truncating declaration ranges. A complete static reproduction is retained under static-recheck-r2/ and is not an issue attachment; it changed only lexical attribution outputs, with zero changes to the old 509 owner ranges. No received worker program was executed, and no Lean/cache/app execution or tracked-worktree/main/exchange/Git mutation occurred.

`INPUTS-MANIFEST.json` binds core preparation inputs/outputs and source/code hashes. `DELIVERY-MANIFEST.json` additionally binds these final role lists, named scope targets, dependency bindings and notes; neither embeds its own hash. Root reviews the data and prepares any issued Claude session and exchange staging.

**Not yet clear to merge — static issue preparation only; the user-dispatched cleanup and native verification remain.**
