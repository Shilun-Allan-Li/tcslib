# LPN four-child split — complete templates, static only

Five complete `.lean.template` files are ready for root's mechanical move after
M3 publication. They contain all42 existing named declarations, including every
original definition, instance, reader, full docstring and the four unchanged
original sorry stubs. No new proof, theorem, definition, assumption, algorithm,
import root or attribute is inserted. There are zero tactic blocks in source
code. The pure temp producers ran only static parsing/byte comparisons and exact
import-following audits; no Lean, Lake, Git, cache, source edit or agent ran.

The source is the428-line Reductions/LPN.lean at root's04249b8 checkpoint, SHA-256
`e7c468cbe10b2744e507a63c48da4029a2f51fcf13ce34fb8a8793b89a7e08bd`.
The earlier LPNModularity planning packet is preserved. These templates use its
exact command boundaries; the new child references use the full bibliography
already present in the old owner. The facade's original module prose is retained
verbatim, followed by its explicit four-child Contents.

| Template | Destination below StructuredSeed/ | Existing names | Lines / max width |
| --- | --- | ---: | ---: |
| Defs.lean.template | Reductions/LPN/Defs.lean | 38 | 372 /100 |
| Encoding.lean.template | Reductions/LPN/Encoding.lean | 3 | 64 /93 |
| Transport.lean.template | Reductions/LPN/Transport.lean | 0 | 40 /95 |
| Hop.lean.template | Reductions/LPN/Hop.lean | 1 | 65 /97 |
| Facade.lean.template | Reductions/LPN.lean | 0 | 53 /95 |

Transport is deliberately a valid empty module, ready for the specialized
01–04 helper additions. Hop has an empty area-Internal insertion region, followed
by the exact original Params.lpn_hop stub. No invalid placeholder expression or
new sorried helper is introduced. Root can land/check the mechanical move before
adding each new helper/proof one at a time. new-helper-placement.tsv carries the
original future helper order/names, but no candidate body is copied here.

Defs receives original49–361 and408–424; Encoding363–386; Hop388–406. Every
attached declaration docstring, current header and complete body/stub is found
byte-identically exactly once in its destination. Both reviewed pure parsers
agree on the exact42 full names, without duplicates/additions/removals. All42
normalized headers and pre-sketch statement-prose hashes equal the M0 frozen map.
There is no path-derived namespace, export alias, wrapper or renamed structure.
Generated fields/constructors/recursors still require root's later full kernel
census; this static source check does not claim to have run it.

## Move ledger and freeze guard

existing-declaration-move-map.json is a plain42-row list compatible with
freeze_global.py (`name`, `old_file`, `new_file`, plus byte/hash provenance).
The TSV carries the same rows. Root must supply this ledger **alongside** the
existing Claim42 ledger and the separate PRG ledger; never discard per-file
REMOVED/ADDED rows as harmless without exact reconciliation. With the approved
PRG37 and prior Claim4214 moves, the combined named move count is93. Root's global
670-header/prose guard and typed kernel comparison remain authoritative after
actual application. Nothing here runs that Git-dependent guard.

The template-current-global-map.json records proposed locations/kinds/headers/
prose for the42 moved names. template-validation.json binds source/template/parser
checks and all file hashes. Full command/doc hashes include complete original
proofs/readers/stubs; only separator newlines are excluded from command digests.
The actual copied ranges retain the original body bytes.

## Import graph and application order

- LPN facade imports Defs, Encoding, Transport and Hop explicitly.
- Defs retains the original Hybrids then Asymptotic.Realization imports.
- Encoding imports Defs and the existing Basic owner.
- Transport imports Defs; Hop imports Transport.
- No child imports its facade, Security or Targets. The raw StructuredSeed.LPN
  assumption module remains distinct from the Reductions.LPN facade.

import-cycle-audit.json follows exact TCSlib import paths and treats external
Lean/Mathlib/package imports as roots. It verifies acyclicity from the LPN facade,
Security, Targets and StructuredSeed, both for this split alone and for the
combined existing PRG three-child overlay. The exact closure gains only four
owned LPN nodes, or seven combined owned nodes. No old module disappears and no
external/direct Mathlib cache-root set changes. No broad scan or Mathlib recursion
was used. This is static source-graph evidence, not a compilation pass.

After copying, root should compile Defs, Encoding, Transport, Hop and the facade
serially, then refresh all affected downstream owners and full source/kernel/
reader/canonical-seal coverage. Applying both splits makes33 owners at this
mechanical stage, before any further justified split. Inventory generation must
remain dynamic: even the initially empty Transport owner and the compatibility
facades belong in the exact collector/build/seal matrix. Definitions/readers now
belong to Defs for control purposes; the old empty facade is not their owner.

The final allowances remain those in the original plan: Defs≈380, Encoding300–500,
Transport220–400 and Hop400–600, with every file≤1000 and width≤100. If later actual
proof growth warrants Sections, use a separately ledgered coherent split rather
than modifying frozen statements or silently narrowing coverage.
