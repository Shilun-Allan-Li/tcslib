# PRG reduction three-child split — read-only templates, UNRUN

Root selected this owned split before implementation. No repository source, Lean,
build, cache, git or agent operation was performed. Every staged source template is
tactic-free. Helper proofs have explicit placeholders; the four old nonreader bodies
retain their existing sorry tokens until root fills the separately staged candidates.
These templates are not claimed to elaborate or compile.

| Owned module | Exact content | Known assembly with current UNRUN bodies |
|---|---|---:|
| Reductions/PRG/Defs.lean | All33 old definitions/abbrevs/structure/instances/readers verbatim | 287 lines |
| Reductions/PRG/Encoding.lean | Exactly three old encoding theorems with old headers/docs | 160 lines |
| Reductions/PRG/Hop.lean | Four proposed helper theorems, then the old prg_hop header/docs | 343 lines |
| Reductions/PRG.lean | Import-only facade importing all three children | 31 lines |

These are exact text estimates including staged module docs and known proof candidates,
not final checked source sizes. All substantive children fall within the requested
150–600 planning range, with343 or more lines of proof growth headroom for Hop.
The unsplit known assembly would already be721 lines before the new split wrappers.

## Exact old move boundaries

Source: TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG.lean,
SHA-256 fd12333000f4fb356251f578b0369e1beed8cc6d6dae2673c5dfa730a2d8687b.
It is byte-identical to the historical M0 source inventory binding for this owner.

- Defs receives original lines51–297 inclusive, starting at PRGChal's full docstring.
  It retains the nested namespace PRGAdvice block, the Data/prodEquiv readers, both
  named data-valued Fintype/Inhabited instances and their complete equality readers,
  all encoders/majorants, preprocessing, reduction and PRGRealizable/readers verbatim.
- Encoding receives lines299–324 inclusive, exactly prgEnc_injective,
  encPRGAdvice_injective and encPRGAdvice_length_le, with all old docs and full headers.
- Hop receives lines326–343 inclusive, exactly prg_hop with its full old docs/header.
- The facade keeps no declaration or alias. It imports Defs, Encoding and Hop.

Each child explicitly reopens the ORIGINAL area namespace; Defs and Encoding then
open Params. File paths do not become namespaces. In Hop the four new helper headers
already spell theorem Params.NAME, so they stay directly under the area namespace;
only the old prg_hop block is wrapped in namespace Params. Do not add an extra Params
around the qualified new helper names. There is no namespace Reductions.PRG.Encoding.
The base area's Encoding.Modular name therefore keeps its existing resolution.

## Exact M0 fullname/header/doc move ledger

existing-declaration-move-map.json is directly compatible with freeze_global.py --moves:
each of37 rows has name, old_file and new_file, with additional source range,
header/prose/full-docstring/command hashes. The TSV is the human-readable equivalent.
It binds all37 historical M0 named declarations:33 to Defs,3 to Encoding,1 to Hop.
The M0 global ledger is evidence/checks/m3-final/global-freeze/frozen-global-map.json,
freeze d10a560b34d58919bc1a5206ce66a444613f94c7. Its current companion and source hashes
were checked by text before planning; no git operation was needed or performed.

The same reviewed pure parsers used by the global freeze tool were loaded via AST
selection, without running any CLI/Git loop. On these virtual templates they agree:
all37 old full names, kinds, normalized headers and statement-prose prefixes are
unchanged; no old name is globally removed; the only four added names are the helper
headers explicitly recorded in new-helper-placement.json. Exact old source chunks,
including complete old docstrings and definitions/readers, are included verbatim.
This lexical result is in lexical-template-audit.json; it is not a new kernel census
of generated structure projections/constructors/recursors or a compiled-type check.

When root implements, pass this ledger together with the existing M3 relocation ledger
and the LPN split ledger to a fresh global guard. Per-file removal/addition rows remain
visible and reconcile exactly to the explicit moves; none should be suppressed as a
header exception. The three new implementation paths also need owner/import-order,
source inventory, seal and final package coverage; the old facade remains in inventory.

## New theorem placement and fill order

Hop's four helper placeholders point to the corrected M4PRGPrepared packet:

1. Params.sdCore_publicSeed: candidate01.
2. Params.prg_verdict_prob: candidate04.
3. Params.prg_nuisance_average: preferred TYPED candidate05, not the older alternative.
4. Params.prg_chain_accept_average: candidate06.
5. Fill the old prg_hop body from candidate07.

The helper names are not renamed or re-exported. They are proposed new theorem-only
headers, not M0 frozen declarations or new algorithm/encoding/machine definitions.
All remain UNRUN. Preserve each old statement/doc header while filling the old body.
Encoding's bodies are the full M4AdviceEncoding candidates04,05,06, in that order.
No dependency on the three injection/length theorems occurs in the staged hop helpers;
Hop therefore imports Defs alone, while the facade exposes every child to Targets.

## Imports and cycle audit

The proposed direct imports are exactly:

- Facade -> Defs, Encoding, Hop.
- Defs -> the original Hybrids and Asymptotic.Realization imports.
- Encoding -> Defs.
- Hop -> Defs.

The synthetic source graph is acyclic from the facade, Security, Targets and the area
facade. Relative to the existing source closure it adds exactly the three owned nodes,
loses no module, adds no external TCSlib or Mathlib module, and has no upstream return
edge into the reduction facade/Security/Targets. import-cycle-audit.json records the
precise nodes and counts. Lean/Core imports are terminal leaves in this static audit.
No BPPBridge, BinaryArith, new sampler root, blanket Mathlib root or direct import of a
forbidden module is proposed. The shared raw Boolean primitive is StructuredSeed.BoolPRG;
it must not be confused with the Reductions/PRG facade or these owned child paths.

## Preparation corrections and limits

The initial Defs range accidentally included the old namespace Params line as well as
the new wrapper; the reviewed parser caught the resulting namespace duplication. The
range was corrected to51–297 before delivery. A draft helper-name regex matched a prose
occurrence of the word theorem; it now anchors to the actual command. The final parser
result above supersedes those invalid drafts and makes no search absence claim.

The first graph draft used a nonnested comment regex, which exposed quoted imports in
Mathlib documentation and reported a spurious cycle. It was replaced with the reviewed
clash parser's nested-comment/string stripper. Only the corrected graph supports the
acyclic/no-external-root conclusion. No Lean probe was run on any draft.

Global frozen statement identity, actual proof correctness, finalized module line counts,
axiom census and final opacity seals still require root's fresh post-implementation gates.
