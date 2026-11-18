# LPN reduction split plan — read-only, NOT_RUN

Recommend four owned children under the EXISTING Reductions/LPN facade:

| Module | Exact content | Current text estimate | Final planning allowance |
|---|---|---:|---:|
| `Reductions/LPN/Defs.lean` | All existing definitions/abbrevs/instances/readers, plus LPNRealizable/readers | 372 | about 380 |
| `Reductions/LPN/Encoding.lean` | Three existing challenge/advice encoding theorems and specific advice accounting helpers | 117, PARTIAL | 300–500 |
| `Reductions/LPN/Transport.lean` | LPNHopFinal 01–04: verdict/coin, canonical uniform/real coordinates | 196 | 220–400 |
| `Reductions/LPN/Hop.lean` | LPNHopFinal 05–09 and the existing Params.lpn_hop statement/body | 386 | 400–600 |
| `Reductions/LPN.lean` | Import-only facade with Contents and references | 32 | about 35 |

The final allowances are planning ranges, NOT counts of completed checked proofs.
Two old advice candidates still contain explicit gaps; the cast and actual-law
averaging candidates remain untested. Exact current assembly counts, including
module wrappers and source docstrings, are in line-budget.json. Eight known local
have repairs add three lines in Transport and five in Hop. Proper theorem docstrings
and elaboration-driven proof growth need the remaining allowance.

## Exact move boundaries

Use current 428-line source hash in move-boundaries.json. Ranges include the
ORIGINAL declaration docstrings and end only between complete commands:

- Defs receives original lines 49–361 inclusive, then 408–424 inclusive. The latter
  moves LPNRealizable AND LPNRealizable_iff beside the reduction definitions. It
  depends only on lpnEnc/lpnRed/advice, never on lpn_hop or its proof. No reader is
  separated from its definition or data-valued instance.
- Encoding receives original lines 363–386 inclusive: lpnEnc_injective,
  encLPNAdvice_injective, encLPNAdvice_length_le. Keep each existing full header and
  docstring unchanged; only the proof body is filled. Reuse the now-owned Basic
  fixed-width list helpers and existing modular encoder APIs. No private generic
  list-code infrastructure or alternative encoding belongs here.
- Hop receives original lines 388–406 inclusive for Params.lpn_hop, after the new
  area-Internal support lemmas. Only its proof body changes. The quantifier order,
  every-realizer premise, own canonical challenge encoding and sentinel guard stay
  exactly as frozen.
- Transport receives new helper candidates 01–04, all under
  TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal.
- Hop first receives new helper candidates 05–09 in that SAME area Internal
  namespace; close Internal and reopen Params for the original lpn_hop command.
  new-helper-placement.tsv records all names and proof dependencies.
- The original LPN.lean keeps no duplicated declarations. It imports every child
  and is the compatibility facade. Existing Security/StructuredSeed imports need
  no change and expose exactly the same public full names.

There are 42 existing top-level declarations. declarations.json/tsv records each
original full name, old range, target module, exact header hash and whole-command
hash. All 38 definition/reader/instance commands move verbatim to Defs; the other
four are the existing nonreader statements, whose frozen headers move with them.
The current file has no explicit private declarations, section variables, local
attributes or notation commands that could silently change headers on relocation.
Keep the original area namespace, options, open Complexity Turing, and BigOperators
scope in each child. The file path does NOT become a namespace. Do not add export
aliases, wrapper defs, renamed structures, eta-expanded readers or a second encoding.

## Imports and cycle audit

The proposed direct imports are:

    LPN facade -> LPN.Defs, LPN.Encoding, LPN.Transport, LPN.Hop
    LPN.Defs -> StructuredSeed.Hybrids, Asymptotic.Realization
    LPN.Encoding -> LPN.Defs, StructuredSeed.Basic
    LPN.Transport -> LPN.Defs
    LPN.Hop -> LPN.Transport

Defs intentionally retains BOTH original external imports, in their original
order. Hybrids is required by the frozen lpnPre/publicSeed interface; narrowing it
would require moving a different owner's definition and is outside this split.
Basic is already transitive in the old closure, and its explicit Encoding import
names the actual fixed-width owner. No new external TCSlib or Mathlib root is needed.

The fresh comment/string-aware source-graph audit overlays these four children and
replaces the old LPN owner by the facade. It verifies acyclicity from LPN, Security,
Targets and the StructuredSeed facade. New closure minus old closure is EXACTLY
these four new owned module nodes; no old module is lost. Neither Defs upstream
root imports the reduction facade, Security or Targets. Details are in
import-cycle-audit.json. This is static graph evidence, not a Lean check.

Important path distinctions prevent accidental cycles:

- StructuredSeed.LPN is the existing RAW assumption owner. It is distinct from
  StructuredSeed.Reductions.LPN, the reduction facade.
- StructuredSeed.Encoding is the existing honest encoding owner. It is distinct
  from StructuredSeed.Reductions.LPN.Encoding, the new reduction-code proof owner.
- A child NEVER imports Reductions.LPN, Security or Targets. Use the exact headers
  staged as tactic-free *.header.lean.txt fragments, rather than copying a scratch
  proof's old import of the complete owner.

The mathematical DAG is also one-way: 02 uses01; 07 uses04/05; 08 uses03/06;
09 uses07/08; public lpn_hop uses09/02. Transport cannot depend on Hop. Encoding
injectivity/length is not a premise of Transport, the actual-law averaging or
lpn_hop; it is used later for target-to-machine assembly. Keeping Encoding off the
hop proof import path separates the M6 accounting from the security mathematics.

## Why split before implementation

The old warning's approximate packet count was stale: CURRENT LPNHopFinal 01–10
contains 472 lines. Unsplit insertion of 01–09, replacement of lpn_hop, and the
three old encoding candidates gives 949 lines. The eight confirmed local-have
repairs make 957 BEFORE proper helper docstrings, namespace switches, complete
advice accounting and cast/Fubini repairs. Thus the file is already approaching
1000 with intentionally incomplete M6 bodies; relying on aggressive inlining is
fragile. This split follows policy section 1's coherent clusters and separation
of definitions from heavyweight theorems without changing the frozen algorithms.
The old suggestion to inline uniform/word bridges is unnecessary after the split;
keeping the named theorem-only bridges supports isolated checking and reuse.

## Fallback if the actual-law proof grows

If Hop approaches 550 before its averaging proof closes, add ONE further owned
LPN/Sections.lean and move candidates05–08 together into it. Sections imports only
LPN.Transport; Hop then imports only LPN.Sections. This removes 172 candidate lines
from Hop, giving roughly 220–240 lines for Sections and 215–235 for Hop before
further growth. Existing public names/headers remain unchanged because their area
Internal namespace stays the same. This is a clean preplanned boundary, not a
reason to manufacture a generic averaging theorem or change the source law.

## Landing/coverage consequences for root

This is a mechanical owned-file organization change, not a new mathematical
construction or a changed binding statement. No new algorithm, sampler, machine,
finite enumeration, efficiency claim or assumption is introduced. Before filling
bodies, root should relocate complete commands, compile the children in dependency
order, and compare the 42 existing full names/types and data readers to the frozen
manifest. A module-origin/owner metadata change is expected; a public API change is
not. No Lean, build, cache, git or source mutation was performed here.

The existing StructuredSeed facade already imports Reductions.LPN and remains
reachable from TCSlib.lean. The revised reduction facade explicitly imports every
child and carries one Contents entry per child. New files still need the campaign's
owner inventory, collector order, declaration census, opacity/control/seal coverage
and final axiom checks. Retarget the relocated definition/readers to Defs rather
than leaving coverage assigned only to an now-empty declaration facade. Preserve
M0 frozen-header baselines by full name and header hash; do not treat file movement
as permission to alter any definition or theorem statement.

The header fragments are tactic-free and are NOT assembled source modules. All
proofs remain in their existing temporary packets; no multiple-proof source file
was emitted by this planning task. SHA256SUMS records the plan artifacts.
