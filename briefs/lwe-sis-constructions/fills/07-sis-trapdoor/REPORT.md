# SIS encoding and finite trapdoor proof fill

This wave fills 40 audited obligations in nine modules. It starts at the
Gate 11 intake `259ff8a13ba08034a15ab7c8464d5ad4a122d6fd` and gives checked
Lean source `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800` on draft #250.
Across the four proof waves, 83 obligations are proved and 18 remain admitted.
The statement freeze is `17b2a282b545c6ebca3fccc88d518d18ae78f485`.

| Module | Filled | Result |
|---|---:|---|
| `Encoding.BooleanVector` | 5 | Step equations and efficiency, raw length, and canonical modular expansion |
| `Encoding.DyadicLinearAlgebra` | 10 | Dot leaf efficiency, step envelopes, loop widths, and canonical dot and matrix products |
| `Hashing.SIS.CollisionOutput` | 7 | Signed postprocessor width, leaf efficiency, exact raw encoding, parsing, and the same-seed SIS bound |
| `Hashing.SIS.Implementation` | 2 | Raw hash width and canonical-matrix evaluation with padded domain bits |
| `TrapdoorFunctions.Lossy.Gadget` | 4 | Additive integer encoding, signed rounding, and digit injectivity |
| `TrapdoorFunctions.Lossy.Matrix` | 4 | Secret cancellation, error bound, finite image cardinality, and the supplied bit-loss budget |
| `TrapdoorFunctions.Lossy.Experiments` | 4 | Actual column law, neighboring DLWE gap, telescoping, and two fixed shifts |
| `TrapdoorFunctions.AllButOne.AntiCyclic` | 2 | Subtraction and the signed branch-message bound |
| `TrapdoorFunctions.AllButOne.Basic` | 2 | Designated-branch cancellation and its image bound |

The loop proofs read `forLoop_pairEncode` and use induction on its iteration
count. The leaf machine proofs compose existing projection, bit, scalar and
pairing contracts. On canonical inputs, modular addition and multiplication
write the current residue at each step. The signed SIS output uses the raw
head/default positions, public padding and split equations, and the existing
signed decoder. The collision bound transports the same matrix and finder coins.

The concealer proof groups independent real and uniform seeds by column and
uses `OneWay.uprob_update` for the single challenge insertion. The public
matrix and test coins are preserved. Exact dyadic rounding uses signed integer
division and removes the quotient's multiple of the small modulus on casting
back. The image argument enumerates a finite interval for each error coordinate.
These are conditional algebraic and finite probability results.

The source comparison preserves all 220 ordered declarations, definition
bodies, signatures, options, and attributes. The only added import is the
existing `OneWayFunctions.Basic` module for `uprob_update`. The seven-facade
closure remains 144 modules. The other 144 frozen paths match the baseline
byte for byte. Separate imported-environment probes compare the exact universe
parameters and type representations of all 220 declarations.

| Evidence | Result |
|---|---|
| Fresh serial sweep | 144 modules, 382.262 seconds, zero errors |
| Admissions | 18 owned, 17 inherited |
| Axiom probe | 64.262 seconds, 220 source and 88 backing prints |
| Owned inventory | 609 constants, 16 new compiler auxiliaries, zero origin changes |
| Scoped style | Zero failures and two inherited warnings over 41 files |

All 40 fills use only standard axioms. The 18 admitted declarations are
exactly the owned constants that use `sorryAx`. Other native warnings match
the preceding gate. The fresh checks use the branch's own pinned packages and
empty olean tree. The type baseline uses this chat's preserved Gate 11 objects.
Development snapshots and receipts are separate from the final sweep. Native
coverage is the seven facades and probes.

Nine remaining admissions depend on the counted-loop efficiency route. Seven
use the pending positional block reader directly or through gadget inversion.
Two are the anti-cyclic rank proof and its branch specialization. The rank
proof's pinned cyclotomic import is currently absent from the isolated cache.
The shared reader and counted-loop registry and head-envelope decisions remain
in the earlier coordination records. [PW10 source preflight](PW10-SOURCE-PREFLIGHT.md)

**Not yet clear to merge.** The 40 fills await proof audit. The 18 other
obligations, scoped source ingestion and matching, and landing checks remain.
