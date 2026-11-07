Creates the Mathlib-only NatBits module and repoints the approved binary-length, logarithmic and
power bounds across 22 Lean files. Six source declarations move with names/statements preserved;
the approved namespace move, redundant public/private deletions and three additions follow D1–D9.
The shared Frag repair is identical to #215.

The new module has 144 lines, 10 public source theorems, no private source declarations, and
**16 compiled constants including six moved internal proof auxiliaries**. All 16 receive
axiom checks. Changed-module non-private census 2,377 → 2,374, with all auxiliaries retained
in the comparison; source census 2,366 → 2,360. Surviving statements/visibility/order stay frozen.

Validation: independent 344-module merged-tree replay, 0 failures/static mismatches; module and
six changed-consumer axiom checks use only standard axioms. Seven boundary probes and the Frag
cell-step seal pass. Full 22-file screen, freeze, lint and blueprint checks are under
`campaign/gates/114-natbits-dedup/evidence/current/`. D9 families remain record-only as ruled.

**Not yet clear to merge:** external Codex gate 114 remains open. Seyoon merges after it closes.
