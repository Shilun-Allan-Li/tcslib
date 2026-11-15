# Scope request: circuit fan-in reader

Request (verbatim):

The brief’s Scope section requires your approval for frozen-file edits. B2 needs the distinct-argument and fan-in facts in `DAGCircuit.IsFaninTwo`, but I found no public reader at the pinned base. May I add the single `isFaninTwo_iff` reader shown in `/private/tmp/sc-garble-runtime/fanin-reader.patch` to `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean`? It exposes the existing definition without changing it. I’ll continue the independent encryption proofs while this is pending.

Seyoon’s answer (verbatim, 2026-11-15):

Approve the reader addition

The exact approved diff is `fanin-reader.patch`.
