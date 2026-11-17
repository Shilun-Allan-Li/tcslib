<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStageSlot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Slot Within a Zone

**Claim.** For $i<\ell$ and $p<C_i$, the slot at position $B_i+p$ is exactly the $p$th entry of the list assigned to index $i$, with an out-of-range entry interpreted as absent.

**Proof.** The zone-index characterization says that an index equals $i$ exactly on the interval from $B_i$ through, but not including, $B_{i+1}$ (`zoneIndex_eq_iff`). The base recurrence gives $B_{i+1}=B_i+C_i$ (`zoneBase_succ`). Since $p<C_i$, the position $B_i+p$ lies in this interval, so its zone index is $i$. Its within-zone offset is $(B_i+p)-B_i=p$. Substituting these into the slot definition gives the stated list entry, including the absent value when $p$ is beyond the list's length.

**Key facts.** `Turing.zoneIndex_eq_iff`, `Turing.zoneBase_succ`.
