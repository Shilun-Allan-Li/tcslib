<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_code_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries after the clock prefix

**Claim.** For all finite Boolean words $bs,\alpha,x$ and every $j\in\mathbb N$, the entry at index $4|bs|+4+j$ of $\langle\langle bs,\alpha\rangle,x\rangle$ equals the entry at index $j$ of $\langle\alpha,x\rangle$, with out-of-range entries absent.

**Proof.** The input-layout identity writes the nested encoding as the clock prefix for $bs$ followed by $\langle\alpha,x\rangle$ (`timed_input_layout`). The prefix has length $4|bs|+4$ (`timedClockPrefix_length`). For an index at or beyond the length of a list prefix, the optional entry in the concatenation is the entry in the second list at the index reduced by the prefix length. Applying this concatenation-index rule gives the claimed equality, including the case where the entry in the second list is out of range.

**Key facts.** `Turing.timed_input_layout`, `Turing.timedClockPrefix_length`.
