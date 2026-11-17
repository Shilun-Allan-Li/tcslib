<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.decodeOracleTable_rank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ranking and Decoding Oracle Machines

**Claim.** For a well-formed oracle machine with $k$ ordinary work tapes, Boolean alphabet, and state set of size $n$, decoding the code formed from $k$, $n$, and its enumeration index returns that same finite oracle machine, preserving its distinguished states and transition table.

**Proof.** Unpairing the code recovers $k$, $n$, and the machine’s enumeration rank. Since the rank is the image of the given well-formed machine under the equivalence with the finite enumeration, it is below the enumeration’s cardinality. Consequently the decoder uses its ranked-table branch, rather than its default machine. That branch takes the inverse enumeration image of this rank; applying the inverse to the image recovers the original well-formed table. Packaging its underlying machine and proof of well-formedness therefore yields exactly the original finite oracle machine.
