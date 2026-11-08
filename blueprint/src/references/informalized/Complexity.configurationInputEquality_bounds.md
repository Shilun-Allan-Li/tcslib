<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationInputEquality_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Equality Formula Bounds

**Claim.** The input-equality CNF has at most $2C(s+n+1)$ variables, and its binary serialization has length at most $6n(2C(s+n+1)+3)+1$.

**Proof.** The coefficient hypothesis bounds every wire used by the input-equality formula strictly below $2C(s+n+1)$ (`codecPairWire_lt`). The general variable-count bound for a relabelled CNF therefore gives the claimed number of variables (`codecCnf_numVars`). The general serialization bound gives a length of at most the CNF cost times the wire bound plus three, with one final delimiter (`codecCnf_serialize`). The input-equality formula has cost at most $6n$ (`codecInputEquality_cost`); substituting this cost and the wire bound yields the stated serialization estimate.

**Key facts.** `Complexity.codecPairWire_lt`, `Complexity.codecCnf_numVars`, `Complexity.codecCnf_serialize`, `Complexity.codecInputEquality_cost`.
