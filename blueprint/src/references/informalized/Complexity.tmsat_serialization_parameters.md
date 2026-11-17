<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_serialization_parameters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization Parameter Bounds

**Claim.** For a machine in code normal form, the binary representation of its state-count parameter, its initial-state index, and its number of states are each bounded by the canonical serialization length.

**Proof.** For each state, let its table block be the concatenation of the action encodings for all input-symbol and work-symbol possibilities. Each such block has length at least one, by `tmsat_action_nonempty`; consequently, `tmsat_flatMap_length` bounds the total table length below by the number of states, namely $m+1$. The pair-encoding length formula `universal_pair_length` expresses the whole serialization length as twice the binary-representation length of $m$, plus two delimiter bits, plus the unary initial-state field and table. The unary field has length $q_0+1$, and the table has length at least $m+1$. Comparing these nonnegative contributions with the total length gives all three stated bounds.

**Key facts.** `Complexity.tmsat_action_nonempty`, `Complexity.tmsat_flatMap_length`, `Turing.universal_pair_length`.
