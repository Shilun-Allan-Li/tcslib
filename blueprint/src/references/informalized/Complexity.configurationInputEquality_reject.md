<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationInputEquality_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Inequality Rejects Paired Codes

**Claim.** For distinct Boolean strings $x,y$ of length $n$, the input-equality CNF evaluates to false on the concatenated configuration codes, with out-of-range variables assigned false.

**Proof.** Assume for contradiction that the formula evaluates to true. Relabeling the clauses and evaluating each variable at its position in the concatenated codes identifies this assignment with the paired bits of the two configuration rows; the bound on $C$ ensures those positions are represented correctly (`configurationCodec_pair_get`). The input-equality formula evaluates to true on a pair of rows exactly when their input fields agree (`codecInputEquality_eval`). The rows here come from $x$ and $y$, so equality of their input fields implies $x=y$ (`codecRowOf_input_eq`), contradicting the hypothesis that they are distinct. Thus the formula evaluates to false.

**Key facts.** `Complexity.configurationCodec_pair_get`, `Complexity.codecInputEquality_eval`, `Complexity.codecRowOf_input_eq`.
