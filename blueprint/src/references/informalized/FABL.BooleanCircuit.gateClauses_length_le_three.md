<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateClauses_length_le_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for gate clauses

**Claim.** For each gate in a Boolean circuit, the list of clauses associated with that gate has length at most three.

**Proof.** Split according to the gate type. An input gate contributes two clauses, a constant gate one, and a negation gate two. For a conjunction gate, the first two clauses are always present; if its source indices coincide, the final part contributes one clause, and otherwise it contributes one three-literal clause. Thus the total is three in either case. The disjunction case has the same clause-count structure: two fixed clauses and one further clause, whether or not its source indices coincide. Hence every gate contributes at most three clauses.
