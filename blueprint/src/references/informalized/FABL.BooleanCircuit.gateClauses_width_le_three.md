<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateClauses_width_le_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of Gate Clauses

**Claim.** Every clause in the list of clauses associated with a gate has width at most three.

**Proof.** Split according to the gate type. Input and negation gates contribute only two-literal clauses, while constant gates contribute a one-literal clause. For an AND or OR gate, the first two clauses have width two. If both inputs refer to the same earlier gate, the remaining clause also has width two; otherwise it has three distinct literals and width three. Thus every listed clause has width at most three.
