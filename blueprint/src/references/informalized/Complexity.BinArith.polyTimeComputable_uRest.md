<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_uRest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Rest Transduction

**Claim.** The transduction that starts in the false Boolean state, updates its state by disjoining it with the negation of each input bit, and emits the current input bit exactly when the state is true is polynomial-time computable.

**Proof.** The state set is the finite Boolean set. Use the update that disjoins the current state with the negation of the input bit, and the output rule that emits the input bit when the state is true and emits nothing otherwise. The general finite-state transduction theorem guarantees polynomial-time computability (`Complexity.polyTimeComputable_transduce`); choosing false as the initial state gives the claimed transduction.

**Key facts.** `Complexity.polyTimeComputable_transduce`.
