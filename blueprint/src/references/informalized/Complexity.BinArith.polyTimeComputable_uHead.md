<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_uHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Head Transduction

**Claim.** The transduction that starts in the true Boolean state, updates its state by conjunction with each input bit, and emits a $1$ exactly when both the current state and input bit are true is polynomial-time computable.

**Proof.** The state set is the finite Boolean set, the state update is conjunction, and the output rule emits a bit precisely when the state and current input bit are both true. The general finite-state transduction theorem gives polynomial-time computability for this update and output rule (`Complexity.polyTimeComputable_transduce`). Taking the initial state to be true yields the stated function.

**Key facts.** `Complexity.polyTimeComputable_transduce`.
