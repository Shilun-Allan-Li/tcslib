<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Evaluation and Rewind

**Claim.** On the doubled serialization of a literal, the evaluator updates the clause accumulator according to whether the certificate bit at index $v$ equals the literal's Boolean value, then returns to the start of the literal in phase $1$ with the certificate head reset to zero, in exactly $3v+8$ steps.

**Proof.** Decompose the doubled literal encoding into the doubled unary prefix for index $v$, the doubled delimiter, and the doubled sign bit. First, the two-step rule (`Complexity.satEval_double`) consumes the initial pair and enters phase $2$. The unary-index result (`Complexity.satEval_index`) consumes the next $v$ doubled true bits, advancing the input by $2v$ and the certificate head from zero to $v$. Another application of the two-step rule consumes the delimiter and enters phase $3$. At certificate offset $v$, the buffer lookup agrees with the assignment bit: the natural-offset buffer identity (`Turing.FinTM.bufferTape_nat`) and the canonical last-tape symbol rule (`Complexity.satEvalCfg_work`) identify it as $u_v$. The evaluator's phase-$3$ transition therefore updates the clause accumulator to $c\vee(u_v=b)$; the two-step rule records this update and enters phase $4$.

The rewind result (`Complexity.satEval_rewind`) moves the certificate head back to zero and returns to phase $1$, without changing the input position. Concatenating these runs with the run concatenation law (`Turing.MultiTapeTM.runFrom_add`) gives the exact total $2+2v+2+2+(v+2)=3v+8$. The pieces of the serialization have total length $2(v+3)$, so the final input position is the stated endpoint.

**Key facts.** `Complexity.satEval_double`, `Complexity.satEval_index`, `Turing.FinTM.bufferTape_nat`, `Complexity.satEvalCfg_work`, `Complexity.satEval_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.satBits_length`.
