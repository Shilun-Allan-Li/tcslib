<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.polyTimeComputable_isValid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Encoding Validity

**Claim.** The function that maps each bit string $w$ to the one-bit string containing its validity indicator is computable in polynomial time.

**Proof.** First, circuit evaluation with target value false is polynomial-time computable: on an input $z$ it returns the one-bit verdict in time $12(|z|+1)^2$ (`evalTM_computes`). The construction also uses polynomial-time transductions to produce the repeated-true and repeated-false strings of length $|w|$, and the transformation that swaps gate kinds. Pairing these strings with the identity input and applying the evaluator gives two polynomial-time verdict computations: one evaluates $w$ paired with $|w|$ true bits, and the other evaluates the gate-kind-swapped input paired with $|w|$ false bits. Polynomial-time computability is preserved under pairing, composition, and concatenation (`pairEncode`, `comp`, `append`); the finite-state transductions are polynomial-time computable (`polyTimeComputable_transduce`), and the identity is polynomial-time computable (`polyTimeComputable_id`). The proof combines the two verdict bits with a fixed equality test: its linear-time implementation is supplied by `computesFunInTime_ifEq`, and hence it is polynomial-time computable (`polyTimeComputable_of_linear`). Finally, the validity characterization says that the validity indicator is the disjunction of those two verdicts (`isValid_eq_verdict`). Thus the composed construction outputs exactly the required one-bit indicator and is polynomial-time computable.

**Key facts.** `BoolCircuit.CircuitEval.evalTM_computes`, `Complexity.polyTimeComputable_transduce`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.append`, `BoolCircuit.CktSatReduction.isValid_eq_verdict`.
