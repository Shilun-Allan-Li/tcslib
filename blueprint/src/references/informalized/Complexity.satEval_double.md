<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consuming a Doubled Input Bit

**Claim.** When the evaluator's transition on the first copy of a doubled input bit makes the stated administrative move, two steps reach the next canonical configuration with the updated phase and certificate-head offset.

**Proof.** The canonical input-symbol rule (`Complexity.satEvalCfg_input`) identifies the bit read at offset $i$ with the assumed bit $b$. Thus the assumed transition is the evaluator's actual first step. The canonical-action calculation (`Complexity.satEvalAction_apply`), together with the positive input-head movement rule (`Turing.moveInputPos_pos_of_ne_right`), shows that this step advances the input offset by one and the certificate-head offset from $j$ to $j'$, entering the specified phase with the skip flag set. The skip-phase transition (`Complexity.satEval_skip`) advances one more input position without changing the certificate head or truth bits, and clears the skip flag. These two steps give the claimed canonical configuration at offset $i+2$.

**Key facts.** `Complexity.satEvalCfg_input`, `Complexity.satEvalAction_apply`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.satEval_skip`.
