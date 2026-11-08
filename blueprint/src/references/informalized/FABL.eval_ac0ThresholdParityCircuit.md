<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.eval_ac0ThresholdParityCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit evaluation

**Claim.** For $m\ge 7$, the constructed circuit evaluates on $x$ to the product over blocks of the parity signs of the selected two-block restrictions of $x$.

**Proof.** Unfold the circuit evaluation. The length of the first layer is the prescribed number of gates, so the cast used to index the tail can be removed without changing the evaluation (`FABL.circuitTail_eval_cast`, `FABL.length_blockFirstLayer`). The tail has an OR gate at its middle layer and an AND output gate, by the gate duality fact (`FABL.CircuitGate.dual_or`). The middle-layer evaluation lemma identifies this evaluation with the parity CNF applied to the pattern of block parity signs (`FABL.eval_blockMiddleLayer`). The parity CNF represents the full parity function (`FABL.parityCNF_toBooleanFunction`), and the target is that same parity-block product by its application lemma (`FABL.ac0ThresholdParityTarget_apply`). Thus the circuit output equals the stated product.

**Key facts.** `FABL.length_blockFirstLayer`, `FABL.circuitTail_eval_cast`, `FABL.CircuitGate.dual_or`, `FABL.eval_blockMiddleLayer`, `FABL.parityCNF_toBooleanFunction`, `FABL.ac0ThresholdParityTarget_apply`.
