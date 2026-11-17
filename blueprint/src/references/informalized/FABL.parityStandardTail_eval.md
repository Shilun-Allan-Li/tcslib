<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityStandardTail_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the parity circuit tail

**Claim.** The parity circuit tail with parameters $r$, $q$, and output gate $g$, evaluated on the specified layer values arising from the parity tree, returns the parity-tree value at depth $t+q+1$ at the root.

**Proof.** Proceed by induction on $q$, allowing both the starting tree depth $t$ and the gate $g$ to vary. For $q=0$, the standard tail is just its output gate connected to the designated output inputs. The output-input evaluation fact (FABL.eval_parityOutputInputs) identifies that evaluation with the product of the actual block assignment, which is precisely the parity-tree value one level above depth $t$ at the root. For the successor case, write the tail as its first layer followed by the standard tail at parameter $q$, with the gate dualized. The cast-evaluation identity (FABL.circuitTail_eval_cast) expresses evaluation of this tail as evaluation of the remainder on the values produced by the first layer. The next-layer evaluation fact (FABL.eval_parityNextLayer) identifies those values with the layer values at parameter $q$ for the dual gate, using the actual assignments one tree level deeper. The tree-assignment identity (FABL.parityNextActualAssignment_tree) supplies exactly this shift from depth $t$ to depth $t+1$. The two successive gate dualizations cancel (FABL.CircuitGate.dual_dual), and the induction hypothesis applied at depth $t+1$ and gate $g$ now gives the desired tree value. The exponents agree by associativity of natural-number addition.

**Key facts.** `FABL.eval_parityOutputInputs`, `FABL.circuitTail_eval_cast`, `FABL.eval_parityNextLayer`, `FABL.parityNextActualAssignment_tree`, `FABL.CircuitGate.dual_dual`.
