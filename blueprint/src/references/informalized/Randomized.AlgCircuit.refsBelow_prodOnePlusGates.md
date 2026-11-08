<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.refsBelow_prodOnePlusGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Earlier References in the Product Circuit

**Claim.** For every gate position in the constructed list $G_k$, the gate is an input variable or the constant $1$, or its two references are both earlier than that position.

**Proof.** Induct on $k$. At $k=0$, the list consists only of the constant gate, so the assertion holds. At the successor stage, the old gates occupy the prefix of the new list, and any position in that prefix retains its gate and index; the induction hypothesis applies. The new list has length $3k+4$, as follows from the length formula (`Randomized.AlgCircuit.length_prodOnePlusGates`). Its appended gates occupy positions $3k+1$, $3k+2$, and $3k+3$: the first is a variable or constant and so has no references, while the addition references positions $0$ and $3k+1$, and the multiplication references $3k$ and $3k+2$. In each case the references are strictly below the gate's position.

**Key facts.** `Randomized.AlgCircuit.length_prodOnePlusGates`.
