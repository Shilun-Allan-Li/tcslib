<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.countP_isOp_prodOnePlusGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operation count in the generated gate list

**Claim.** For every natural number $n$ and every natural number $k$, the gate list constructed for $k$ factors contains exactly $2k$ arithmetic operation gates, counting addition, subtraction, and multiplication gates.

**Proof.** Proceed by induction on $k$. With zero factors, the list consists only of the constant gate, which is not an operation gate, so the count is $0=2\cdot 0$. For the successor step, the construction appends a variable-or-constant gate, an addition gate, and a multiplication gate. The first is not an operation gate in either case, while the addition and multiplication each contribute one. Thus the count increases by two; from the induction hypothesis it is $2k+2=2(k+1)$.
