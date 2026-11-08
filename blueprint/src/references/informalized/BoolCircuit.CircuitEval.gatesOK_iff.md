<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.gatesOK_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive and indexed gate conditions

**Claim.** For a finite list of gates, the recursive condition on each gate and its available argument indices is equivalent to requiring the local gate conditions for every gate and the stated bound on each argument at its list position.

**Proof.** Induct on the gate list, generalizing the available length. The empty list satisfies both sides vacuously. For a list with first gate $g$ and tail $G$, unfolding the recursive condition separates the local conditions for $g$ from the recursive condition on $G$ with available length increased by one. By the induction hypothesis, the tail condition is equivalent to its indexed bounds. In the forward direction, the bound for position zero is exactly the local bound for $g$; at a successor position, the tail bound applies with its starting length increased by one, giving the required bound after simplifying the index arithmetic. Conversely, the indexed bound at zero gives the local argument bound for $g$, and the bounds at successor positions yield the tail's indexed conditions. The length, distinctness, and NOT-arity requirements correspond directly to the local condition on each member.
