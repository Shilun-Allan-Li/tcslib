<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.faninTwo_adderGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of adder gates

**Claim.** For every natural number $n$, each gate in the adder circuit with parameter $n$ is well formed and has at most two inputs.

**Proof.** Split the adder gate list into the partial adder construction and its final two gates. The partial construction is covered by the fan-in theorem for adder gates built through step $i$ (`faninTwo_adderGatesUpTo`), applied at $i=n/3$ with the required bound $3(n/3)\le n$. The final gates are a NOT gate reading the carry index and an AND gate reading the accumulator and sum indices. The bound on the accumulator index (`accIdx_lt`) places it before the relevant new gate position; the carry index and the remaining index bounds follow from their definitions and elementary arithmetic. Thus each final gate has distinct arguments where needed, a NOT gate has exactly one argument, and neither gate has more than two. These facts give well-formedness and the claimed fan-in bound for every gate.

**Key facts.** `BoolCircuit.faninTwo_adderGatesUpTo`, `BoolCircuit.accIdx_lt`.
