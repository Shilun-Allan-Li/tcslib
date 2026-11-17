<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.universalCircuit_const_true_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Universal Circuit for One

**Claim.** For every $n$, the universal circuit for the constant-one function has size $2^n(n+1)+1$.

**Proof.** The size formula for a universal circuit says its size is one plus the number of assignments on which the function is true, multiplied by $n+1$ (`universalCircuit_size`). The constant-one function is true on every assignment, and there are $2^n$ assignments to $n$ Boolean variables. Substituting this count into the formula gives $2^n(n+1)+1$.

**Key facts.** `BoolCircuit.universalCircuit_size`.
