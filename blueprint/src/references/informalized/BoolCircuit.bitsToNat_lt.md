<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.bitsToNat_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on binary list encoding

**Claim.** For every finite Boolean list $w$, the natural number encoded by its bits followed by a terminal digit $1$ is less than $2^{|w|+1}$.

**Proof.** Every digit in the encoded list is less than the base $2$ by the digit bound (\texttt{bitsToNat_digits_lt}). The standard bound for a number represented by base-$b$ digits says that if all digits are less than $b$, then its value is less than $b$ raised to the number of digits. Here the digit list has length $|w|+1$, so its value is less than $2^{|w|+1}$.

**Key facts.** `BoolCircuit.bitsToNat_digits_lt`.
