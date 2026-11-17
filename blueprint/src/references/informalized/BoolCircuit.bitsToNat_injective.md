<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.bitsToNat_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of binary list encoding

**Claim.** The map sending a finite Boolean list to the natural number whose base-two digits are its bits followed by a terminal digit $1$ is injective.

**Proof.** For each Boolean list $w$, the base-two digits of its encoding are exactly the list of its Boolean digits followed by the terminal $1$. Indeed, the digits are all less than the base $2$ by the digit bound (\texttt{bitsToNat_digits_lt}), and the final digit is nonzero; the base-expansion theorem for \texttt{Nat.digits} therefore recovers the original digit list from its \texttt{Nat.ofDigits} value. If two encodings are equal, applying this recovery to each shows that their digit lists, including the terminal $1$, are equal. Cancel the common final singleton to obtain equality of the mapped Boolean digit lists. The map from Booleans to digits, sending false to $0$ and true to $1$, is injective, so equality of the mapped lists implies equality of the original Boolean lists.

**Key facts.** `BoolCircuit.bitsToNat_digits_lt`.
