<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.bits_two_pow_eq_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits of a Power of Two

**Claim.** For every natural number $n$, the binary digit list of $2^n$ consists of $n$ false digits followed by a single true digit.

**Proof.** Use the fact that multiplying $2^n$ by a positive integer $m$ prefixes the binary digit list of $m$ with $n$ false digits ($\texttt{bits\_two\_pow\_mul}$). Take $m=1$, which is positive. Since the binary digits of $1$ are the single digit $\texttt{true}$, the resulting list is $n$ false digits followed by that true digit, as claimed.

**Key facts.** `Turing.bits_two_pow_mul`.
