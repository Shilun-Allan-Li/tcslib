<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeNumber_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits of the Sentinel Code

**Claim.** For every finite Boolean string $xs$, the least-significant-first binary digits of its sentinel numeric code are exactly $xs$ followed by a true bit.

**Proof.** Proceed by induction on $xs$. For the empty string, the sentinel code is $1$, whose binary digit list is the single true bit. For a string $b::xs$, its code is obtained by appending the bit $b$ to the code of $xs$. The binary-digit append identity applies because the code of $xs$ is nonzero; positivity of every sentinel code gives this condition (`Turing.bridgeNumber_pos`). By the induction hypothesis, the digits of the shorter code are $xs$ followed by true, so appending $b$ yields precisely $b::xs$ followed by true.

**Key facts.** `Turing.bridgeNumber_pos`.
