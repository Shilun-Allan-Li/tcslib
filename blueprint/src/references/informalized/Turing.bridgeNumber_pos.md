<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeNumber_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Sentinel Code

**Claim.** The sentinel numeric code of every finite Boolean string is strictly positive.

**Proof.** Induct on the string. The empty string has code $1$, which is positive. For a string $b::xs$, the code is obtained by applying the binary bit-append operation to $b$ and the code of $xs$. In each of the two cases $b=\text{false}$ and $b=\text{true}$, this operation preserves strict positivity, so the code remains positive.
