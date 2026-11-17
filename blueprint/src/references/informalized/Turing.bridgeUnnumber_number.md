<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeUnnumber_number -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the sentinel code

**Claim.** For every Boolean string $xs$, decoding its sentinel numeric code returns $xs$.

**Proof.** The sentinel-code bit identity (\texttt{bridgeNumber_bits}) says that the binary expansion of the code is $xs$ followed by a final true bit. The decoder reverses this expansion, removes the sentinel bit at the end of the reversed list, and reverses back. The result is precisely $xs$.

**Key facts.** `Turing.bridgeNumber_bits`.
