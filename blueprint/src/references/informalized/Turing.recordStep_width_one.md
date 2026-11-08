<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_width_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the Successor Value

**Claim.** The binary representation of $n+1$ has length one exactly when $n=0$.

**Proof.** The length of the binary digit list for $n+1$ is its binary size (`Nat.size_eq_bits_len`). If this length is one, then $n+1$ cannot be at least $2$, since every number at least $2$ has binary size greater than one (`Nat.lt_size`). Hence $n=0$. Conversely, if $n=0$, then $n+1=1$, whose binary size is one.
