<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.split_fuel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length Computation Bound

**Claim.** For all natural numbers $C,e$, `lengthBitsTM` computes the binary representation of the input length within $((C+1+5e)2^e+45)(|w|+1)^{e+1}$ steps on every word $w$.

**Proof.** The length-bits machine computes the binary representation of $|w|$ in $5(|w|+1)$ steps (`lengthBitsTM_computes`). Since $|w|+1\le (|w|+1)^{e+1}$, its running time is at most $5(|w|+1)^{e+1}$. The stated coefficient is at least $5$, so this is within the claimed bound. A machine that has halted remains in its halted configuration, allowing its computation-time guarantee to be extended to this larger time bound (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.lengthBitsTM_computes`, `Turing.FinTM.ComputesInTime.mono`.
