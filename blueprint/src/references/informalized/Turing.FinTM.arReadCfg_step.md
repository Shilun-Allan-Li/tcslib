<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arReadCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Read Sweep

**Claim.** For a valid read-sweep counter $j<N+1$, one simulator step advances the read-sweep configuration from counter $j$ to counter $j+1$.

**Proof.** Because $j<N+1$, the simulator takes the read-sweep branch. The symbol currently scanned on each work tape is the entry at offset $j$ of the encoded original symbol (`Turing.FinTM.arReadCfg_symbols`). The transition writes this entry into the buffer at offset $j$; updating the partially filled buffer in this way gives exactly the buffer for counter $j+1$ (`Turing.FinTM.arBuffer_update`). The input position, tape contents, and output are otherwise unchanged. The encoded work-head position advances from offset $j$ to $j+1$, as required by the next read-sweep configuration. Hence the resulting state and every configuration field agree with that configuration.

**Key facts.** `Turing.FinTM.arReadCfg_symbols`, `Turing.FinTM.arBuffer_update`.
