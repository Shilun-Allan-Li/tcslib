<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.workChain_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Work-Chain Values

**Claim.** At time zero, the work-chain value at every integer position is none.

**Proof.** At time zero the run has made no steps, so `runFrom_zero` identifies the configuration with the initial configuration. In that configuration every work-tape cell is empty and each work-tape head is at position zero. If the defining comparison in the work-chain holds, its value is the symbol scanned at that head, which is none; if it fails, the definition returns none directly. Either way the result is none.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`.
