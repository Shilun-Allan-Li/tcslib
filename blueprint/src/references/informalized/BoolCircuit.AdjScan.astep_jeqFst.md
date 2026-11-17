<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.astep_jeqFst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step source comparison

**Claim.** On an edge input with target $(iv,tv)$, the source-comparison instruction at state $uE$ preserves registers $(p,c,a)$ and moves to the accepting state exactly when $a=iv$.

**Proof.** The edge scan’s instruction at $uE$ with its flag set compares the bits of register $a$ with the first word decoded from the input pair. The edge-target hypothesis identifies that word with the bits of $iv$. Since the natural-number bit representation is injective (`Complexity.LogProg.bits_injective`), the comparison succeeds exactly when $a=iv$. This instruction changes only the control label, leaving the registers and result unchanged, which gives the claimed transition.

**Key facts.** `Complexity.LogProg.bits_injective`.
