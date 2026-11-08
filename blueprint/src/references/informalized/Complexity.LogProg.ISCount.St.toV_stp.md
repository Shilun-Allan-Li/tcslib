<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_stp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walk-step-count coordinate

**Claim.** For any state $\sigma$, the coordinate at index $16$ of its 17-coordinate encoding is the step count $\mathrm{stp}$.

**Proof.** By definition, the encoding lists the state fields in order, with $\mathrm{stp}$ in position $16$. Evaluating the encoding at that index therefore returns $\mathrm{stp}$.
