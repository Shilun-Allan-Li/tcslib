<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.toV_wB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected stage register

**Claim.** The state vector entry at the register selected by the Boolean value is $i$ when the value is true and $i_1$ when it is false.

**Proof.** Consider the two Boolean cases. If the value is true, the selected register is the one storing $i$, so the state vector entry is $i$. If it is false, the selected register stores $i_1$, so the entry is $i_1$. This gives the claimed conditional in both cases.
