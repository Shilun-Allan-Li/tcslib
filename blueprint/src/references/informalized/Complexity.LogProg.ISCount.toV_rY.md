<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.toV_rY -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected state register

**Claim.** The state vector entry at the register selected by the Boolean value is $s$ when the value is true and $$ when it is false.

**Proof.** Split into the two possible Boolean values. When the value is true, the selected register is the register for $s$, and the state vector has value $s$ there. When it is false, the selected register is the register for $$, whose state-vector value is $$. These are exactly the two branches of the stated conditional.
