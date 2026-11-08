<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.v_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Register Value

**Claim.** For any register record, the register-value function at coordinate $0$ equals its input length.

**Proof.** By definition, the vector of register values lists the input length as its first entry, at coordinate $0$. Reading that entry gives the claimed equality.
