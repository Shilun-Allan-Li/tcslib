<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.v_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Pointer Slot

**Claim.** For any register state, slot $0$ of its register vector contains its input pointer.

**Proof.** By the definition of the register-value vector, its coordinates are listed in register order, beginning with the input pointer. Evaluating this vector at coordinate $0$ therefore gives the input pointer.
