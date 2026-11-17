<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fixed Return Configuration

**Claim.** For every bit-list input and every configuration of the increment machine whose control is the return state, one step leaves the entire configuration unchanged.

**Proof.** With control equal to the return state, the machine's transition table selects its control action: it preserves the configuration's state and makes no tape or output change. Its input-head movement is zero, which fixes the input position (`Turing.moveInputPos_zero`). Consequently every component of the configuration is unchanged.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
