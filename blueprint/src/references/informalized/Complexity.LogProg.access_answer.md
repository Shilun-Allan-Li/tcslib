<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_answer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer-State Halting Path

**Claim.** From the answer-state configuration with tapes encoding $0,0,k,p$ and the third head at $0$, there is an access path to the same configuration halted with output $[b]$.

**Proof.** The initial configuration satisfies the head bounds by `accessCfg_safe`, using that all heads are at zero and zero lies within the permitted interval. The one-step access-path fact (`access_step`) applies to a safe configuration in state “answer $b$”; in that state the transition emits the bit $b$ and halts. Unfolding that transition shows that the tapes and head positions are unchanged, the state is halted, and the output is the one-bit word $[b]$. The zero input-head movement preserves its position (`moveInputPos_zero`), so the resulting configuration is exactly the specified halted configuration.

**Key facts.** `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.access_step`, `Turing.moveInputPos_zero`.
