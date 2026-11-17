<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation Phase of the Round

**Claim.** There is a time $t\le2(|s|+1)$ such that after $t+1$ steps the round body reaches the counting-host embedding of the source's initial configuration with unary work tapes of length $|s|+1$, heads at zero, and empty output; throughout this run it avoids the anchor state.

**Proof.** Apply the phase-embedding argument (`splitEmbed_cut`) to the preparation machine embedded in the round body. The preparation simulation reaches its designated ready state after $2(|s|+1)$ steps by the preparation-run fact (`splitPrepare_run`). The embedding keeps preparation states distinct from the anchor. At the ready state the preparation machine is stationary, and before reaching it the round body agrees with the preparation machine under the state embedding. Thus the embedding argument supplies a time $t$ no greater than $2(|s|+1)$ at which the ready configuration is reached, while avoiding the anchor through that time. One further round-body step switches from this ready state to the counting state. The transition is a control action with no tape or output changes; a zero input movement leaves the input position fixed (`moveInputPos_zero`). Unpacking the ready configuration shows that this is exactly the counting-host configuration encoding the source's initial state and unary work tapes, with heads at zero and empty output. The added endpoint is not the anchor either, so anchor avoidance holds through time $t+1$. The successor-run identity (`runFrom_succ_eq_step'`) expresses this last step after the first $t$ steps.

**Key facts.** `Turing.FinTM.splitEmbed_cut`, `Turing.FinTM.splitPrepare_run`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
