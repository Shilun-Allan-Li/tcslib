<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.controlCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step controller simulation

**Claim.** When $c$ is nonhalting, one step of the conditional-dispatch machine from the embedded controller configuration is the embedding of the configuration reached by taking one step of $D$ from $c$.

**Proof.** Since $c$ is nonhalting, write its state as $q$. The embedded configuration is therefore in the controller's active state carrying $q$ and the stored output bit, if any. In this state, the conditional machine uses $D$'s transition on the same input symbol and the same symbols under $D$'s work-tape heads. The embedding leaves the input position unchanged and embeds the work-tape contents and head positions into the first block of tapes; the additional tapes are blank and stationary. The transition action consequently preserves the input movement and updates the first block exactly as $D$ does, while leaving the extra tapes blank and stationary. Its successor state records $D$'s successor state and the updated stored output bit, and its output remains empty. Comparing the state, input position, tape contents, head positions, and output gives precisely the embedded configuration after one step of $D$.
