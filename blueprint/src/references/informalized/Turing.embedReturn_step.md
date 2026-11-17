<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedReturn_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step under return embedding

**Claim.** Under the stated transition rules, stepping the return embedding of any configuration gives the return embedding of its original one-step result.

**Proof.** Split on the original configuration's state. If it is halted, its run configuration has no state. The return embedding places it in the added state, where the idle transition keeps that state and leaves the input head, work tapes, output, and work heads unchanged. This is exactly the return embedding of the unchanged halted configuration. If the state is $q$, the return embedding has state $\mathrm{inl}(q)$. Its input symbol and work-head symbols are unchanged, so the left-state transition hypothesis identifies the transition used by the returned machine with the return embedding of the original transition. Applying these actions gives identical configurations: their movements, tape changes, output, and successor state all match by the definition of the return action and configuration embedding.
