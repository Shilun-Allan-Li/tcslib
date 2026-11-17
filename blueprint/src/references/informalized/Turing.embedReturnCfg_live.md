<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedReturnCfg_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live state under return embedding

**Claim.** When a configuration has a live state, its return embedding agrees with renaming that state into the left summand.

**Proof.** Split on the configuration's state. The halted case contradicts the hypothesis that the state is not none. In the live case, write the state as $q$. The return embedding replaces it by the left-summand state $\mathrm{inl}(q)$, and renaming the configuration by the left injection does the same; all other configuration data are unchanged. Hence the configurations agree.
