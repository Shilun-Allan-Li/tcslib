<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Stop_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Release Wrapper

**Claim.** If the original configuration is live and, when the release flag is true, its state is not the designated exit state, then the wrapper’s next configuration is the original machine’s next configuration with the flag set to true.

**Proof.** Because the configuration is live, its state has the form $\mathrm{some}(q)$ for some state $q$. The wrapper’s halt condition is that the flag is true and the underlying state is the designated exit state. The hypothesis rules out precisely this conjunction, so the wrapper does not halt on this step. Its transition otherwise uses the original machine’s transition from $q$, while marking the successor state with a true flag and preserving the transition’s tape actions. This is exactly the original one-step successor with the flag set to true.
