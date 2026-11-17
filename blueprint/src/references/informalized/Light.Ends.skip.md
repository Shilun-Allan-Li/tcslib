<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skip execution

**Claim.** If $Q$ holds in state $\sigma$, then skip can execute from $\sigma$ within any budget $T$ and end in a state satisfying $Q$.

**Proof.** Skip leaves the state unchanged and has execution cost zero. Since zero is at most every natural-number budget, choose $\sigma$ itself as the final state; the assumed $Q(\sigma)$ is the required postcondition.
