<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement away from the anchor

**Claim.** For every state other than administrative anchor state $0$, the active and stopped body machines have the same transition on every input symbol and tuple of work-tape readings.

**Proof.** Split according to whether the state lies in the clean-machine component or the administrative component. In the clean-machine component, the stopped flag does not occur in the transition, so the two transitions are definitionally identical. In the administrative component, the hypothesis that the state is not the anchor implies its finite administrative index is nonzero. Expanding the transition definition, the only branch whose behavior depends on the stopped flag is the index-zero branch. Every remaining branch is identical for the two parameter values, proving the claim.
