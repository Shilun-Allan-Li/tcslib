<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.ite_bool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean encoding of a proposition

**Claim.** For a proposition with a decision procedure, choosing between $f(\mathrm{true})$ when it holds and $f(\mathrm{false})$ otherwise is the same as applying $f$ to its Boolean decision value.

**Proof.** Split into the two cases: the proposition holds, or it does not. In the first case its decision value is true and both sides equal $f(\mathrm{true})$; in the second its decision value is false and both sides equal $f(\mathrm{false})$.
