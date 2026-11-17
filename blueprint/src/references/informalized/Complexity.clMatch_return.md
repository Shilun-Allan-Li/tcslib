<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Matcher Control Is Stationary

**Claim.** In the completed control, the matcher’s transition is the action with zero movement, no tape writes, no output, and the same completed control as successor, for any input symbol and scanned work-tape contents.

**Proof.** The transition definition’s completed-control branch is exactly the zero-movement control action whose successor is that same completed state. It does not inspect the input or work-tape symbols, so the equality holds for every assignment of them.
