<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.canon_of_getLastD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicality from the Default Last Bit

**Claim.** If the last bit of $w$, taking the default value true when $w$ is empty, is true, then $w$ is canonical.

**Proof.** The characterization of canonical Boolean strings states that $w$ is canonical exactly when its defaulted last bit is true (`Complexity.LogProg.drop_canon`). Applying its forward implication to the hypothesis gives the result.

**Key facts.** `Complexity.LogProg.drop_canon`.
