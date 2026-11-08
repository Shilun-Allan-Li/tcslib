<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.getLastD_of_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final bit of a canonical word

**Claim.** If every nonempty canonical bit string ends in true, then its final entry, with true as the default for an empty string, is true.

**Proof.** The characterization of canonical words (`drop_canon`) states that this final-entry condition is equivalent to canonicality. Applying its implication from canonicality gives the result.

**Key facts.** `Complexity.LogProg.drop_canon`.
