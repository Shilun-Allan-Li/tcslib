<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPPIT.lean :: Randomized.pitVerifier_of_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on invalid circuit pairs

**Claim.** If the projections of a bit string do not decode to a pair of well-formed circuits with a common input count, the verifier returns true.

**Proof.** Unfold the verifier and split on the decode result of each projection. If either decode fails, its default branch returns true. If both decode, split on whether their input counts agree. When they do not agree, the verifier again returns true. In the remaining case the counts agree; if both circuits were well formed, their decode results and well-formedness would exhibit the pair forbidden by the hypothesis. Thus at least one is not well formed, and the verifier's conditional returns true.
