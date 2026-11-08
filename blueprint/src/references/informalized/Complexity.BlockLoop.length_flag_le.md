<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean :: Complexity.BlockLoop.length_flag_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Boolean Flag

**Claim.** If $f$ is a nonempty finite bit string and $b$ is Boolean, then the length of $[1]$ when $b$ is true and of $f$ otherwise is at most the length of $f$.

**Proof.** If $b$ is false, the selected string is $f$, so the lengths are equal. If $b$ is true, the selected string is the singleton $[1]$, of length one; nonemptiness of $f$ implies its length is at least one. In either case the required bound follows.
