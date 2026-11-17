<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.summ_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary after appending a Boolean value

**Claim.** For a Boolean list $u$ and optional Boolean value $e$, the summary of $u$ followed by $e$ (when present) is the combination of the summary of $u$ with $e$.

**Proof.** If $e$ is absent, appending it leaves $u$ unchanged, and combining with an absent value leaves its summary unchanged. If $e$ is present, split into the three possible shapes of $u$: empty, a singleton, or a list with at least two entries. In the first two cases the appended list has respectively one or two entries, so its summary is the appended value or false, exactly the combination prescribed by `push`. In the last case both the original and appended lists have at least two entries, so both summaries are false.
