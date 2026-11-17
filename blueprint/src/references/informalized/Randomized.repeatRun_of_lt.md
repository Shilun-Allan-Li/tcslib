<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.repeatRun_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Complete Block Means No Result

**Claim.** If the bit string $w$ has length less than $t$, the repeated-run procedure returns no value on $w$.

**Proof.** Since $|w|<t$, the defining condition for the recursive clause fails. The other branch of the definition returns `none`, so the run produces no value.
