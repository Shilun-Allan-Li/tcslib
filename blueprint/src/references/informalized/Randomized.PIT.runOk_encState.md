<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.runOk_encState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Validity of an Encoded State

**Claim.** For bit strings $ctx,w$ and a finite list $vs$ of natural numbers, the run-validity predicate of their encoded state equals true exactly when $w=[0]$.

**Proof.** The first- and second-component projections of a pair encoding recover the components that define the state, so expanding the encoding reduces the run-validity expression to the condition that $w$ is nonempty and is done. If $w$ is empty, the nonempty condition fails. If $w$ has one bit, checking its two possibilities shows that only the string $[0]$ is both nonempty and done. If $w$ has at least two bits, it is neither empty nor a one-bit string, so the done condition fails. These cases give exactly the indicator of $w=[0]$.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
