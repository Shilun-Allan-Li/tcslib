<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.rewindAt_emb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Halted Run at Rewind

**Claim.** Embedding a halted configuration $u$ into block $j$ produces a rewind-phase configuration with the counter updated according to whether the summary of $u$’s output is true, with empty output and all blocks later than $j$ still blank with their heads at zero.

**Proof.** Because $u$ is halted, the state clause in the embedding definition places the augmented configuration in rewind phase at index $j$, with counter $\operatorname{bump}(c,\text{summary}(u)=\mathrm{true})$. The embedding sets the output to the empty list. Now take any block index greater than $j$. It cannot equal $j$, so the embedding leaves its tapes and head positions equal to those in $D$. Freshness of $D$ says these are blank and at zero, respectively. These are exactly the three clauses required for the rewind condition.
