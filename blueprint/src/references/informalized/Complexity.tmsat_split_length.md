<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_split_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a padded concatenation

**Claim.** If finite bit strings $y$ and $w$ satisfy $|w|=|y|+1$, then $|yw|$ is odd and $(|yw|-1)/2=|y|$.

**Proof.** The length of a concatenation is the sum of the lengths, so $|yw|=|y|+|w|=2|y|+1$. This is odd, and subtracting one and dividing by two gives $|y|$.
