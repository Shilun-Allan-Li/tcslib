<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_split_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split of a Padded String

**Claim.** If $|w|=|y|+1$, the odd split of $yw$ is the self-delimiting pair encoding of $y$ and $w$.

**Proof.** The length assumption gives $|y|+(|y|+1)=|y|+|w|=|yw|$. By `tmsat_split_exists`, the split search at the concatenation's length therefore returns the cut position $|y|$. The definition of the odd split now encodes the prefix of that length and the remaining suffix. Those are exactly $y$ and $w$, respectively.

**Key facts.** `Complexity.tmsat_split_exists`.
