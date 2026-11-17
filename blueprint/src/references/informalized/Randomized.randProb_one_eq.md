<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_one_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Specified One-Bit String

**Claim.** For either Boolean value $c$, a uniformly random Boolean string of length one equals the one-bit string $[c]$ with probability $1/2$.

**Proof.** For fixed $c$, exactly one of the two functions from a one-element index set to the Booleans yields the list $[c]$ under the list conversion. Thus the event has cardinality one, while the sample space has size $2$. Its probability is therefore $1/2$.
