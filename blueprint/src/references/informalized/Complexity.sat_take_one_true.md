<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_take_one_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Bit Prefix Characterization

**Claim.** For every binary string $x$, its prefix of length one is $[1]$ if and only if its first bit exists and equals $1$.

**Proof.** Split into the two cases $x=[]$ and $x=b::r$. For the empty string, the prefix is empty and there is no first bit, so both sides are false. For a nonempty string, taking one element gives $[b]$, while the head is $b$; these agree with the claimed equivalence exactly when $b=1$.
