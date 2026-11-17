<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumInc_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Increment Specification

**Claim.** For every Boolean word $u$, a successful fixed-width increment produces a word of the same length whose little-endian value is one greater than that of $u$; if there is no result, then the value of $u$ plus one is $2^{|u|}$.

**Proof.** Induct on the word. The empty word has no increment, and its value plus one is $1=2^0$. For a word beginning with false, incrementing changes that first bit to true and leaves the remaining word unchanged; this preserves length and adds one to the little-endian value. For a word beginning with true, the increment recursively processes the tail and, if successful, changes the first bit to false. The tail's value increases by one, while the leading-bit contribution drops by one; because the leading bit doubles the tail value, the whole word's value increases by exactly one, and its length is unchanged. If the recursive increment has no result, the induction hypothesis says the tail's value plus one is $2^{|u|}$, where $u$ is the tail. The original word's value plus one is then $2^{|u|+1}$, as required.
