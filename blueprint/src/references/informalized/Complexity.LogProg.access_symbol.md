<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_symbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol read from the counter tape

**Claim.** In the specified access configuration, the symbol under the head of work tape $2$ is the first bit of $\mathrm{bits}(k)$ after its first $q$ bits are dropped, if such a bit exists.

**Proof.** By construction, work tape $2$ stores the binary word for $k$, and its head is at position $q$. Reading the buffered tape at that position gives the bit at index $q$ of that word, or no symbol if the index is beyond its end. This is precisely the head of the word obtained by dropping the first $q$ bits.
