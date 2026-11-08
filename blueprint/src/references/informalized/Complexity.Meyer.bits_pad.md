<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.bits_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Binary Representation

**Claim.** If $j<2^w$, the binary digits of $j$, listed least significant first and padded with zeroes to length $w$, form the width-$w$ little-endian binary word of $j$.

**Proof.** The size bound implies that the number of binary digits of $j$ is at most $w$, using the characterization of binary size by the length of the bit list and the size bound for numbers below a power of two. Let $u$ be the bit list of $j$ followed by $w-|u|$ zeroes. Appending zeroes does not change the represented value ($\texttt{ctrVal\_append\_zeros}$), and the bit list represents $j$ ($\texttt{ctrVal\_bits}$). Hence the value of $u$ is $j$. Its length is exactly $w$. The word reconstructed from a word’s length and represented value is that word ($\texttt{enumWord\_ctrVal}$); applying this to $u$ proves the asserted equality.

**Key facts.** `Complexity.Meyer.ctrVal_append_zeros`, `Complexity.TimeHierarchy.ctrVal_bits`, `Complexity.Meyer.enumWord_ctrVal`.
