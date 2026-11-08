<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.encodeList_prefixFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix-Freeness of List Encoding

**Claim.** If the encoding of elements of a type is prefix-free in the stated strong sense, then the encoding of finite lists formed from it is also prefix-free in that sense.

**Proof.** We induct on the first list. If it is empty, its encoding is the single terminator bit $0$. A nonempty list encoding starts with $1$, so equality after appending suffixes rules out a nonempty second list; when both lists are empty, removing their common terminator gives equality of the suffixes. Now suppose the first list is $a::as$. A second list cannot be empty, since its encoding starts with $0$ while the first starts with $1$. Write the second as $b::bs$. Removing the common initial $1$ from the equality leaves an equality in which the encoding of $a$ followed by the remainder on its side equals the encoding of $b$ followed by the corresponding remainder on the other side. Prefix-freeness of the element encoding forces $a=b$ and equality of those remainders. The induction hypothesis applied to the remaining lists then gives $as=bs$ and equality of the appended suffixes. Thus the original lists and suffixes agree.
