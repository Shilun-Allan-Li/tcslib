<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.CodeAt.tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail of a Code Segment

**Claim.** If the list beginning at position $\mathrm{pos}$ has $i$ followed by the list $l$, then $l$ is a prefix of the list beginning at position $\mathrm{pos}+1$.

**Proof.** Apply the result that takes the right part of a code segment to the decomposition $[i]\mathbin{++}l$. The next position is $\mathrm{pos}+|[i]|=\mathrm{pos}+1$, giving the claimed prefix relation.

**Key facts.** `WordRAM.CodeAt.right`.
