<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_width_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary width after halving

**Claim.** For every nonzero natural number $n$, the binary word for $\lfloor n/2\rfloor$ has length one less than the binary word for $n$.

**Proof.** For nonzero $n$, its binary word has positive length, since binary length agrees with the natural-number size and positive numbers have positive size. The binary word for $n/2$ is the tail of the binary word for $n$ (`bits_half`). Removing the head of a nonempty list decreases its length by one, giving the stated equality.

**Key facts.** `Complexity.LogProg.bits_half`.
