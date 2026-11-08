<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.canon_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Binary Words

**Claim.** For every natural number $n$, its binary bit word is canonical: if the word is nonempty, its last bit is $1$.

**Proof.** For any proof that $\mathrm{Nat.bits}(n)$ is nonempty, the result follows directly from the fact that the last bit of a nonempty binary expansion is true (`bits_getLast`).

**Key facts.** `Complexity.LogProg.bits_getLast`.
