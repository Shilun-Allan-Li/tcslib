<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeEraseWrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Write Reader Erasure Law

**Claim.** For every bit string, discarding the value decoded by the optional-write reader gives the same result as a two-bit skipper that accepts every pair of bits.

**Proof.** A bit string with fewer than two bits fails both the reader and the skipper. If it begins with two bits, there are four possible pairs. In each case the reader succeeds and returns the suffix after those two bits, regardless of the decoded write value; the skipper likewise accepts the pair and returns that suffix. Hence the two results agree in every case.
