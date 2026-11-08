<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_double_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Doubled Word

**Claim.** Replacing each bit of a finite binary word by two consecutive copies produces a word of length twice the original length.

**Proof.** Apply the paired-encoding length formula (`Turing.universal_pair_length`) to the word $a$ and the empty word. The encoding consists of the doubled bits of $a$, followed by the two-bit separator and the empty suffix. Its length is therefore both the length of the doubled word plus $2$ and $2|a|+2$. Cancelling the separator length gives $2|a|$.

**Key facts.** `Turing.universal_pair_length`.
