<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.choices_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of alternative symbols

**Claim.** At a position $i$ in a word over a finite alphabet $\alpha$, exactly $|\alpha|-1$ symbols differ from the symbol $u_i$.

**Proof.** The set of symbols different from $u_i$ is the whole alphabet with the single element $u_i$ removed. Since $u_i$ belongs to the alphabet, removing it reduces the cardinality by one. Hence the number of alternatives is $|\alpha|-1$.
