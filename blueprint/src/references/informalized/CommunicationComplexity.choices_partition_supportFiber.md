<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Hamming.lean :: CommunicationComplexity.choices_partition_supportFiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition by a coordinate symbol

**Claim.** The support fiber of $u$ over $\{i\}\cup S$ is the union, over symbols $a$ different from $u_i$, of the words in that fiber whose value at $i$ is $a$.

**Proof.** Take a word $w$ in the support fiber over $\{i\}\cup S$. Because $i$ belongs to its support, $w_i\ne u_i$. Thus $w_i$ is one of the symbols indexing the union, and $w$ belongs to the corresponding filtered fiber. Conversely, a word in any such filtered fiber already lies in the support fiber, so it belongs to the left-hand side. These two inclusions give the asserted union; the parts are disjoint because a word has only one value at coordinate $i$.
