<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean :: Turing.NDTM.visitedWith_subset_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions Under Appended Choices

**Claim.** Every head position visited on a chosen work tape during the run under $w$ is also visited during the run under the concatenated word $ww'$.

**Proof.** Take a visited position from the run under $w$. By the definition of the visited set as an image, it is the head position after running on some prefix of length $j$, where $j$ lies in the range from $0$ through $|w|$. The same index $j$ lies in the corresponding range for $ww'$, since $|w|\le |ww'|$. Moreover, taking the first $j$ symbols of $ww'$ gives exactly the first $j$ symbols of $w$, because $j\le |w|$. Thus this same index witnesses that the position belongs to the visited set for $ww'$.
