<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.chunkStep_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunk step on paired encodings

**Claim.** For bit strings $c$, $r$, and $a$, applying the chunk step to the encoding of $c$ paired with the encoding of $r$ paired with $a$ leaves the encoding unchanged when $r$ is empty. Otherwise, it pairs $c$ with an encoding whose first component is the suffix of $r$ after its first $|c|$ bits and whose second component is $a$ followed by the encoding of those first $|c|$ bits.

**Proof.** Unfolding the chunk step and the length-based prefix operations on these paired encodings reduces each decoded first and second component to the list used to construct it. If $r$ is empty, the emptiness test selects the branch that returns the original input. If $r$ is nonempty, the prefix and suffix of $r$ of length $|c|$ are respectively $r.take(|c|)$ and $r.drop(|c|)$, giving the stated updated pair.
