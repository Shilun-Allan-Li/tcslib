<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean :: Complexity.LogProg.tapeWord_bufferTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Word from Its Buffer Tape

**Claim.** For every finite Boolean word $w$, the word extracted from the tape storing $w$ contiguously from cell zero is $w$.

**Proof.** The tape storing $w$ is certainly a buffer tape for some word, namely $w$ itself, so the definition of the extracted word selects a word $w'$ whose buffer tape equals that of $w$. Equality of the tape functions implies equality of their values at every integer position. At each natural index $i$, the buffer tape returns the optional entry of its stored word at index $i$. Hence $w'[i]?=w[i]?$. Lists whose optional entries agree at every index are equal, so the extracted word is $w$.
