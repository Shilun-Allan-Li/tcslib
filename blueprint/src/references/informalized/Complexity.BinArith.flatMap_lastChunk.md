<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.flatMap_lastChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Last Chunks

**Claim.** For a bit string $w$ and any $N\ge |w|$, concatenating the last chunks of the suffixes of $w$ at positions $0$ through $N-1$ gives the one-term list containing the last bit of $w$, or the empty list when $w$ is empty.

**Proof.** Proceed by induction on $w$. For the empty string, every last chunk is empty, and the last-bit list is empty as well. For $w=b::v$, the length bound ensures $N$ is positive, so write it as $M+1$. The first suffix is $b::v$, and the remaining suffixes are precisely the suffixes of $v$ at positions $0$ through $M-1$. Thus the concatenation is the first last chunk of $b::v$ followed by the corresponding concatenation for $v$, which is its last-bit list by induction. If $v$ is empty, the first chunk contributes $[b]$; if $v$ is nonempty, the first chunk contributes nothing and the induction result contributes the last bit of $v$. In either case this is exactly the last-bit list of $b::v$.
