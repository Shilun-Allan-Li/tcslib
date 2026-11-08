<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.iterate_sampleStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the Sampling Step

**Claim.** After $j$ iterations, the encoded input pair $(Nw,Lw)$ is preserved, the random string has its first $j|Lw|$ bits removed, and the output is preserved if initially nonempty; if initially empty, it records the first successful sample among at most $j$ tries, or remains empty if no try succeeds.

**Proof.** Induct on $j$, generalizing over the random string $r$ and output $out$. At zero iterations the encoding is unchanged, and the stated sampling record is empty because zero tries are available. For the induction step, apply one sampling step after the $j$-step description. The encoding projections recover each component of the paired data (\texttt{Complexity.pairFstD_pairEncode}, \texttt{Complexity.pairSndD_pairEncode}), so the step consumes the next block of $|Lw|$ bits and leaves the suffix after $(j+1)|Lw|$ bits; this uses the identity that dropping a prefix and then another prefix is equivalent to dropping their summed lengths. If $out$ was nonempty, the step retains it. If it was empty, inspect the next block: when its binary value is below the threshold represented by $Nw$, this is the first successful try and the output becomes the encoding of that value; otherwise the step leaves the output empty, corresponding to the previous search continued on the remaining random bits. This is exactly the recursive definition of making up to $j+1$ sampling tries.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
