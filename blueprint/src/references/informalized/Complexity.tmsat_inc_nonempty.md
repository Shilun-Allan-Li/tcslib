<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_inc_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment output is nonempty

**Claim.** For every bit string $w$, the fixed-width increment function never returns the empty word as its output.

**Proof.** If $w$ is empty, the increment function returns `none`, so it cannot return `some []`. For a nonempty word, split on its first bit. If the first bit is $0$, incrementing changes it to $1$ and leaves the tail unchanged, producing a nonempty word. If the first bit is $1$, the result is obtained by incrementing the tail and, if that succeeds, prepending $0$. In either case the result is either `none` or begins with $0$, hence is not `some []`.
