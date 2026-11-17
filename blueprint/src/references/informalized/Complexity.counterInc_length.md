<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counterInc_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bounds for Binary Increment

**Claim.** For every finite binary word $b$ written least-significant bit first, its increment has length at most $|b|+1$, and the number of leading $1$ bits of $b$ is at most the length of its increment.

**Proof.** Proceed by induction on the word. For the empty word, its increment is the one-bit word $[1]$ and it has no leading $1$ bits, so both bounds hold. For a nonempty word, split on its first bit. If it is $0$, incrementing changes just that bit to $1$; the length is unchanged and the number of leading $1$ bits of the original word is zero. If it is $1$, incrementing changes that bit to $0$ and increments the remaining word. The induction bounds on the tail, together with the added first bit, give both claimed inequalities.
