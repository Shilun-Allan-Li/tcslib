<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counterInc_potential -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Count Identity for Binary Increment

**Claim.** For every finite binary word $b$ written least-significant bit first, the number of $1$ bits in its increment plus the number of leading $1$ bits in $b$ equals the number of $1$ bits in $b$ plus one.

**Proof.** Proceed by induction on the word. For the empty word, incrementing creates one $1$, while the original word has no $1$ bits and no leading $1$ bits. If the first bit is $0$, incrementing changes it to $1$ and leaves the tail unchanged; there are no leading $1$ bits in the original word, so the identity follows directly. If the first bit is $1$, incrementing changes it to $0$ and increments the tail. The number of $1$ bits in the result is therefore the number in the incremented tail. The original word has one more $1$ than its tail, and its leading-$1$ count is one plus the tail's leading-$1$ count. Applying the induction identity to the tail yields the claimed equality.
