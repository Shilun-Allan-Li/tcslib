<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_inc_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow of fixed-width increment

**Claim.** For every bit string $w$, fixed-width little-endian increment returns no result exactly when $w$ consists entirely of ones, including the empty word.

**Proof.** Induct on the word. For the empty word, increment returns no result, and the empty word is the all-ones word of length zero. For a nonempty word, inspect its first bit. If it is $0$, increment changes that bit to $1$ and returns a result, so overflow does not occur; the word is not all ones either. If the first bit is $1$, increment overflows exactly when the recursive increment of the remaining bits overflows. By induction, that happens exactly when the remaining word consists entirely of ones. Together with the leading $1$, this is precisely the condition that the whole word consists entirely of ones.
