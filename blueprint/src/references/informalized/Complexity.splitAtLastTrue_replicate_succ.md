<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.splitAtLastTrue_replicate_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutting a word of true bits

**Claim.** For every natural number $n$, cutting the word of $n+1$ true bits at its last true bit returns the word of $n$ true bits.

**Proof.** Reversing a list of true bits leaves it unchanged, and a list of $n+1$ true bits consists of a list of $n$ true bits followed by one more true bit. Thus the reversed word begins with a true bit; the cut removes that bit and reverses the remaining $n$ true bits. Since that remaining word is itself unchanged by reversal, the result is `some (List.replicate n true)`.
