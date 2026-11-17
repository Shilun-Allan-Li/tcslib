<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_primrec_nhead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Negated List Head

**Claim.** The function sending a Boolean list $w$ to the singleton list containing the negation of its first bit, with the first bit taken to be false when $w$ is empty, is primitive recursive.

**Proof.** The first-bit function with the empty-list convention is primitive recursive, and Boolean negation is primitive recursive. Their composition gives the negated first bit. Applying list-cons to that value and the constant empty list produces the required singleton list.
