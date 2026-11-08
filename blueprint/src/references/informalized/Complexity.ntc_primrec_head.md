<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_primrec_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the List Head

**Claim.** The function sending a Boolean list $w$ to the singleton list containing its first bit, with the first bit taken to be false when $w$ is empty, is primitive recursive.

**Proof.** The first-bit function with the empty-list convention is primitive recursive. The constant function with value the empty list is also primitive recursive, so applying the primitive-recursive list-cons operation to these two functions produces exactly $[w.headI]$.
