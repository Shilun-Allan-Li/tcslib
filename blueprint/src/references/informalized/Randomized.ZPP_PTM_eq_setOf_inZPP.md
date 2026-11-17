<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.ZPP_PTM_eq_setOf_inZPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier characterization of zero-error time

**Claim.** A language belongs to zero-error expected polynomial time exactly when it has a polynomial-time verifier and natural numbers $a,k$ such that, on each input, the verifier never gives an incorrect Boolean answer on any random string of length $a(|x|+1)^k$, and its probability of giving no answer is at most $1/2$.

**Proof.** For one inclusion, every language in `ZPP_PTM` has an abstract zero-error verifier of the stated kind, by `inZPP_of_mem_ZPP_PTM`. Conversely, every language satisfying that verifier characterization belongs to `ZPP_PTM`, by `inZPP_subset_ZPP_PTM`. Together these inclusions establish the claimed equality.

**Key facts.** `Randomized.inZPP_of_mem_ZPP_PTM`, `Randomized.inZPP_subset_ZPP_PTM`.
