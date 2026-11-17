<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Diagonalization.lean :: Complexity.UC_eq_false_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Value of the Diagonal Function

**Claim.** The diagonal value at a string is false exactly when the decoded machine halts on that same input with output $[1]$ at some finite time.

**Proof.** By definition, the diagonal value is false precisely when the existential condition in its defining test holds: there is a finite time at which the decoded machine halts on the given input with output $[1]$. Unfolding the conditional definition gives the two directions directly.
