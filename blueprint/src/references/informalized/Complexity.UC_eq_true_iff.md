<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Diagonalization.lean :: Complexity.UC_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Value of the Diagonal Function

**Claim.** The diagonal value at a string is true exactly when the decoded machine never halts on that same input with output $[1]$ at any finite time.

**Proof.** The diagonal value is defined to be true when the existential condition asserting such a halting run is false. Negating that condition says exactly that there is no finite time at which the decoded machine halts on the given input with output $[1]$.
