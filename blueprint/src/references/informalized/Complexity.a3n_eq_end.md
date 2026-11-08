<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Word Equality

**Claim.** For binary words $u$ and $v$, the prefix of $u$ of length $|v|$ equals $v$ and there is no entry of $u$ at index $|v|$ if and only if $u=v$.

**Proof.** Suppose the prefix condition and the missing-entry condition hold. The missing-entry condition implies $|u|\le |v|$. A list whose length is at most the requested prefix length is unchanged by taking that prefix, so the given equality reduces to $u=v$. Conversely, if $u=v$, taking the prefix of length $|v|$ returns the whole word, and there is no entry at index $|v|$; both conditions follow directly.
