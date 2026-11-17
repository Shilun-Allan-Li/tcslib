<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.falsifyingCNF_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Width

**Claim.** Every clause in the truth-table CNF of a Boolean function on $\ell$ bits has at most $\ell$ literals.

**Proof.** Any clause in the CNF is the clause associated with some vector $v$. That clause lists one literal for each of the $\ell$ positions, so it has length exactly $\ell$, and in particular at most $\ell$.
