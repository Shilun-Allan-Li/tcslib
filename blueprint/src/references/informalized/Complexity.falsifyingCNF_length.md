<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.falsifyingCNF_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Clause Count

**Claim.** The truth-table CNF of a Boolean function on $\ell$ bits has at most $2^\ell$ clauses.

**Proof.** The construction has one clause for each vector in the truth table on which $f$ is false. Its clause count is therefore the number of such vectors. This is at most the total number of vectors in $\{0,1\}^{\ell}$, which is $2^\ell$.
