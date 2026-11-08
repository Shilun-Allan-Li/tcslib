<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.size_mintermDNF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minterm DNF size bound

**Claim.** For a function from the $n$-dimensional sign cube to $
\{-1,1\}$, the minterm DNF formed from inputs where the function equals $-1$ has size at most $2^n$.

**Proof.** By definition, the size is the number of inputs in the cube on which the function equals $-1$: mapping those inputs to their minterms does not change the list length. This set is contained in the whole cube, whose cardinality is $2^n$, so the claimed bound follows.
