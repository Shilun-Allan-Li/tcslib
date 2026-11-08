<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_tseitinClauseChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause chain length

**Claim.** If the number of literals in $L$ is at most the number in $A$ plus $3$, then the Tseitin clause chain has length $\max(|L|-2,1)$.

**Proof.** Proceed by induction on the length of $L$, following the recursive definition of the chain. When $L$ has at least four literals and $A$ has an auxiliary literal, the construction emits one clause and recurses on a list formed by that auxiliary literal’s negation followed by the last three literals and the remainder of $L$. The capacity hypothesis is preserved for these shorter lists: removing one auxiliary and replacing the first three literals by one leaves enough auxiliaries for the recursive call. By induction, the tail chain has length $\max((|L|-2)-2,1)$; adding the emitted clause gives $\max(|L|-2,1)$, as a direct check of the natural-number cases shows. If $L$ has at least four literals but $A$ is empty, the capacity hypothesis is impossible. For lists of lengths zero through three, the definition returns a singleton list containing $L$, whose length is $1=\max(|L|-2,1)$.
