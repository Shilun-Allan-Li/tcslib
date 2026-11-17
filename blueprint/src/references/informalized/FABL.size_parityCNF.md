<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.size_parityCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity CNF size

**Claim.** For positive $n$, the CNF obtained by taking one clause for each satisfying input of the Boolean dual of parity on $n$ coordinates has exactly $2^{n-1}$ clauses.

**Proof.** Parity on all $n$ coordinates is balanced when $n>0$ (\(`parityFunction_univ_isBalanced`\)). The Boolean dual of a balanced function is also balanced (\(`isBalanced_booleanDual`\)), so the Boolean dual of parity is balanced. Applying the balanced minterm DNF size result to this dual shows that its minterm DNF has $2^{n-1}$ terms. By the definition of the parity CNF, those terms are exactly its clauses; hence its size is $2^{n-1}$.

**Key facts.** `FABL.parityFunction_univ_isBalanced`, `FABL.isBalanced_booleanDual`, `FABL.size_mintermDNF_of_isBalanced`.
