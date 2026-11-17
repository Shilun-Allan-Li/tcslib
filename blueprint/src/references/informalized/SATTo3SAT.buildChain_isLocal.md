<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.buildChain_isLocal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Locality of chain clauses

**Claim.** If every lifted literal is local to index $i$, then each clause in the chain built with clause index $i$ has all three literals local to $i$.

**Proof.** Induct on the literal list, generalizing the chain counter. The empty list produces no clauses. For lists of length one or two, the only possible chain clause has the negated auxiliary variable at index $i$ in its first position, lifted input literals in the other positions, and, in the one-literal case, a positive auxiliary variable at index $i$ in the third position. These are all local by definition and by the hypothesis on the lifting map. For a longer list, a clause in the chain is either the first clause, whose auxiliary literals both have index $i$ and whose lifted literal is local by hypothesis, or belongs to the chain for the tail. In the latter case the induction hypothesis applies to that tail with the incremented counter.
