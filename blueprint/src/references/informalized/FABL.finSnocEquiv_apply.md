<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.finSnocEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snoc Equivalence Evaluation

**Claim.** The equivalence between a function on the first $n$ indices together with one element of $\Omega$ and a function on $n+1$ indices sends the pair to the function obtained by appending that element as the last value.

**Proof.** The forward map of the equivalence is defined to be the operation that appends the final value to the given function. Evaluating the equivalence at the pair therefore gives exactly that appended function, by definition.
