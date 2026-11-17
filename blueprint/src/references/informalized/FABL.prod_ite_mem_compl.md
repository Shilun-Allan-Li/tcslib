<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.prod_ite_mem_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product split over a set and its complement

**Claim.** The product that selects $f(i)$ on $A$ and $g(i)$ outside $A$ is the product of $f$ over $A$ times the product of $g$ over the complement of $A$.

**Proof.** Partition the finite index set into those indices belonging to $A$ and those not belonging to $A$. The product of a piecewise-selected function over a finite set factors as the product over the indices satisfying the condition times the product over those failing it (`Finset.prod_ite`). Since the ambient set is the whole finite type, these two filtered sets are precisely $A$ and its complement. Substituting them gives the claimed factorization.
