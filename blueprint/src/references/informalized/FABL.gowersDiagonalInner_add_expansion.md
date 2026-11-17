<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersDiagonalInner_add_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion of the Diagonal Inner Product

**Claim.** The diagonal Gowers inner product of $f+g$ is the sum, over all subsets $A$ of the $k$-dimensional Boolean cube, of the Gowers inner product of the family that uses $f$ at indices in $A$ and $g$ at all other indices.

**Proof.** Expand the product indexed by the Boolean cube at each fixed choice of the averaging variables. Each term in the expansion chooses, independently at every index, either the value of $f$ or that of $g$. Such choices are in one-to-one correspondence with subsets $A$: use $f$ on $A$ and $g$ on its complement. The product expansion therefore gives the sum over all these subsets, by the product decomposition over a set and its complement (\texttt{FABL.prod_ite_mem_compl}). Next, interchange this finite sum with the average over the base point, and then with the average over the directions. The resulting summand for each $A$ is precisely the Gowers inner product of the family choosing $f$ on $A$ and $g$ elsewhere, proving the identity.

**Key facts.** `FABL.prod_ite_mem_compl`.
