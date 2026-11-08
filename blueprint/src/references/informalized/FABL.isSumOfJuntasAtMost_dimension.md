<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.isSumOfJuntasAtMost_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition into coordinate juntas

**Claim.** Every real-valued function on $\Omega^n$ is a sum indexed by subsets of coordinates, with each summand depending only on the coordinates in its indexing set and all terms indexed by sets of size greater than $n$ equal to zero.

**Proof.** Define the summand indexed by $J$ to be $f$ when $J$ is the full set of coordinates, and zero otherwise. The full-coordinate term depends only on those coordinates because agreement on all coordinates means the two inputs are equal; every zero term also has the required dependence property. No subset of the $n$ coordinates has more than $n$ elements, so the vanishing requirement for sets of size greater than $n$ holds. In the sum, every term except the full-coordinate term is zero, leaving exactly $f$.
