<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.orFunction_transitiveSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitive symmetry of OR

**Claim.** For every $n$, the OR function on sign vectors of length $n$ is invariant under coordinate permutations, and for any two coordinates there is a permutation sending the first to the second.

**Proof.** The OR function is symmetric: its value is determined by whether every coordinate equals $1$, a condition unchanged by permuting coordinates. The general fact that every symmetric function on the sign cube is transitive symmetric then supplies, for any two coordinates, a permutation carrying one to the other while preserving the function (\texttt{FABL.IsSymmetric.isTransitiveSymmetric}), applied to the symmetry of OR (\texttt{FABL.orFunction\_symmetric}).

**Key facts.** `FABL.orFunction_symmetric`, `FABL.IsSymmetric.isTransitiveSymmetric`.
