<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeValue_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor recursion for parity trees

**Claim.** The depth-$(t+1)$ parity tree value at index $g$ is the product of the depth-$t$ values at indices $gr+j$ for $j<r$.

**Proof.** This is the defining successor clause for the parity tree: at the next level, its value is the product of the values of its $r$ children, indexed by $gr+j$.
