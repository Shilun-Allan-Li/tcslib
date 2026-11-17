<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PromiseKarpReducible.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of promise reductions

**Claim.** If $A$ reduces to $B$ and $B$ reduces to $C$ by polynomial-time maps preserving promised yes- and no-instances, then $A$ reduces to $C$ by such a map.

**Proof.** Choose reductions $f$ from $A$ to $B$ and $g$ from $B$ to $C$. Use their composition $g\circ f$. A promised yes-instance of $A$ is sent by $f$ to a promised yes-instance of $B$, and then by $g$ to a promised yes-instance of $C$. The same two preservation steps send every promised no-instance of $A$ to a promised no-instance of $C$. The composition of polynomial-time maps is polynomial-time, so it witnesses the required reduction.
