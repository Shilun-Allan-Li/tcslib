<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.length_iterate_le_of_ctx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Iterated Context-Preserving Maps

**Claim.** If each application of $f$ preserves the first decoded component and increases length by at most $A$ times one plus that component's length, then after $j$ iterations the length is at most the initial length plus $jA$ times one plus the initial decoded-component length.

**Proof.** First show that the first decoded component remains unchanged under every iterate of $f$. This follows by induction on the number of iterations: it is immediate at zero, and the preservation hypothesis for one application combines with the induction hypothesis at the successor step. Now induct on $j$ for the length estimate. At zero it is equality. At the successor step, apply the one-step length bound to the current iterate. The invariance just proved replaces its decoded-component length by the initial one, so this step adds at most the fixed quantity $A(|\pi_1(d)|+1)$. The induction bound for the preceding iterate then gives $|d|+(j+1)A(|\pi_1(d)|+1)$.
