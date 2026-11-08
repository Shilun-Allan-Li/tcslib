<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.length_prodOnePlusGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the product circuit

**Claim.** For every natural number $k$, the recursively constructed gate list has length exactly $3k+1$.

**Proof.** Induct on $k$. At $k=0$, the list consists of the single constant gate, so its length is $1$. At the successor step, the construction appends three gates to the list for $k$. By the induction hypothesis its length is therefore $(3k+1)+3$, which rearranges to $3(k+1)+1$.
