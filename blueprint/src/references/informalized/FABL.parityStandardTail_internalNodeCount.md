<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityStandardTail_internalNodeCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Internal nodes in the parity circuit tail

**Claim.** For natural numbers $r$ and $q$ and either an AND or an OR gate, the number of internal nodes in the parity circuit tail is $\sum_{k=0}^{q-1} r^k2^r$, with the sum equal to zero when $q=0$.

**Proof.** Induct on $q$, keeping the output gate arbitrary. At $q=0$, the standard tail is an output layer, which has no internal nodes, and the sum over an empty range is zero. For the successor case, the tail adds one non-output layer containing exactly as many gates as the parity layer size at index $q$, and its remaining tail is the standard tail at index $q$ with the dual gate. By the induction hypothesis, that remainder contributes the sum over indices below $q$. The sum-range successor identity appends the new term $r^q2^r$, yielding the sum over indices below $q+1$.
