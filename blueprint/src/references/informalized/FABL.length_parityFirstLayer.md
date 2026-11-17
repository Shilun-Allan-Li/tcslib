<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.length_parityFirstLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Parity Layer Length

**Claim.** For all natural numbers $n$, $r$, and $q$, the first parity layer has length $r^q 2^r$.

**Proof.** The first parity layer enumerates one term for each index in the finite type of size $\text{parityLayerSize}(r,q)$. The enumeration therefore has exactly that many entries, regardless of the terms assigned to the indices. Substituting the definition of the layer size gives $r^q 2^r$.
