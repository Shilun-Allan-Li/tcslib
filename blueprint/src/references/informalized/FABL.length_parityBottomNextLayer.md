<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.length_parityBottomNextLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bottom Next Layer Length

**Claim.** For all natural numbers $n$, $r$, and $q$, the bottom next layer has length $r^q 2^r$.

**Proof.** The bottom next layer enumerates one node-input set for each index in the finite type of size $\text{parityLayerSize}(r,q)$. Enumerating a function over that finite index type produces a list with exactly that many entries. By the definition of the layer size, this is $r^q 2^r$.
