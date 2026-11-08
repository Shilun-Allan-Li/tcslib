<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitTail.layerCount_castInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Count Under Reindexing

**Claim.** If $m=k$, identifying the input indices of a circuit tail with those of $k$ leaves its layer count unchanged.

**Proof.** Since $h$ identifies $m$ with $k$, substitute $k=m$. The cast of the tail is then the tail itself, so both sides are its layer count and the equality is reflexive.
