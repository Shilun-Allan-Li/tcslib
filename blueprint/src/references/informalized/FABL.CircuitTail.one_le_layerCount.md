<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.CircuitTail.one_le_layerCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every Tail Has a Layer

**Claim.** Every circuit tail has at least one layer.

**Proof.** Split into the two possible forms of a circuit tail. An output tail has layer count $1$. A layered tail has layer count $1$ plus the layer count of its remaining tail, which is a natural number and hence nonnegative. In either case the count is at least $1$.
