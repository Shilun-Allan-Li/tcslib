<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.layer1RestrictedWidth_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted width bounded by maximum

**Claim.** For any coordinate restriction and any indexed first-layer gate, that gate’s restricted width is at most the maximum restricted width among all first-layer gates.

**Proof.** The indexed gate belongs to the finite set of all first-layer indices. The supremum of the restricted widths over that set is therefore at least the value at this index, which is precisely the asserted inequality.
