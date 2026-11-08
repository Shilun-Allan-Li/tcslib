<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.length_embedGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Embedded Gates

**Claim.** For a directed acyclic circuit $D$, the list formed by embedding its gates has length equal to the number of gates of $D$ plus one.

**Proof.** The embedded list is the map of the gates of $D$, with each gate remapped and its arguments deduplicated, followed by one additional gate. Mapping preserves list length, and appending a singleton adds one. Thus the length is $|D.\mathrm{gates}|+1$.
