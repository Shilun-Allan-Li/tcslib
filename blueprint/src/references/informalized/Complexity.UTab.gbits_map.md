<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.gbits_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a mapped gate list

**Claim.** For a finite list $l$ and a function $f$ assigning a gate to each element, the encoding of the mapped gate list is the concatenation, in list order, of one followed by the encoding of each $f(a)$.

**Proof.** By definition, the gate-list encoding concatenates, for each gate, one followed by its encoding. Applying this to the list obtained by mapping $f$ over $l$ gives one followed by the encoding of $f(a)$ for each element $a$, in the original order; the list mapping and concatenation combine directly into the stated flat concatenation.
