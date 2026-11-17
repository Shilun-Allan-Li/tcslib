<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.blockFirstLayer_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the first DNF layer

**Claim.** For every $m\ge7$, the DNF formula whose terms are the first block layer has width $2m$.

**Proof.** For the upper bound, every term in the first layer is a block minterm, and each such minterm has width $2m$ by `FABL.width_blockMinterm`. The characterization of formula width as the maximum term width (`FABL.DNFFormula.width_le_iff`) therefore gives width at most $2m$. For the reverse inequality, the layer has positive size, so choose its term at index zero. It belongs to the layer, and every term in the layer has width at most the formula width by `FABL.DNFFormula.width_le_of_mem`. This chosen term is a block minterm and thus has width $2m$; consequently the formula width is at least $2m$.

**Key facts.** `FABL.DNFFormula.width_le_iff`, `FABL.width_blockMinterm`, `FABL.length_blockFirstLayer`, `FABL.DNFFormula.width_le_of_mem`.
