<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.padSrcs_map_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding Preserves the Mapped Prefix

**Claim.** Mapping $f$ over the padded list and taking its first $|l|$ entries gives exactly the list obtained by mapping $f$ over $l$.

**Proof.** By definition, padding appends a list of false constants to $l$. Mapping $f$ over this concatenation gives the mapped list $l.map\,f$ followed by the mapped padding. Since the first list has length $|l|$, taking that many entries returns exactly $l.map\,f$.
