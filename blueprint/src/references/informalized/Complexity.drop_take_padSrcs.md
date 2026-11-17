<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.drop_take_padSrcs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping and taking padded sources

**Claim.** Mapping $f$ over the padded concatenation of $\mathrm{pre}$ and $\mathrm{rest}$, then dropping $|\mathrm{pre}|$ entries and taking $|\mathrm{rest}|$ entries, gives $\mathrm{rest}$ mapped by $f$.

**Proof.** Expanding the padding and distributing the map over concatenation writes the mapped list as the mapped prefix, followed by the mapped rest, followed by the mapped padding. The first part has length $|\mathrm{pre}|$, since mapping preserves list length. Dropping that many entries therefore leaves the mapped rest followed by the mapped padding; taking $|\mathrm{rest}|$ entries selects exactly the mapped rest.
