<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.dc_distinct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Decode Registers

**Claim.** For each decode identifier, the pointer, base, accumulator, and temporary registers are pairwise distinct in the specified order.

**Proof.** The identifier has three possible values, $S$, $\mathrm{Pos}$, and $\mathrm{Pos2}$. In each case, the definitions assign these four roles explicit register indices; comparing those indices gives all six required inequalities.
