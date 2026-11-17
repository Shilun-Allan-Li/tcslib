<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.QuadraticCircuitOutputSensitiveAdapter.semantic_eq_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantic output of the quadratic circuit adapter

**Claim.** For every Boolean circuit with a positive number of input bits, the semantic PCPP description produced by its output-sensitive adapter equals the canonical three-query PCPP description obtained from the quadratic circuit construction.

**Proof.** The adapter is, by definition, an output-sensitive adapter for the quadratic circuit construction, and its semantic agreement property states that for each such circuit its output-sensitive semantic description equals the three-query transformation of the quadratic construction. The canonical quadratic circuit reduction is that same transformation. Substituting this circuit into the adapter's semantic agreement property gives the asserted equality.
