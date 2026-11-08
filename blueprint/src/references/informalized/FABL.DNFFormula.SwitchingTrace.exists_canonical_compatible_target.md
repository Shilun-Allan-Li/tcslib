<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.SwitchingTrace.exists_canonical_compatible_target -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Compatible Target Term

**Claim.** For a switching trace based at a restriction, some canonical term arising from a nonempty set of compatible term indices at that restriction is compatible with the trace’s target restriction.

**Proof.** Apply the compatibility component of the established target theorem: it supplies a nonempty compatible-index set and proves that its canonical term remains compatible with the target. (The same theorem also establishes that the target extends the initial restriction, though that component is not needed here.)

**Key facts.** `FABL.DNFFormula.SwitchingTrace.target_extends_and_canonical_compatible`.
