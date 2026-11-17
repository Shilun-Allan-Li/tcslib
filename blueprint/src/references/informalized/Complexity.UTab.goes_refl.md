<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.goes_refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of the Run Relation

**Claim.** For any counter program with eleven registers, input, label, register assignment, and input position, the run relation holds from that label and assignment back to themselves, with unchanged position, no additional output, and step bound zero.

**Proof.** For any prior output list $o$, choose a run length of zero. By the zero-run identity (`run_zero`), running for zero steps leaves the entire initial configuration unchanged. Since appending the empty list leaves $o$ unchanged, this is exactly the required final configuration, and the chosen run length is at most zero.

**Key facts.** `Complexity.CounterProg.run_zero`.
