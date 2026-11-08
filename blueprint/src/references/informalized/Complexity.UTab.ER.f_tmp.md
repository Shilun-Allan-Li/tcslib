<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_tmp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch register lookup

**Claim.** For any register state $e$, reading its scratch coordinate returns the scratch value stored in $e$.

**Proof.** The scratch coordinate is $10$, and the register lookup function returns $e.tmp$ there. Since $rTMP=10$, reading this coordinate gives $e.tmp$.
