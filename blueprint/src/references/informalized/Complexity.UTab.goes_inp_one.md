<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_inp_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Input Position

**Claim.** Under the stated register, phase-source, and layout-source hypotheses, one execution of the input-position instruction emits the prescribed instruction bits, advances the instruction position by one, updates the preceding-cell register as specified, and reaches the phase’s successor label within $L_{\max}(M)+3$ steps.

**Proof.** First, when $t\ne 0$, the formula for the input index and the bound $t\ge 1$ imply that the current instruction position is at least one layer stride. Thus the preceding-cell register, which is the current position minus that stride, has the required form. Apply the general execution result for a template whose successor is its input-processing phase (`goes_instr_inv`): it advances the instruction position, updates the preceding-cell register, and emits the template’s operation list. The input-template bit calculation (`inp_bits`) identifies that operation list with the encoded bits prescribed by the position, phase-source, and layout-source hypotheses. Rewriting the general result with this identification gives the claim and its step bound.

**Key facts.** `Complexity.UTab.goes_instr_inv`, `Complexity.UTab.inp_bits`.
