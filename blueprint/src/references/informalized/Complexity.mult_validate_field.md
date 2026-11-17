<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_validate_field -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Field Validation

**Claim.** Under the stated transition, last-bit, failure, and success hypotheses, the run from the field-test state halts with the specified answer while maintaining the safety conditions before halting.

**Proof.** The starting configuration is safe by the program-state precondition lemma (`mult_preconditions`). The stipulated first step either skips directly to the next validation state when $w$ is empty, or enters the field-clearing state. In the empty case, the word is canonical, so the success hypothesis applies to the unchanged bounded register assignment and gives the required halt.

For nonempty $w$, the program clears register $0$ and reads the bit at the designated source position. The last-bit reachability lemma (`mult_last_bit`) carries out this scan, and the assumed equality identifies the read bit with the last bit of $w$. The canonical-last-bit characterization (`mult_canonical_last`) says that, for a nonempty word, canonicity is equivalent to this bit being true. If it is true, the program continues in the next validation state with register $0$ updated to the read position. The update bound (`register_update_le`) shows this assignment remains bounded, and it agrees with the original assignment on every other register, so the success hypothesis yields the specified halt. If the bit is false, the word is noncanonical; the failure hypothesis makes the answer false, and the program returns false using `mult_return`. In each branch, composing the scan or first step with the later halting run preserves safety along the entire run.

**Key facts.** `Complexity.mult_preconditions`, `Complexity.LogProg.AHalt.step`, `Complexity.mult_last_bit`, `Complexity.mult_canonical_last`, `Complexity.LogProg.register_update_le`, `Complexity.mult_return`, `Complexity.LogProg.AReach.halt`.
