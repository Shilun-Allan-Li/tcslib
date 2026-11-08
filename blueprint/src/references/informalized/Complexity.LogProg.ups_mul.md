<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ups_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Subroutine Semantics

**Claim.** Under the register bound and product bound, if every configuration at the multiplication site's exit state has acceptance probability $q$ for all permitted inner-counter values, then the multiplication site's entry configuration has acceptance probability $q$.

**Proof.** First clear the outer counter, preserving the register bound. The multiplication-loop correctness theorem (`psem_mul`) applies with the input register, the cleared outer counter, the inner counter, and the result register in their specified roles. Its loop compares the outer counter with the first factor; when they agree it exits, and otherwise it clears and advances the inner counter while accumulating the second factor into the result, thereby implementing repeated addition. The hypotheses that these registers are distinct, the first factor is no larger than the outer bound, and the final sum is bounded ensure the loop stays within the register bound. For each allowed inner-counter value, the assumed exit semantics supplies the theorem's exit condition: the nested register updates agree with the prescribed exit configuration because the multiplication registers are distinct from the outer and inner counters. Thus `psem_mul` gives probability $q$ after clearing the outer counter. Finally, the program's entry instruction is precisely that clear operation, so the semantics for the original entry state follows from the semantics-preservation rule for clearing a register (`PSem.clr`).

**Key facts.** `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.psem_mul`, `Complexity.LogProg.register_update_le`.
