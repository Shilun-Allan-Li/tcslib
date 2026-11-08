<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning a designated answer

**Claim.** From the answer state labelled by $b$, with registers within the stated bound and no answer yet recorded, the machine halts with answer $b$.

**Proof.** The answer state executes a return instruction carrying the same Boolean value $b$. Its machine precondition holds by the general precondition lemma, and the register-bound assumption supplies the other required invariant. The return-state halting fact then gives termination with answer $b` (`AHalt.ret`).

**Key facts.** `Complexity.mult_preconditions`, `Complexity.LogProg.AHalt.ret`.
