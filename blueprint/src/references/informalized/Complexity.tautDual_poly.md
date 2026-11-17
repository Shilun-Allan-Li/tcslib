<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Dualization

**Claim.** The function sending a binary string to the encoding of the De Morgan dual of its decoded CNF formula, as a DNF formula, is computable in polynomial time.

**Proof.** Take a machine that outputs the constant empty word in linear time, and use it to supply the time bound needed by the emit-and-loop construction. With the dual transducer as the loop body, the invariant records that the work state is empty and the emitted word is empty between rounds. The round theorem supplies, for every input, a positive-length run of at most $4|x|+5$ steps that returns to the anchor, avoids it at earlier times, and emits the guarded dual output. Thus the construction theorem gives a machine computing that output within a polynomial bound. By the guarded-output identity, this output is exactly the encoding of the dual of the decoded CNF formula. Finally, the proof enlarges the bound to a constant multiple of $(|x|+1)$, which has the required polynomial form with exponent one.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.exists_emitLoopTM`, `Complexity.tautDual_round`, `Complexity.tautDual_output`, `Turing.FinTM.ComputesInTime.mono`.
