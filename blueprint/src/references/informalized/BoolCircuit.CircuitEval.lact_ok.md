<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.lact_ok -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of phase actions

**Claim.** For a main phase, the prescribed local action satisfies all the stated write, output, movement, and next-state conditions.

**Proof.** Unfold the definitions of the local action, its validity predicate, the main-phase predicate, and the walking-phase predicate, and split on the phase and the optional scanned symbols. In the two initial scan phases, the hypothesis that the phase is main rules out the cases that would violate the stated conditions. For the remaining phases, inspect the prescribed action in each possible symbol case: rejection halts with an output symbol; ordinary transitions enter a main read phase with no output and the permitted head movement; transitions entering a value rewind have a present value, move left, and enter a nonwalking main phase; and append transitions do not move or mark and arise only outside walking phases. The remaining unmatched cases reject, so they satisfy the halting clause. These case checks establish each conjunct of the validity predicate.
