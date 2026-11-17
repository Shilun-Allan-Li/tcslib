<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.main_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting simulation on a delimited word

**Claim.** For an encoded delimited word and an invariant abstract state, the circuit-evaluation machine halts with output equal to the recursive abstract value, within $(|l|+1)(2B+4)$ steps whenever $|s.\mathrm{vals}|+|l|\le B$.

**Proof.** Induct on the list $l$. If $l$ is empty, the delimiter is the next input pair. The bounded update theorem (`macro_step`) applies to this pair; the empty-word abstract step produces a Boolean value (`absStep_none`). Thus the machine halts with the same value as the empty recursive run, within the claimed bound.

For $l=b::l'$, the next encoded pair is $(b,b)$, whose pair symbol is the singleton containing $b$. Apply `macro_step`. If this abstract update returns a successor state, it preserves the invariant and grows the value list by at most one. The input decomposition can then be rewritten with the prefix extended by the pair $(b,b)$, so the induction hypothesis applies to $l'$. Concatenate the first simulation segment and the inductive run using `Turing.MultiTapeTM.runFrom_add`. The condition on $B$ bounds the value-list length at the recursive call, and the two segment bounds combine to at most $(|l|+1)(2B+4)$. The recursive output agrees with the abstract run on $b::l'$ by its defining equation. If instead the first abstract update already returns a Boolean, `macro_step` gives a halting configuration with that output, and the defining equation for the recursive abstract run identifies it as the required value. Its time bound is no larger than the claimed total bound. In both cases the machine halts with the specified singleton output.

**Key facts.** `BoolCircuit.CircuitEval.absStep_none`, `BoolCircuit.CircuitEval.macro_step`, `Turing.MultiTapeTM.runFrom_add`.
