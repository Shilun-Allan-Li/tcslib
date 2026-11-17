<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.accFin_foldl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folded gate evaluation

**Claim.** For every gate kind and argument list, the accumulator fold from its prescribed initial value, followed by the gate’s final adjustment, equals the gate’s value on those arguments, with out-of-range indices read as false.

**Proof.** First observe that folding Boolean conjunction over a list, starting from a Boolean $b$, gives $b$ conjoined with the conjunction of the list’s mapped values. The analogous statement holds for disjunction. For an AND gate, the initial accumulator is true, each argument combines by conjunction, and the final adjustment leaves the result unchanged; the fold identity therefore gives the conjunction of the values at all argument indices. For an OR gate, the initial accumulator is false and the same reasoning with disjunction gives their disjunction. For a NOT gate, the accumulator fold is the conjunction of the argument values, and the final adjustment negates it, exactly as in the gate’s definition. In each case, the mapped values use the convention that an out-of-range lookup is false.
