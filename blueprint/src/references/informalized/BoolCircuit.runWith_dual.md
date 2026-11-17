<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.runWith_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of gate execution

**Claim.** Executing the circuit with AND and OR interchanged, from the entrywise negation of the initial list, gives the entrywise negation of the original execution.

**Proof.** Proceed by induction on the gate list, allowing the initial list to vary. For an empty list the claim is immediate. For a first gate $g$, the execution rule says to append its output and then execute the remaining gates. Every argument of $g$ is in range by the hypothesis at position zero. The gate duality fact (`DAGGate.eval_dual`) therefore says that the dual gate, evaluated on the negated initial list, produces the negation of $g$’s output. Thus the two lists after this first step are entrywise negations of one another. Apply the induction hypothesis to the remaining gates with these extended lists. Their argument bound follows from the original bound at position $i+1$, since the initial list has gained one entry; the NOT-gate arity condition is inherited by the tail. This proves the result.

**Key facts.** `BoolCircuit.runWith_cons`, `BoolCircuit.DAGGate.eval_dual`.
