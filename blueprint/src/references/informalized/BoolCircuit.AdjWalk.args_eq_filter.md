<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.args_eq_filter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtering the Sorted Gate Arguments

**Claim.** If the gate's argument list is strictly increasing and every argument is less than $V$, filtering $0,1,\ldots,V-1$ to retain its arguments returns exactly that list.

**Proof.** The filtered list and the gate's argument list contain exactly the same elements: every retained index is, by definition, an argument, and every argument lies in the interval from $0$ to $V-1$ by the bound hypothesis. Both lists have no repetitions, since the interval has no repetitions and the argument list is strictly increasing. Thus the lists are permutations of one another. The filtered interval is strictly increasing, as is the argument list; uniqueness of a sorted list within a permutation class then gives equality.
