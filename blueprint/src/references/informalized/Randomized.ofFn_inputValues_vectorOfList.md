<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.ofFn_inputValues_vectorOfList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List of Evaluated Wire Values

**Claim.** Evaluating each wire in a finite list using the given input assignment and constant values produces the list obtained by applying the wire evaluation to every element of the original list.

**Proof.** First, evaluating the function-valued list entry by entry and then forming the list gives the same list as applying the evaluation map to the list of entries. Indeed, at each index, the wire is either an input position, in which case both constructions return its assigned input value, or a Boolean constant, in which case both return that constant. The list of entries represented by the function obtained from the original list is exactly the original list, by the list-vector reconstruction identity (`BoolCircuit.vectorOfList_ofFn`). Substituting this identity gives the claimed equality.

**Key facts.** `BoolCircuit.vectorOfList_ofFn`.
