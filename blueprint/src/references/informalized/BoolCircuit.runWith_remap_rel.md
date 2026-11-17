<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_remap_rel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relation Under Gate Remapping

**Claim.** Under the stated hypotheses on the input relation, index map, initial lists, and gate arguments, each output of the original circuit is related to the corresponding remapped output.

**Proof.** Use induction by appending the gates one at a time, so the induction hypothesis describes the relation between all existing output positions before the next gate is evaluated. For the empty list, every index in the required range is an initial index; the initial relation hypothesis gives the result.

Now write a nonempty list as an earlier list followed by a final gate $g$. The position hypotheses restrict to the earlier list, while the final gate's arguments are all among the indices available before it is added. The induction hypothesis therefore relates the two evaluations at every earlier position. The length formula gives lengths $L+|old|$ and $L'+|old|$ for the two current output lists. For an index below $L+|old|$, its image under $\sigma$ lies below $L'+|old|$: this follows from the bound on $\sigma$ for initial indices, and from the stipulated shift of the new gate indices for later ones. Consequently, both readings at such a position select the existing outputs, and the induction hypothesis supplies their relation.

It remains to consider the new final position, $L+|old|$. Its image is $L'+|old|$ by the shift condition. Reading these positions in the lists after adding the final gate selects precisely the two newly appended gate outputs. For each argument of $g$, the argument bound places it among the indices covered by the induction hypothesis, so the remapped and original input values are related. The gate compatibility hypothesis then relates the two outputs. This proves the claim at the new position as well.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_singleton`.
