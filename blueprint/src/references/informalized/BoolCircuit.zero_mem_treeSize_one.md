<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.zero_mem_treeSize_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty language of tree size one

**Claim.** The empty language over the Boolean alphabet has tree size at most one: there is a family of Boolean tree circuits, one for each input length, each of size at most $1$, whose accepted language is empty.

**Proof.** Use the fact that the empty language has tree size bounded by any function $T$ that is everywhere at least $1$ ( `Language.zero_inTreeSize`). For the constant function $T(n)=1$, the required bound holds with equality at every input length. Thus the empty language belongs to the class of languages of tree size at most one.

**Key facts.** `Language.zero_inTreeSize`.
