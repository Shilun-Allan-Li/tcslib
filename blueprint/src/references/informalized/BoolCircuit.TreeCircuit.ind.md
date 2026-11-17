<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.ind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structural Induction for Boolean Circuits

**Claim.** If a property holds for every literal circuit, and holds for a gate node whenever it holds for every child in that node's list, then it holds for every circuit tree.

**Proof.** Use structural recursion on circuit trees, strengthening the recursive motive to cover lists of children: for a list, every member satisfies the property. In the literal case, the assumed literal property proves the claim. In the node case, the strengthened induction hypothesis establishes the property for every child in the node's list, so the assumed node property applies. The list part of the strengthened motive follows by list induction: membership in a cons list is either membership of its head, handled by the head hypothesis, or membership in the tail, handled by the tail hypothesis. Thus the strengthened induction yields the desired property for every tree.
