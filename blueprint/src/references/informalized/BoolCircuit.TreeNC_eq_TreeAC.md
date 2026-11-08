<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.TreeNC_eq_TreeAC -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Tree Circuit Classes

**Claim.** The union of the tree-circuit classes with fan-in at most two and polylogarithmic depth of exponent at least one equals the union of the tree-circuit classes with unrestricted fan-in and polylogarithmic depth.

**Proof.** Fix a language $L$. By the characterizations of membership in the two unions (`BoolCircuit.mem_TreeNC_iff` and `BoolCircuit.mem_TreeAC_iff`), it suffices to prove both inclusions. If $L$ belongs to a fan-in-two level with exponent $i\ge 1$, the same circuit family, with the same size and depth bounds, witnesses membership in the unrestricted-fan-in level of exponent $i$: fan-in two is an additional restriction, so it can be discarded (`Language.InTreeNC.inTreeAC`). Conversely, suppose $L$ belongs to the unrestricted-fan-in level of exponent $i$. The fan-in reduction theorem upgrades its family to one with fan-in at most two and depth exponent $i+1$ (`Language.InTreeAC.inTreeNC_succ`). Since $i+1\ge 1$, this places $L$ in the first union. Thus the two unions have the same members.

**Key facts.** `BoolCircuit.mem_TreeNC_iff`, `BoolCircuit.mem_TreeAC_iff`, `Language.InTreeNC.inTreeAC`, `Language.InTreeAC.inTreeNC_succ`.
