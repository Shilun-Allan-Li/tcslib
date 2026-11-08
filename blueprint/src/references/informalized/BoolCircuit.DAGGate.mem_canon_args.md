<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGGate.mem_canon_args -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument Membership Under Canonicalization

**Claim.** An index occurs among the arguments of the canonical form of a gate exactly when it occurs among the arguments of the original gate.

**Proof.** By the definition of canonicalization, its argument list consists of the indices in the range from zero through the folded maximum, filtered to retain those already in the original argument list. Thus membership in the canonical list entails membership in the original list. Conversely, if $a$ occurs in the original list, the bound on a list element by its folded maximum (`le_foldr_max`) gives $a\leq$ that maximum. Hence $a$ lies in the specified range and passes the membership filter, so it occurs in the canonical list.

**Key facts.** `BoolCircuit.DAGGate.le_foldr_max`.
