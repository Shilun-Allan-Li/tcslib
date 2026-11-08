<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.ACLevel_subset_NCLevel_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alternating circuit class inclusion

**Claim.** Every language in the depth-$i$ alternating circuit class belongs to the fan-in-two circuit class at depth level $i+1$.

**Proof.** Let $L$ be any language in the depth-$i$ alternating circuit class. The inclusion theorem for these classes (`Language.InAC.inNC_succ`) says that membership at level $d$ implies membership in the fan-in-two class at level $d+1$. Apply it with $d=i$ to obtain the required membership, and hence the set inclusion.

**Key facts.** `Language.InAC.inNC_succ`.
