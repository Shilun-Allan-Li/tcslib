<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.ofFn_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from indexed values

**Claim.** If a Boolean list $l$ has length $a$, then the list formed from its indexed values, using false as the default, is exactly $l$.

**Proof.** Both lists have length $a$. To compare their entries, take any index $i<a$. At that index, the value in the constructed list is the defaulted lookup of $l$ at $i$. Since $i$ lies within the length of $l$, this lookup is the actual $i$th entry of $l$. Thus the lists have equal lengths and agree at every valid index, so they are equal.
