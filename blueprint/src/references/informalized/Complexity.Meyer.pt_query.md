<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query formation

**Claim.** For fixed $b$ and polynomial-time computable $T,A,X$, the function forming the concatenation of $b$, the doubled-bit encoding of $T(z)$, the separator $00$, the similarly encoded $A(z)$, another separator $00$, and $X(z)$ is polynomial-time computable.

**Proof.** First use the pair-encoding identity for the finite-state transduction: applying $fT$ to the pair encoding of two words produces the doubled-bit encoding of the first word, followed by $00$ and the second word (Complexity.Meyer.fT_pairEncode). Thus the desired output can be written as the fixed prefix $b$ followed by $fT$ applied to the pair encoding of $T(z)$ and the result of applying $fT$ to the pair encoding of $A(z)$ and $X(z)$. Starting with $X$, polynomial-time closure under pair encoding combines it with $A$; closure under composition with $fT$ then forms the inner encoded segment. Pair encoding with $T$ and another application of $fT$ form the outer segment. The transduction $fT$ is polynomial-time computable (Complexity.Meyer.pt_fT), so these composition and pair-encoding closure results show that the variable suffix is polynomial-time computable. Finally, prepending a fixed word preserves polynomial-time computability (Complexity.polyTimeComputable_prepend), giving the claim.

**Key facts.** `Complexity.Meyer.fT_pairEncode`, `Complexity.Meyer.pt_fT`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_prepend`.
