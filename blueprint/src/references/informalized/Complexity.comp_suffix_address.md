<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_suffix_address -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing the Second Component

**Claim.** For $j<|b|$, the bit at position $4|x|+4+2j$ in the nested pair encoding is the bit of $b$ at position $j$.

**Proof.** The inner encoding of $x$ paired with $b$ has length $2|x|+2+|b|$ (`length_pairEncode`). In the outer encoding, positions below twice the inner length address the doubled inner word. The index $4|x|+4+2j$ is exactly twice the inner position $2|x|+2+j$, so the outer pair-encoding bit formula selects that inner bit (`pairEncode_getD`). Since $j<|b|$, the inner position lies in the suffix occupied by $b$; the suffix-addressing identity (`pairEncode_getD_snd`) therefore identifies it with $b_j$.

**Key facts.** `Turing.length_pairEncode`, `Complexity.pairEncode_getD`, `Complexity.pairEncode_getD_snd`.
