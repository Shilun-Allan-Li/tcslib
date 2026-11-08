<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessCheck_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing Successful Access Checks

**Claim.** If checking $y$ against $k$ returns `some b`, then $y$ is the encoding of some bit string $z$ paired with the binary representation of a natural number $r$, and $b$ is true exactly when $r=k$.

**Proof.** Decode $y$. If decoding fails, the access check is empty, contrary to the hypothesis. Thus it decodes as a pair $(z,w)$. For the check to return a value, the second component $w$ must be canonical. The canonical-word characterization says $w$ is the binary representation of its value (`Complexity.LogProg.canon_eq_bits`); let that value be $r$. The decoder's reconstruction property (`Turing.eq_pairEncode_of_pairDecode`) then shows that $y$ is the encoding of $z$ and $w$, hence of $z$ paired with the binary representation of $r$. By the definition of the access check, $b$ records whether $w$ equals the binary representation of $k$. Injectivity of binary representation (`Complexity.LogProg.bits_injective`) identifies this test with whether $r=k$.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.bits_injective`.
