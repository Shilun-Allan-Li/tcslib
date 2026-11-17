<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.length_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of an Encoded Unary Pair

**Claim.** If $y$ encodes the unary word $1^n$ paired with $w$, then $|y|=2n+2+|w|$.

**Proof.** The encoding can be written as the doubled first word, followed by the two-symbol separator and then the second word (`Turing.pairEncode_eq_dbl`). Doubling the unary word $1^n$ gives a unary word of length $2n$ (`Complexity.LogProg.dbl_replicate`). Adding the separator's length $2$ and the final word's length $|w|$ yields the formula.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
