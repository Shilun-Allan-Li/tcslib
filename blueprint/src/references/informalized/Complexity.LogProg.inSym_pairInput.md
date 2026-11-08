<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.inSym_pairInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol in a paired encoding

**Claim.** At one-based input position $k+1$ in the encoding of the specified pair, the input symbol equals the symbol at index $k$ in the displayed concatenation.

**Proof.** The symbol at one-based position $k+1$ is, by the successor-position identity (`inSym_succ`), the element at index $k$ of the encoded word. Rewrite the pair encoding as the doubled first component followed by the separator and the second component (`pairEncode_eq_dbl`). The first component consists of $n$ ones, whose doubled word is $2n$ ones (`dbl_replicate`). Expanding the inner pair encoding then gives exactly the concatenation in the claim, so the indexed symbols agree.

**Key facts.** `Complexity.LogProg.inSym_succ`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
