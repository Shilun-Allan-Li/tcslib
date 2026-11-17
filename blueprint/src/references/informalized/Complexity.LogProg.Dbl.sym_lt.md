<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.sym_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary prefix of a pair encoding

**Claim.** Every symbol at a zero-based position $k<2n$ in the pair encoding of $n$ ones and $w$ is true.

**Proof.** Rewrite the pair encoding as the doubled first word followed by the separator and $w$ (`pairEncode_eq_dbl`). The doubled word of $n$ ones is a word of $2n$ ones (`dbl_replicate`), and the assumption $k<2n$ places the indexed symbol inside that prefix. Hence the symbol at position $k$ is true.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
