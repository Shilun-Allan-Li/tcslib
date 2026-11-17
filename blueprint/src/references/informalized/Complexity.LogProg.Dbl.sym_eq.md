<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.sym_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator symbol in a unary pair encoding

**Claim.** In the pair encoding of $n$ ones and $w$, the symbol at zero-based position $2n$ is false.

**Proof.** Rewrite the pair encoding as the doubled first word followed by the separator and then $w$ (`pairEncode_eq_dbl`). Doubling a word of $n$ true bits gives a word of $2n$ true bits (`dbl_replicate`). Thus position $2n$ is the first symbol of the appended separator, namely false.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
