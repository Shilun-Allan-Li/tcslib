<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.drop_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix after Pair Encoding

**Claim.** For any two finite bit strings $u$ and $w$, deleting the first $2|u|+2$ bits from their pair encoding leaves exactly $w$.

**Proof.** Rewrite the pair encoding as the doubled word $\mathrm{dbl}(u)$, followed by the two-bit separator and then $w$ (`Turing.pairEncode_eq_dbl`). The doubled word has length $2|u|$, so dropping $2|u|+2$ bits removes precisely that word and the separator. The remaining suffix is $w$.

**Key facts.** `Turing.pairEncode_eq_dbl`.
