<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.pe_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping the First Encoded Component

**Claim.** For any bit strings $u$ and $v$, dropping the first $2|u|+2$ bits of their self-delimiting pairing yields exactly $v$.

**Proof.** Rewrite the pairing as the doubled word for $u$, followed by the two-bit separator and then $v$ (`pairEncode_eq_dbl`). The doubled word has length $2|u|$, so the drop removes that word and the separator. The list drop-over-append rule then reduces the remaining suffix to $v$.

**Key facts.** `Turing.pairEncode_eq_dbl`.
