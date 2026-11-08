<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_good_quad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fields of a padded quadruple

**Claim.** If the certificate word has length one more than the encoded quadruple, then appending it to that quadruple produces a valid input whose extracted fields are exactly the specified code, input, width, clock, and certificate.

**Proof.** Let $y$ be the encoded quadruple. The split-append property (Complexity.tmsat_split_append) says that splitting $y$ followed by a word $w$ of length $|y|+1$ recovers the pair encoding of $y$ and $w$. The decoder exactly inverts pair encoding (Turing.pairDecode_pairEncode), so the extracted instance and certificate are $y$ and $w$. Apply the same decoding identity successively to the nested pair encodings defining $y$: this recovers $\alpha$, $x$, and the two unary words. The unary words have lengths $n$ and $t$ by construction, and their all-ones form makes both unary validity checks hold. Thus every parsing and unary check in the validity guard succeeds, and all the stated fields have the required values.

**Key facts.** `Complexity.tmsat_split_append`, `Turing.pairDecode_pairEncode`.
