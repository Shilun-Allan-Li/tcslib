<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_inc_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of increment procedures

**Claim.** For every Boolean word $s$, the recursively defined fixed-width increment and the certificate-enumeration increment have the same optional output.

**Proof.** Induct on the word. For the empty word, both definitions return no output. For a nonempty word, split on its first bit. If that bit is false, both procedures return the word with that bit changed to true and leave the rest unchanged. If it is true, both recursively increment the tail and, when that succeeds, prepend false to the result; when it fails, both return no output. The induction hypothesis identifies the recursive results, so the optional outputs agree in either case.
