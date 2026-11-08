<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterToken_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Token and Remainder Lengths

**Claim.** For every Boolean word $x$, the length of its leading unary token plus the length of its remainder is $|x|$.

**Proof.** Induct on $x$. The empty word has empty token and remainder, so the equality holds. For a word beginning with false, the split returns a one-bit token and the rest of the word as remainder, and their lengths sum to the original length. For a word beginning with true, the split prepends that true bit to the token obtained by splitting the tail, while leaving the tail's remainder unchanged. The induction hypothesis gives the length equality for the tail; adding one to the token length gives the required equality for the whole word.
