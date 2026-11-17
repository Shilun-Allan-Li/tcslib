<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairEncode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Pair Encoding

**Claim.** If two pairs of bit strings have the same pair encoding, then their first components agree and their second components agree.

**Proof.** Let the two pairs be $(x,\alpha)$ and $(y,\beta)$, and suppose their encodings are equal. Applying the decoder to both sides preserves equality. The decoding theorem says that decoding each encoded pair returns that pair, so the resulting equality is $\operatorname{some}(x,\alpha)=\operatorname{some}(y,\beta)$. Injectivity of the option constructor and equality of ordered pairs give $x=y$ and $\alpha=\beta$.

**Key facts.** `Turing.pairDecode_pairEncode`.
