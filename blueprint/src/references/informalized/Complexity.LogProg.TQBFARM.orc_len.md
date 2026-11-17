<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.orc_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle query for input length

**Claim.** On the encoded query consisting of $y$ and the binary representation of $a$, the second oracle returns true exactly when $a<|y|$.

**Proof.** The second oracle is the indicator of the language of encoded pairs whose index is less than the length of the first component. Applying the indicator identity `Complexity.indicator_inputLenLang` to this encoded query gives the Boolean decision of $a<|y|$.

**Key facts.** `Complexity.indicator_inputLenLang`.
