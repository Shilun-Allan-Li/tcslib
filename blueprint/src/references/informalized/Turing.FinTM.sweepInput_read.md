<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepInput_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correct Decoding of the Scanned Input

**Claim.** When the encoded configuration’s input-head position is the transported position of the original configuration’s head, decoding its scanned symbol returns exactly the symbol scanned in the original configuration.

**Proof.** The transport of an input-head position preserves its numerical value, and it is at the left boundary exactly when the original position is at the left boundary. The encoded input also has the same length as the original input, since it is formed by mapping the encoding over each symbol. Consequently, both configurations agree on whether the head is at either boundary; at either boundary, both scanned-symbol results are blank. If the head is interior, the encoded input’s symbol at that position is the encoding of the original symbol there. The decoding map returns that original symbol, as required.
