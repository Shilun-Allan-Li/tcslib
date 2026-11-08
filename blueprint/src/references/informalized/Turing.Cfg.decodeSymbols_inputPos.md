<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.decodeSymbols_inputPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input head preserved by decoding

**Claim.** Decoding a configuration’s symbols leaves its input-head position unchanged.

**Proof.** In the definition of decoding, the input-head position is the original position transported across the equality of the two input lengths. This transport does not change the underlying natural-number value, so the decoded configuration has the same input-head position as the original.
