<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arDecode_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Symbol

**Claim.** Decoding the code of any optional symbol $a$ returns $a$.

**Proof.** The decoder is defined as a left inverse of the injective encoding. Therefore, when its input is the code $E(a)$ of an optional symbol, it returns $a$ by the left-inverse property of an injective map.
