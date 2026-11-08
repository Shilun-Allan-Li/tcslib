<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPairCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol in the pairing configuration

**Claim.** In the canonical pairing configuration, the input head at position $i$ scans $x[i]?$, independently of the captured word, administrative state, offset, and output.

**Proof.** The pairing configuration is built with input position $i+1$, while input positions are shifted by one in the machine’s representation. The input-symbol calculation for a configuration at position $i+1$ gives exactly the list lookup $x[i]?$. Applying that fact to the canonical configuration proves the claim; the other fields do not affect its input position.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
