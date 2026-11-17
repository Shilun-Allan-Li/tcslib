<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTape_ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality from block coordinates

**Claim.** If two tapes agree at every position $(N+1)z+j$ for block positions $z$ and offsets $j$, then the tapes are equal.

**Proof.** Take any integer position $p$. Its quotient and remainder determine a block position $z$ and a valid offset $j$ for which $p=(N+1)z+j$ (`arPos_coords`). The assumed agreement at that block coordinate therefore gives equality of the two tapes at $p$. Since this holds for every integer position, the tapes are equal.

**Key facts.** `Turing.FinTM.arPos_coords`.
