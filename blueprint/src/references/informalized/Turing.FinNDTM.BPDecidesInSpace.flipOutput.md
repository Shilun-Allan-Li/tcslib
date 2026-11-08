<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.BPDecidesInSpace.flipOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementing Bounded-Error Decisions

**Claim.** Complementing every output bit preserves the space bound and halting guarantee and makes the machine decide the complement language with the same probability threshold.

**Proof.** The flipped machine uses the same work-tape head positions along each choice word, so its space usage agrees with the original machine’s (`Turing.NDTM.flipOutput_initCfg`, `Turing.NDTM.flipOutput_spaceUsedWith`). For each input, take the time bound supplied for the original decision. The flipped machine halts within that bound because output flipping preserves halting (`Turing.FinNDTM.flipOutput_haltsWithin_iff`). The complement-language indicator is the bitwise complement of the original indicator: this follows by considering whether the input belongs to the language. On each choice word, the flipped output is the original output with every bit complemented (`Turing.FinNDTM.flipOutput_outputWith`). Since complementing bits is injective, the flipped machine outputs the complement-language indicator exactly when the original outputs the original indicator. Thus these events have equal probability (`Randomized.randProb_congr`), and the original lower bound of $2/3$ carries over.

**Key facts.** `Turing.NDTM.flipOutput_initCfg`, `Turing.NDTM.flipOutput_spaceUsedWith`, `Turing.FinNDTM.flipOutput_haltsWithin_iff`, `Turing.FinNDTM.flipOutput_outputWith`, `Randomized.randProb_congr`.
