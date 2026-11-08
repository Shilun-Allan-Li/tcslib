<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.correct_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness at the Initial Time

**Claim.** If all local checks pass and $x_b$ agrees with the input at every valid input index, then at time zero the encoded state and output, work tape, and input tape agree with the machine's initial configuration on the stated ranges.

**Proof.** For the state and output component, apply the initial-state check at time and address zero. Its equality forces every queried state/register pair to match the machine's initial pair; the zero-step run is the initial configuration (`runFrom_zero`), whose summary is that pair (`SS_init`). For a work tape and offset $d$, the initial-work checks determine both Boolean answers for the selected sign and address to be the encoding of a blank symbol. Decoding those two answers recovers `none` (`decode_symBit`), which is exactly the initial work-tape content (`RW_init`); again the zero-step run is the initial configuration.

For an input offset $d$, the initial-input checks similarly determine the two answers to encode the symbol represented by the input-boundary convention: it is blank outside the input and is the corresponding bit of $x_b$ inside. The assumption on $x_b$ identifies those bits with the entries of $x$, so this decoded symbol is the initial input symbol (`xin_eq`). The initial input-symbol query is the input tape at offset $d$ (`RI_init`), and the run at time zero is the initial configuration (`runFrom_zero`).

**Key facts.** `Complexity.Meyer.NumVal_ans`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.Meyer.SS_init`, `Complexity.Meyer.decode_symBit`, `Complexity.Meyer.RW_init`, `Complexity.Meyer.xin_eq`, `Complexity.Meyer.RI_init`.
