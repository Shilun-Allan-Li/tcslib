<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_table_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Next Tape Cell

**Claim.** The tape storing $l$ followed by $b$ and then $r$ contains $b$ at the integer position $|l|$.

**Proof.** At the nonnegative position $|l|$, the tape lookup is the list lookup at natural index $|l|$ (`bufferTape_nat`). In the concatenation $l ++ (b :: r)$, this index lies just past the prefix $l$, so the lookup returns the first element of $b :: r$, namely $b$.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
