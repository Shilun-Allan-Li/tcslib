<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.field_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of reading a field

**Claim.** When reading a field from the suffix succeeds with payload $w$ and remainder $r$, the tabulating machine consumes exactly $2|w|+2$ steps and reaches the stated configuration, appending the payload to the appropriate auxiliary word according to the flag.

**Proof.** Induct on the structure of the suffix that successfully encodes the field. In the continuation case, the suffix begins with a bit $b$ and then true. The decoding equation says that the tail after these two bits encodes a shorter payload $w'$ and remainder $r'$, so $w=b::w'$. The lookup-after-dropping fact (getElem?_of_drop) identifies the two input bits read at the current position. The transition descriptions show that these two steps return the machine to its field-reading state at the start of the shorter suffix, with $b$ appended to the auxiliary word selected by the flag (pcfg_fA and pcfg_fB_true). Apply the induction hypothesis there. The two initial steps plus the recursive $2|w'|+2$ steps total $2|w|+2$, and the final auxiliary words are exactly those obtained by appending the full payload $w$ to the selected word.

In the terminating case, the suffix begins with a bit followed by false, so the payload is empty and the remainder is the tail after this marker. The two transitions read this pair and place the machine in the designated next state, with no change to either auxiliary word (pcfg_fA and pcfg_fB_false). This is the required configuration after $2|w|+2=2$ steps. Empty or one-bit suffixes cannot yield a successful field decoding, so they are ruled out by the decoding hypothesis. In every case, the original work tapes remain blank and the output stays empty, as recorded in the configuration transitions.

**Key facts.** `Complexity.Meyer.getElem?_of_drop`, `Complexity.Meyer.pcfg_fA`, `Complexity.Meyer.pcfg_fB_true`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.Meyer.pcfg_fB_false`, `Turing.MultiTapeTM.runFrom_zero`.
