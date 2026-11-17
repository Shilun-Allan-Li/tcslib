<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_read_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading Fixed Action Fields

**Claim.** When the table contains eight fixed action bits followed by a suffix, reading the remaining fields from field $f$ takes $n+1$ steps and leaves the interpreter in successor decoding with the register equal to those eight bits and cursor at $|l|+8$.

**Proof.** Induct on the number $n$ of fields remaining after the current one, with $f+n=7$. At the current cursor, the table lookup is the bit in field $f$: the natural-index lookup for the buffer tape identifies it with the corresponding list entry (`Turing.FinTM.bufferTape_nat`). If $n=0$, then $f=7$. Reading this last bit updates the register at field $7$; the hypothesis says all earlier fields already agree with the table, so the updated register is the full eight-bit register. The transition enters successor decoding and advances the cursor to $|l|+8$. The one-step run interpretation justifies this transition (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`). If $n>0$, then $f<7$. The interpreter reads the current bit, updates that register field, and moves right to field $f+1$. Every register entry below $f+1$ now agrees with the table: the new field was just set, and all earlier ones agreed by hypothesis. Apply the induction hypothesis to the remaining fields. The total cursor advance and register contents are then as claimed.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`.
