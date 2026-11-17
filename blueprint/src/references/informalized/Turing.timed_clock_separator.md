<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cells of the inner separator

**Claim.** For every $r<4$, the entry at index $4|b_s|+r$ of the nested pair encoding equals the entry at index $r$ of the four-bit word $0011$.

**Proof.** Use the input-layout identity (`timed_input_layout`) to expose the clock prefix followed by the encoding of the remaining data. Induct on $b_s$. When it is empty, the four possible indices $r=0,1,2,3$ lie directly in the inner separator and give $0,0,1,1$. When a bit is added at the front, its clock-prefix contribution has length four, so the target index shifts by four; the induction hypothesis identifies the shifted entry with the same separator entry.

**Key facts.** `Turing.timed_input_layout`.
