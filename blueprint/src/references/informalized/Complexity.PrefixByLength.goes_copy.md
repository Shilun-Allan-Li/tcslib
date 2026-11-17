<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Bit String

**Claim.** For either program parameter, every $n$ and bit string $r$, the program on input $r$ starting at its copy label with register value $n$ and input position $0$ halts with the register unchanged, position $|r|$, and output extended by $r$, in at most $2|r|+2$ steps. This holds for any output already printed.

**Proof.** Induct on the input string. For the empty string, the copy instruction reads the end of input and moves to stop; the next instruction halts. This takes two steps and leaves the position, register, and output suffix as claimed. For a string $b::r$, the copy instruction reads $b$, moves to the label that prints that bit, and advances the position to $1$. The next instruction prints $b$ and returns to copy. Meanwhile, apply the induction hypothesis to the remaining input $r$: prepend the already-consumed bit to that input, so the same remaining computation starts at position $1$. Concatenating these runs shows that the output suffix is $[b]$ followed by $r$, the final position is $1+|r|$, and the register is unchanged. The one-bit read and print steps are the corresponding read and output rules (`Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`, `Complexity.CounterProg.goes_out`). Runs concatenate by the composition law for `Goes` (`Complexity.CounterProg.Goes.trans`); shifting the input by the consumed prefix uses `Complexity.CounterProg.Goes.prepend_input`. The stated step bound follows by adding the two initial steps to the inductive bound, with the final bound adjustment justified by `Complexity.CounterProg.Goes.congr`.

**Key facts.** `Complexity.CounterProg.goes_rd_end`, `Complexity.CounterProg.goes_halt`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`, `Complexity.CounterProg.goes_out`, `Complexity.CounterProg.Goes.prepend_input`, `Complexity.CounterProg.Goes.congr`.
