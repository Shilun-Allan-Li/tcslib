<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_bad_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting on a Short or Delimited Tail

**Claim.** For either program parameter and every $n$, if $t$ is empty, has length one, or begins with $10$, the program starting at its scan label with register value $n$ and input position $0$ reaches a halted state with unchanged register and no additional output, in at most three steps. This holds for any output already printed.

**Proof.** Consider the three possible forms of the input. If it is empty, the scan instruction reads past the end and goes directly to the stop label without changing the register or input position. The stop instruction halts, so the total is two steps and the final position is $0$. If the input is the one-bit string $[b]$, the scan reads $b$ and moves to the corresponding second-bit label, advancing the position to $1$. The next read finds the end and moves to stop, and one more step halts; the register and output remain unchanged, and the final position is $1$. Finally, if the input begins with $[1,0]$, the first read moves to the second-true label and the second read consumes $0$ and moves to stop. Halting there takes one more step. The position is $2$, while the register and output are unchanged. The one-step read and halt facts used in these cases are the read-at-end and halt rules (`Complexity.CounterProg.goes_rd_end`, `Complexity.CounterProg.goes_halt`), together with the rules for reading false and true bits (`Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`). In the empty case, the resulting run is stated with a three-step bound by enlarging its actual two-step bound (`Complexity.CounterProg.Goes.congr`).

**Key facts.** `Complexity.CounterProg.goes_rd_end`, `Complexity.CounterProg.goes_halt`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_rd_true`, `Complexity.CounterProg.Goes.congr`.
