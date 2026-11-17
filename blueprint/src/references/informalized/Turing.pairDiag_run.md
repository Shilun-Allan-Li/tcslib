<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Complete Pairing Run

**Claim.** For every bit string $x$, running the diagonal pairing machine from its initial configuration on $x$ for $4|x|+5$ steps yields a halted configuration with input head at position $|x|+1$ and output equal to the encoding of $x$ paired with itself: each bit of $x$ doubled, followed by $01$, followed by $x$.

**Proof.** Let $n=|x|$. First run the doubling phase for $2n$ steps. The doubling-run result gives state $0$, head position $n+1$, and output formed by doubling the first $n$ bits of $x$; since those bits are all of $x$, the output is the doubled string. Next apply the three-step separator and turnaround phase. It moves to state $4$ at position $n$ and appends $01$. Then the rewind pass, applied with $j=n$, takes $n+1$ steps to reach state $5$ at position $1$, preserving the output. These phases total $2n+3+(n+1)=3n+4$ steps. The run concatenation law justifies composing these consecutive runs (`Turing.MultiTapeTM.runFrom_add`). From state $5$ at position $1$, the copy phase for $n$ steps appends all of $x$ and leaves the head at position $n+1$, so after a further $n$ steps the output is the doubled $x$, followed by $01$, followed by $x$. This brings the total to $4n+4$ steps. One final step reads no symbol at the right boundary (`Turing.pairDiag_right`); the machine transitions to the halting state without changing the head position or output. The run-length decompositions use the run concatenation law and the one-step extension law (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`), and a zero input-head movement leaves the head fixed (`Turing.moveInputPos_zero`).

**Key facts.** `Turing.pairDiag_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.pairDiag_separator`, `Turing.pairDiag_rewind`, `Turing.pairDiag_copy`, `Turing.pairDiag_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.pairDiag_step`, `Turing.moveInputPos_zero`.
