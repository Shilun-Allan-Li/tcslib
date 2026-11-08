<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.onesFrom_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Interval of Marked Cells

**Claim.** For every $n$, the tape marking exactly the cells in $[0,n)$ agrees at every integer cell with the tape containing $n$ consecutive true bits from cell zero and blanks elsewhere.

**Proof.** Fix an integer cell $c$. If $c<0$, both tapes are blank: the interval condition fails, and the finite buffer tape is blank at negative positions. If $c\ge 0$, the buffer tape reads the replicated word at index $c$. This is true exactly when $c<n$, since the word consists of $n$ true bits and has no entry at indices $c\ge n$. The interval tape is true under exactly the same condition $0\le c<n$. Therefore the tapes agree at every cell.
