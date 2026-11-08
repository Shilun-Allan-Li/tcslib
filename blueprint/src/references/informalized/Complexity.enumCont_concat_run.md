<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_concat_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation Machine Run

**Claim.** For Boolean words $x$ and $s$, running the assembly machine on input $x$ from its initial configuration with $s$ on its work tape for $|x|+|s|+2$ steps gives a halted configuration with the input head at the right boundary, work tape $s$ headed at $|s|$, and output $x\mathbin{++}s$.

**Proof.** First apply the input-phase assembly result (`Complexity.enumCont_concat_native`) with empty prefix and remaining input $x$. After $|x|+1$ steps the machine is in candidate phase at the right boundary, with its work tape still holding $s$ and output $x$. Next apply the candidate-phase assembly result (`Complexity.enumCont_concat_candidate`) with empty candidate prefix and remaining word $s$. In $|s|+1$ additional steps it halts, leaves the work tape unchanged with its head at $|s|$, and appends $s$ to the output, giving $x\mathbin{++}s$. The initial configuration's input head is at position $1$ and its output is empty, so it is exactly the required starting point. The run-addition identity (`Turing.MultiTapeTM.runFrom_add`) combines the two consecutive run segments, whose total length is $(|x|+1)+(|s|+1)=|x|+|s|+2$.

**Key facts.** `Complexity.enumCont_concat_native`, `Complexity.enumCont_concat_candidate`, `Turing.MultiTapeTM.runFrom_add`.
