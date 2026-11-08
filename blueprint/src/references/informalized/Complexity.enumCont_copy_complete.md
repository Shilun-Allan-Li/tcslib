<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_copy_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Copy and Rewind

**Claim.** Starting with the heads at zero, tape zero storing `old`, and the last tape storing `v`, where $|old|\le |v|$, the machine reaches $q_a$ after $2|v|+2$ steps, with $f$ applied symbolwise to $v$ on tape zero, the last tape blank, and both heads at zero.

**Proof.** Apply the copy-scan result (`Complexity.enumCont_copy_scan`) with the prefix empty and the remaining suffix equal to $v$. It gives, after $|v|+1$ steps, state $q_r$, a blank last tape, and tape zero storing $f(v)$ followed by `old.drop |v|`; the length hypothesis makes that dropped suffix empty. The scan leaves the heads at position $|v|-1$. The rewind result (`Complexity.enumCont_pair_rewind`) then applies with word $f(v)$ and $j=|v|$: in $|v|+1$ further steps it reaches $q_a$, preserves tape zero, and returns both heads to zero. The total time is $(|v|+1)+(|v|+1)=2|v|+2$.

**Key facts.** `Complexity.enumCont_copy_scan`, `Complexity.enumCont_sparse_some`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.enumCont_pair_rewind`.
