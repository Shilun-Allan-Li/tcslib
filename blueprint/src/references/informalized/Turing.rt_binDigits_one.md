<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_binDigits_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits of One

**Claim.** For every positive $w$, the first $w$ binary digits of $1$, listed from least significant to most significant, consist of one true digit followed by $w-1$ false digits.

**Proof.** Write $w=v+1$, which is possible since $w>0$. The indices in the digit list then comprise $0$ followed by the indices obtained by adding one to each index below $v$. The zeroth bit of $1$ is true. Every positive-index bit is false: for each index $j<v$, the bit at $j+1$ is false because shifting the index in the bit test shows that it would require the next bit of $1$ to be set, whereas $1$ has no such higher bit. Thus the remaining $v=w-1$ entries are all false, as asserted.
