<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amortized Counter Invariant

**Claim.** For each $i\le |x|$, the machine reaches the configuration storing the binary representation of $i$ in state $0$, with input-head position $i+1$, within a time bound $t+2w(i)\le4i$.

**Proof.** Use induction on $i$. For $i=0$, the initial configuration already stores the empty binary representation, and the time bound holds with $t=0$. For the successor case, take the time $t$ supplied by induction for $i$. Append one complete counter increment, which takes $2\operatorname{carry}(i.bits)+2$ steps by the counter-increment result. The run-addition identity lets us concatenate this run with the first $t$ steps. The incremented bit word is the binary representation of $i+1$ ($\texttt{counterInc_bits}$). To verify the bound, use the potential identity $\operatorname{count}_1(\operatorname{inc}(b))+\operatorname{carry}(b)=\operatorname{count}_1(b)+1$ ($\texttt{counterInc_potential}$), together with the induction bound; elementary arithmetic gives the required estimate for the successor. The increment result applies since $i<|x|$, as follows from the successor case’s hypothesis.

**Key facts.** `Complexity.counterInc_potential`, `Complexity.counterInc_bits`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.counter_increment`.
