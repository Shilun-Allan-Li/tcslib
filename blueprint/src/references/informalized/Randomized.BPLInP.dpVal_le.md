<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.dpVal_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on dynamic-programming values

**Claim.** For every depth $t$ and code $c$, the dynamic-programming value is at most $(2V)^t$.

**Proof.** Induct on $t$, uniformly in the code $c$. At depth zero, the value is either zero or one, so it is at most $(2V)^0=1$. At depth $t+1$, each candidate code contributes the sum of two terms, one for each choice bit. By the induction hypothesis each depth-$t$ value is at most $(2V)^t$, and each term is either that value or zero. Thus each candidate contributes at most $2(2V)^t$. There are exactly $V$ candidate codes in the range, so summing gives at most $V\cdot 2(2V)^t=(2V)^{t+1}$, as required.
