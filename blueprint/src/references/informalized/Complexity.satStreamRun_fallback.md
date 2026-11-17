<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_fallback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fallback Output

**Claim.** For any input $x$ and natural number $k$, running $k+1$ rounds from fresh cursor $0$, consumed length $|x|$, and phase $0$ emits exactly $[0]$.

**Proof.** The first round sees the empty unconsumed suffix, since the consumed length is already $|x|$. In phase $0$, this end-of-input case emits $[0]$ and moves to phase $4$, leaving the cursors fixed. Every subsequent round in phase $4$ leaves the state unchanged and emits nothing, by the finished-run property (\texttt{Complexity.satStreamRun_finished}). Hence the entire run's output is the initial $[0]$ followed by empty outputs, as claimed.

**Key facts.** `Complexity.satStreamRun_finished`.
