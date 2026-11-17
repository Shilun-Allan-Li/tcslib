<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Streaming Runs

**Claim.** Running $m+n$ rounds gives the same final state and concatenated output as running $m$ rounds and then $n$ rounds from the resulting state.

**Proof.** Induct on $m$, keeping the starting state arbitrary. When $m=0$, the zero-round run leaves the state unchanged and emits the empty string, so the identity follows directly. For the successor step, the recursive definition performs one round first and then runs the remaining rounds. The natural-number identity $(m+1)+n=(m+n)+1$ lets us expose that first round on the left-hand side. Apply the induction hypothesis to the remaining $m+n$ rounds, starting from the state produced by the first round. The outputs then agree because concatenation is associative: the first round's output is followed by the output of the $m$-round segment and then the $n$-round segment.
