<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.enc_inputPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Input-Head Position

**Claim.** When the abstract read position $p$ satisfies $p\le |x|$, the input-head position in the encoded configuration is $p+1$.

**Proof.** The encoding assigns input-head position $\min(p+1,|x|+1)$. Under the hypothesis $p\le |x|$, we have $p+1\le |x|+1$, so the minimum is $p+1$.
