<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Stmt.Runs.seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential execution preserves runs

**Claim.** If executing $s$ safely reaches a state from which $t$ runs safely to $R$, then executing $s$ followed by $t$ safely reaches a state satisfying $R$.

**Proof.** Unpack the premise: $s$ is block-safe initially, and after $s$ the statement $t$ is block-safe and its resulting state satisfies $R$. Sequential block-safety requires exactly these first two safety facts. Sequential execution produces the same final state as executing $t$ after $s$, so the given postcondition is the required one.
