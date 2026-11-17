<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.Goes.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Run Bound

**Claim.** If every output word admits a run reaching the specified endpoint and output extension within $b$ steps, then it also admits such a run within any bound $b'\ge b$.

**Proof.** Fix an output word $o$. By the hypothesis, there is a time $t\le b$ at which the required endpoint and output extension are reached. Since $b\le b'$, the same time satisfies $t\le b'$. The run itself is unchanged, so this proves the claim for every $o$.
