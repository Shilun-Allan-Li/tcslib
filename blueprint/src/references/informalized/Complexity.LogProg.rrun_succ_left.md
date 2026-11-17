<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.rrun_succ_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run After One Step

**Claim.** The run of length $n+1$ from $c$ equals the run of length $n$ starting from the configuration reached after one step from $c$.

**Proof.** Use the run composition law: a run of length $a+b$ from a configuration is the run of length $b$ from the configuration reached after $a$ steps (`rrun_add`). First commute the summands in $n+1$ to write the length as $1+n$, then apply this law with $a=1$ and $b=n$. The resulting expression is precisely the run of length $n$ from the one-step configuration.

**Key facts.** `Complexity.LogProg.rrun_add`.
