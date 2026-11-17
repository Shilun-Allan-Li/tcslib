<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nans_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer Across a Deterministic Run

**Claim.** If the deterministic replacement machine takes $T$ steps from $a$ to $a'$, and every active state before time $T$ has a deterministic instruction in the original machine, then a length-$(T+N)$ choice sequence from $a$ leaves answer $b$ exactly when a length-$N$ choice sequence from $a'$ leaves answer $b$.

**Proof.** First observe that for any choice string $\sigma$ of length $T$ and any suffix $\tau$, running the concatenation from $a$ is the same as running $\tau$ from $a'$. Indeed, runs on concatenated strings split into a run on the first part followed by a run on the suffix (`narun_append`). Up through time $T$, every active instruction is deterministic by hypothesis, so the original machine’s run on $\sigma$ agrees with the deterministic replacement run for those $T$ steps (`narun_eq_arun`). The assumed endpoint equation then identifies the intermediate configuration with $a'$. For the forward implication, split a witnessing length-$(T+N)$ string after its first $T$ bits; its remaining suffix has length $N$ and, by this observation, witnesses the same answer from $a'$. For the reverse implication, prepend any $T$ bits, for example $T$ false bits, to a witnessing length-$N$ suffix. The same observation shows that the resulting length-$(T+N)$ string preserves its answer.

**Key facts.** `Complexity.LogProg.narun_append`, `Complexity.LogProg.narun_eq_arun`.
