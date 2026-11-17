<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.mono_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in Choice Length

**Claim.** If every choice sequence of length $N$ from $a$ leads to a halted configuration and all earlier live configurations satisfy $G$, then the same holds for every length $N'\ge N$.

**Proof.** Fix a choice word $\sigma$ of length $N'$. Its first $N$ bits form a word of length $N$, so the assumed halting property gives a halted configuration after that prefix, together with the guard condition at every earlier live prefix. For any $s\ge N$, split the first $s$ bits of $\sigma$ into that length-$N$ prefix followed by the next $s-N$ bits (`take_split`). Once a run is halted, appending any further choices leaves its configuration unchanged (`narun_append_of_halted`). Thus the run along $\sigma$ is already halted after all $N'$ bits. For a time $t<N'$, if $t<N$, its prefix is one of the earlier prefixes covered by the original guard condition; the list-prefix identities identify the two runs. If $t\ge N$, the run at time $t$ is the halted configuration, so it cannot satisfy the hypothesis that it is live. Hence every earlier live configuration satisfies $G$.

**Key facts.** `Complexity.LogProg.take_split`, `Complexity.LogProg.narun_append_of_halted`.
