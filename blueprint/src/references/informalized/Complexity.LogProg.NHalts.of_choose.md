<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.of_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Choice

**Claim.** If the instruction at $l$ chooses between $l_1$ and $l_0$, then, for either choice bit $b$, halting within $N+1$ steps from $(l,v,res)$ implies the stated halting property within $N$ steps from the selected successor.

**Proof.** Fix a choice word $\sigma$ of length $N$ for the selected successor, and prepend the bit $b$. This gives a word of length $N+1$ to which the hypothesis applies. The first step from $l$ follows the branch selected by $b$ (`nastep_choose`), and the run on the remaining word is exactly the run from that successor (`narun_cons`). The resulting configuration is therefore halted. For each $t<N$, apply the guard part of the hypothesis at time $t+1$ on the prefixed word. Its prefix of length $t+1$ consists of $b$ followed by the first $t$ bits of $\sigma$, so its configuration is exactly the length-$t$ run from the selected successor. This gives the required guard condition whenever that configuration is live.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_choose`.
