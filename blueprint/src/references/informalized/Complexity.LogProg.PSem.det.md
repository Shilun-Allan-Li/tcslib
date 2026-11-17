<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Deterministic Step

**Claim.** If the instruction at $l$ is deterministic, the current configuration satisfies the guard, and its one-step successor has probabilistic semantics with probability $p$, then the current configuration also has probabilistic semantics with probability $p$.

**Proof.** The deterministic-step principle follows the two parts of probabilistic semantics. For termination, the current configuration satisfies the guard by hypothesis, and each choice bit takes it to the same deterministic successor; the successor's termination proof therefore supplies termination for both branches. For the probability clause, any halting length from the current live configuration is positive: a length-zero run cannot already be halted. Write it as $N+1$. Removing the first, irrelevant choice bit gives a halting length $N$ from the deterministic successor (Complexity.LogProg.NHalts.of_det). The successor's probability equalities then apply at $N$. Since the first step ignores the choice bit, the probability of either output after $N+1$ bits equals its probability after $N$ bits from the successor (Complexity.LogProg.randProb_narun_det). Thus both output probabilities have the required values. The step identities used here are the deterministic transition facts Complexity.LogProg.nastep_det and Complexity.LogProg.nastep_det'.

**Key facts.** `Complexity.LogProg.nastep_det`, `Complexity.LogProg.nastep_det'`, `Complexity.LogProg.NHalts.of_det`, `Complexity.LogProg.succ_of_nhalts`, `Complexity.LogProg.randProb_narun_det`.
