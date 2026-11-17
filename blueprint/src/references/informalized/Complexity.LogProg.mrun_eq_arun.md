<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.mrun_eq_arun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement with the Deterministic Run

**Claim.** If the deterministic run formed from the program’s deterministic instructions and the answer $\beta$ is still running at time $T$, then through every time $t\le T$ the memory-augmented run agrees with it and keeps its memory state unchanged.

**Proof.** Proceed by induction on $t$. At time zero the two configurations agree by definition. For the successor step, suppose $t+1\le T$ and the configurations agree at time $t$. The run-composition identity for memory-augmented runs (mrun_add) lets us express the run through $t+1$ as one step after the configuration at time $t$. The deterministic run has the analogous successor description, and we compare those steps. Write its configuration at time $t$ as $(c,\mu)$, with the same register-machine configuration $c$ and memory state $\mu$ on the memory-augmented side. If its control state is halted, both one-step transitions leave the configuration fixed, so they agree. If it is live, write its state as $l$. When the instruction of the memory-augmented program at $l$ is deterministic, the one-step correspondence lemma (mstep_det) shows that both runs make the same register-machine transition and retain $\mu$. In the other case, the deterministic part replaces that instruction by the answer $\beta$ and halts at the next step. The deterministic run would therefore be halted at time $t+1$ and remain halted through time $T$, contradicting the hypothesis that it is still running at time $T$. Thus only the deterministic-instruction case can occur, proving agreement at time $t+1$.

**Key facts.** `Complexity.LogProg.mrun_add`, `Complexity.LogProg.mstep_det`, `Complexity.LogProg.MARM.detPart_mem`, `Complexity.LogProg.arun_add`, `Complexity.LogProg.arun_halted`.
