<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.rej -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Immediate-rejection semantics

**Claim.** If the instruction at state $l$ immediately returns false and the current configuration satisfies the guard, then it has probabilistic semantics with acceptance probability $0$.

**Proof.** The immediate-return principle (`Complexity.LogProg.PSem.ret`) gives probabilistic semantics for a guarded configuration whose instruction returns $b$, with acceptance probability $1$ when $b$ is true and $0$ when $b$ is false. Taking $b$ to be false gives probability $0$; the probability parameter is then identified with the stated value by equality of rationals (`Complexity.LogProg.PSem.congr`).

**Key facts.** `Complexity.LogProg.PSem.ret`, `Complexity.LogProg.PSem.congr`.
