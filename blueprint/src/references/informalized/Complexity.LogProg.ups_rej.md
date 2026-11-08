<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathParse.lean :: Complexity.LogProg.ups_rej -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection State Semantics

**Claim.** If every register is bounded by $B$ and $q=0$, then the universal probabilistic program started at the rejection state has probabilistic semantics with acceptance probability $q$.

**Proof.** The rejection state executes a deterministic instruction that returns false. The rejection-state rule (`PSem.rej`) therefore gives probabilistic semantics with acceptance probability $0$, provided the starting configuration satisfies the register guard. The register-bound hypothesis supplies that guard (`UReg.reg`). Finally, since $q=0$, changing the stated acceptance probability from $0$ to $q$ preserves the semantics (`PSem.congr`).

**Key facts.** `Complexity.LogProg.PSem.rej`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.PSem.congr`.
