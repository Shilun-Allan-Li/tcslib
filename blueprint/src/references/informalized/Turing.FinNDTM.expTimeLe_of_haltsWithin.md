<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.expTimeLe_of_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Nonhalting Bound from Uniform Halting

**Claim.** If every branch on input $x$ has halted within $t_0$ steps, then for every $K$ the sum of the nonhalting probabilities for choice lengths below $K$ is at most $t_0$.

**Proof.** The halting result as a function of the choice word is prefix-stable (`Turing.FinNDTM.haltRun_isPrefixStable`): once a run halts, extending its choice word leaves its halting result unchanged. The assumed uniform halting condition says that for every word of length $t_0$, the machine's state is the halting state. By the characterization of an absent halting result (`Turing.FinNDTM.haltRun_eq_none_iff`), the halting result on each such word is therefore not absent. The expected-time bound for prefix-stable results that are never absent at length $t_0$ (`Randomized.expTimeLe_of_forall_ne_none`) now bounds the sum of nonhalting probabilities over all shorter lengths by $t_0$, as claimed.

**Key facts.** `Turing.FinNDTM.haltRun_isPrefixStable`, `Turing.FinNDTM.haltRun_eq_none_iff`, `Randomized.expTimeLe_of_forall_ne_none`.
