<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rbind_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Fresh-Randomness Bind

**Claim.** Executing a fresh-randomness bind with randomness pair $(\omega_1,\omega_2)$ is the same as first executing the initial protocol with $\omega_1$ and then executing the selected continuation with $\omega_2$.

**Proof.** Unfold the randomized execution as deterministic execution on the randomness-private-input pairs. Reindexing the initial protocol’s inputs selects the first randomness coordinate, and reindexing the continuation’s inputs selects the second; the execution of each reindexed protocol is its original execution at those inputs (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). The execution rule for a bind says to run the initial protocol, use its output to select a continuation, and then run that continuation on the same inputs (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`). Here the reindexings make those shared inputs exactly $(x,y)$ with randomness $$, respectively $$, yielding the displayed sequential execution.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
