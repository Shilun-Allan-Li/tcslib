<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.comapRandomness_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution After Randomness Reindexing

**Claim.** Running the randomness-reindexed protocol with new coins gives the same output as running the original protocol with those coins mapped into its original randomness spaces.

**Proof.** The deterministic execution law for input reindexing says that a protocol reindexed along maps $f_X,f_Y$, when run on $u,v$, has the same output as the original protocol run on $f_X(u),f_Y(v)$ (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`). Take $f_X(\omega_x',x)=(hX(\omega_x'),x)$ and $f_Y(\omega_y',y)=(hY(\omega_y'),y)$. Applying the law and unpacking private-coin execution yields the stated equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`.
