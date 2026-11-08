<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.run_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After an Amplified Run

**Claim.** If every length-$T$ choice word halts $N$ on $x$, and every length-$m$ word halts the amplified machine from any rewind configuration at index $j$, then every length-$(T+m)$ word halts it from the embedding into $D$ of $N$’s initial configuration at index $j$ and counter $c$.

**Proof.** The embedding simulates each step of $N$ by one step of the amplified machine whenever the simulated configuration has not yet halted (`step_emb`). After $T$ choices, the simulated machine is halted by the hypothesis on $N$. The embedding of that halted configuration is a rewind configuration for index $j$: the embedding-to-rewind property supplies precisely this phase and preserves the freshness needed for the induction hypothesis (`rewindAt_emb`). The assumed length-$m$ halting property then halts the amplified machine on the remaining choices. The composition principle for halting a simulated prefix followed by a halting suffix formalizes these two segments (`halts_comp`).

**Key facts.** `Randomized.Amplify.step_emb`, `Randomized.Amplify.rewindAt_emb`, `Randomized.Amplify.halts_comp`.
