<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.amp_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Time of the Amplified Machine

**Claim.** If $N$ halts on $x$ after every choice word of length exactly $T$, then the amplified machine with parameters $r$ and $\mathrm{dec}$ halts on $x$ after every choice word of length exactly $T+r(T+|x|+2)+1$.

**Proof.** Take any choice word $w$ of the asserted length. The amplified machine's initial configuration is the embedding of the original initial configuration in the first simulation phase (`init_eq_emb`), and that embedded configuration is fresh (`fresh_init`). Apply the simulation halting result (`run_halts`): it reduces halting after $T$ initial steps of the original machine to halting during the subsequent rewind and remaining phases. The needed halting of those phases is supplied by `rewind_halts`, using the hypothesis that every length-$T$ run of $N$ halts. The resulting total length is $T+r(T+|x|+2)+1$, so the amplified run has halted as claimed.

**Key facts.** `Randomized.Amplify.init_eq_emb`, `Randomized.Amplify.fresh_init`, `Randomized.Amplify.run_halts`, `Randomized.Amplify.rewind_halts`.
