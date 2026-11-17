<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFresh_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First completion of the field loader

**Claim.** For every Boolean input word $x$, valid input-head position $p$, stream prefix $\mathrm{pre}$, field $w$, stream tail, and old target word, the loader reaches its completed reading control at some positive time at most $2|\mathrm{old}|+3|w|+6$. Before that time it is never in the completed control, and at that time the target contains exactly $w$ with its head at zero, the stream head is at $|\mathrm{pre}|+2|w|+2$, and the input, stream contents, and empty physical output have the specified values.

**Proof.** First, the bounded reset-and-read result (`clFresh_run`) supplies a time $B\le 2|\mathrm{old}|+3|w|+6$ at which the unrestricted loader has reached the designated reader configuration, including its completed reading state. The start configuration is the reset configuration with its state embedded into the left side of the composite state type, and the endpoint’s state is the embedded completed reading state. The start state is not that completed state, as witnessed by the state calculation in the proof. Apply the first-arrival principle (`clFirst`) to this run: since the completed state is stationary (`clFresh_idle`), there is a first time $t$ at which it is reached; this time is positive, no earlier time has that state, and the configuration at $t$ is the supplied endpoint. Its bound $t\le B$ gives the claimed bound.

**Key facts.** `Complexity.clFresh_run`, `Complexity.clFirst`, `Complexity.clFresh_idle`.
