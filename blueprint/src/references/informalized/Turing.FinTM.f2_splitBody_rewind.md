<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the input head

**Claim.** From a configuration in control state $0$, the rewind phase reaches control state $2$ with the input head at position $1$, preserving all other configuration data, in at most the initial input-head position plus two steps and avoiding the anchor state throughout.

**Proof.** The rewind machine first moves the input head left into its scanning state, then continues moving left while it reads an input symbol. When it reaches the left end marker, it moves right once and enters state $2$. The catalog-rewind result (`f2_catalogRewind`) formalizes this scan and bounds its length by the initial input-head position plus two, with the final input position equal to $1$ and all other configuration data preserved. Embed these states into the split-body rewind phase carrying the fixed Boolean value $ok$. The embedding avoids the anchor, agrees with the rewind machine before its terminal state, and the terminal state is fixed in the simulated machine. The simulation-cut lemma (`f2_splitEmbed_cut`) transfers the run to the split-body machine, possibly shortening it, while preserving the endpoint and ensuring anchor avoidance at every time up to that endpoint.

**Key facts.** `Turing.FinTM.f2_catalogRewind`, `Turing.FinTM.f2_splitEmbed_cut`.
