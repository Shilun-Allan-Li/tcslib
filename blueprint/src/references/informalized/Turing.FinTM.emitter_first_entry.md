<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_first_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Entry into a Stopping Set

**Claim.** If every configuration whose state satisfies $P$ is fixed by one machine step, and a run reaches a configuration $d$ whose state satisfies $P$ at time $T$, then it reaches $d$ at some earliest such time $t\le T$.

**Proof.** The set of times at which the run has a state satisfying $P$ is nonempty, since time $T$ qualifies by the endpoint hypothesis. Let $t$ be its least element. Then $t\le T$, and by minimality no earlier time has a state satisfying $P$. At time $t$ the run is fixed by one step, by the assumed fixed-point property. Iterating a fixed point leaves it unchanged, so the run from time $t$ is still the same configuration after $T-t$ further steps. The run-composition law (`Turing.MultiTapeTM.runFrom_add`) identifies this latter configuration with the original run at time $t+(T-t)=T$, namely $d$. Therefore the run at the first qualifying time $t$ is already $d$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
