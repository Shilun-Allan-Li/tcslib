<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitEmbed_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anchor-free simulation to a terminal state

**Claim.** If the source run reaches a configuration whose state satisfies the stopping predicate after exactly $T$ steps, then the host run reaches the state-renamed terminal configuration at some time $t\le T$, and avoids the anchor at every time from $0$ through $t$.

**Proof.** Choose $t$ to be the first time the source run has a state satisfying the stopping predicate. Since the terminal configuration at time $T$ has such a state, this first time exists and is at most $T$. The source configuration at time $t$ is fixed by one step, so all later iterates are equal to it; in particular, the configuration at time $T$ is the one at time $t$. Thus the source run at time $t$ is the given terminal configuration. For each time $j\le t$, the host run agrees with the state-renamed source run: this follows by induction on $j$. At a successor step, if the source state is absent then both machines remain at the configuration; if it is present, minimality of $t$ says that state does not satisfy the stopping predicate, so the assumed transition agreement applies. Finally, every source state before or at time $t$ is either absent or is mapped by the embedding to a state different from the anchor. The host agreement therefore shows that its configurations throughout this interval avoid the anchor. Applying the agreement at time $t$ and the identification of the source configuration there gives the required terminal configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
