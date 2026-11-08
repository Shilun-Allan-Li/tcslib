<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.heavy_prefix_mem_goldreichLevinRunUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heavy Prefixes Persist Through the Run

**Claim.** For every stage $k$, if the run up to that stage returns an active set, then the $k$-coordinate prefix of any frequency whose coefficient has magnitude at least $\tau$ belongs to that active set.

**Proof.** Proceed by induction on the stage. At stage zero the run returns the singleton active set containing the empty prefix, so the assertion holds. Now suppose it holds at stage $k$ and the run at stage $k+1$ returns an active set. Examine the recursive run at stage $k$: if it returned no set, then the next stage would also return no set, contrary to the assumption. Thus it returned some previous active set. By induction, the $k$-coordinate prefix of the heavy frequency lies in that set. The heavy-prefix retention result then places its next prefix in the retained set for this stage (`heavy_prefix_mem_goldreichLevinRetained`). The recursive definition returns that retained set when its size is within the active cap; if it exceeds the cap, it returns no set. Since the run at stage $k+1$ is assumed to return a set, it must be the retained set, proving the claim.

**Key facts.** `FABL.heavy_prefix_mem_goldreichLevinRetained`.
