<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.embed_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Computation Run

**Claim.** Under the stated transition agreement and the condition that the source run avoids the exceptional state before time $t$, the host machine's $t$-step run from the embedded initial configuration equals the embedding of the source machine's configuration at time $t$.

**Proof.** Proceed by induction on the number of steps, allowing the starting configuration to vary. At zero steps both runs return their starting configurations, so the claim is immediate. For the successor step, the hypothesis at time zero gives a state $q$ such that the starting configuration is in state $q$ and $q$ is not exceptional. Thus its embedded state is precisely the image of $q$. The assumed transition agreement at this nonexceptional state, together with the single-step embedding result (`Turing.embed_step`), shows that one host step from the embedded configuration equals the embedding of one source step. The remaining $t$ steps start from that source successor. The avoidance hypothesis transfers to this shifted run: its condition at time $j<t$ is the original condition at time $j+1<t+1$. Applying the induction hypothesis to this successor configuration proves the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.embed_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
