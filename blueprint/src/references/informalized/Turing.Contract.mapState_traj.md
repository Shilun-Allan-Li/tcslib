<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.mapState_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Trajectory Agreement

**Claim.** Under the stated transition agreement on good states and the hypothesis that all states visited strictly before the contract time are good, the run of $N$ from $d$ agrees through the contract time with the state-embedded run of $M$ from the constantly relabeled configuration.

**Proof.** Let $c$ be the configuration obtained from $d$ by replacing every state by the entry state. Its state is the entry state, and relabeling its states by the embedding recovers $d$: the state coordinates agree by the hypothesis on $d$, while all other configuration data are unchanged. Apply the trajectory agreement theorem (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) to $c$ at time $u$. Its guard requires goodness at each time $v<u$ when the source run has a state. The contract hypothesis supplies exactly this: the precondition holds for $c$, and $v<u\leq C.\mathrm{time}(i,c)$ implies $v<C.\mathrm{time}(i,c)$. The theorem therefore identifies the host run from the embedded $c$ with the embedded source run at time $u$. Replacing the embedded $c$ by $d$ using the configuration equality proves the assertion.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`.
