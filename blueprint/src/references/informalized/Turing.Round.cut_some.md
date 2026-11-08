<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Round.cut_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intermediate States in a Round

**Claim.** At every strictly intermediate positive time in a round of duration $t$, the machine is in some state $s$ with $s\ne a$ and whose optional state is not in $E$.

**Proof.** Fix $u$ with $0<u<t$. The round condition says that the optional state at time $u$ is outside the set consisting of the halted state, the anchor state, and the states in $E$. The characterization of being outside this set (`Turing.not_mem_roundStop`) therefore supplies a state $s$ such that the configuration’s state is $\mathrm{some}(s)$, with $s\ne a$ and $\mathrm{some}(s)\notin E$.

**Key facts.** `Turing.not_mem_roundStop`.
