<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_call_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Call Phase Simulation

**Claim.** An embedded host call begun in the designated entry state follows the source computation for the specified duration, reaches the embedded endpoint, and avoids the anchor state throughout.

**Proof.** Since $t>0$, write the duration as $t+1$. First, one host step from the entry configuration agrees with the embedded source step: the entry transition hypothesis identifies the transition, and compatibility of mapped actions with mapped configurations (`Turing.Cfg.mapState_apply`) identifies the resulting configuration with the embedding of the source configuration after one step. Now apply the embedded phase simulation theorem (`Turing.FinTM.emitterP2_phase`) to the source run beginning after this first step, for the remaining $t$ steps. Use as its good states all states other than the exit state. The guard hypothesis ensures goodness at every intermediate time: an intermediate time in this tail corresponds to a source time $1+j$, which is strictly between $0$ and the total duration. The source endpoint condition for the tail follows by decomposing the run into its first step and the remaining steps (`Turing.MultiTapeTM.runFrom_add`). Combining the first step and this tail gives the claimed endpoint at total time $t+1$. For safety, at time zero the host is in the entry state, distinct from the anchor. At each later time, decompose the host run after its first step; the phase simulation's safety conclusion excludes the anchor for the remainder.

**Key facts.** `Turing.Cfg.mapState_apply`, `Turing.FinTM.emitterP2_phase`, `Turing.MultiTapeTM.runFrom_add`, `Turing.embedEmitTM_runFrom`.
