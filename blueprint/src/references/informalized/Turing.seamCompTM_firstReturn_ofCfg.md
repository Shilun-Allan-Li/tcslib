<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_firstReturn_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return for Composed Configurations

**Claim.** Given a first visit by the first machine to its exit state and a second-machine run from the resulting configuration with its state changed to the entry state, the composed machine avoids the right-component state $q_2$ at every time $t<T_1+1+T_2$.

**Proof.** The hypotheses already have the general form needed: the first machine takes $c_0$ to $c_1$ in $T_1$ steps, $c_1$ is in the exit state, and that state is avoided at all earlier times. The second machine's run begins at $c_1$ with only its state replaced by the entry state, and the hypothesis says it avoids $q_2$ for the first $T_2$ times. Applying the general first-return result for sequential composition gives that the composed run cannot have $q_2$ in its right component before the $T_1$ steps to the exit, the one-step switch, and the subsequent $T_2$ steps (`seamComp_firstReturn_general`).

**Key facts.** `Turing.seamComp_firstReturn_general`.
