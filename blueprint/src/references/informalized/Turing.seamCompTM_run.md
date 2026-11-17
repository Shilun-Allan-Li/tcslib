<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of a Composed Machine

**Claim.** If the first machine reaches its exit configuration after $T_1$ steps without visiting the exit state earlier, and the second machine reaches its specified final configuration after $T_2$ steps from its entry configuration with the first machine's resulting tape words, then the composed machine reaches the corresponding right-component final configuration after $T_1+1+T_2$ steps.

**Proof.** The second-machine run in the hypothesis starts with state $entry$ and tape words $w_1$. Rewriting its starting configuration as the exit configuration with its state replaced by $entry$ is valid because changing the state of a words configuration leaves its tape data fixed (`seam_ofWords_mapState`). The general composition theorem then applies: the first machine reaches its exit configuration without an earlier visit, the composed machine spends one transition switching to the second machine, and the next $T_2$ steps reproduce the second machine's run from that switched configuration (`seamComp_run_general`). Its endpoint is the second machine's final configuration with its state placed in the right component; identifying this state-mapped words configuration gives exactly the claimed endpoint (`seam_ofWords_mapState`).

**Key facts.** `Turing.seam_ofWords_mapState`, `Turing.seamComp_run_general`.
