<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_firstReturn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return in Sequential Composition

**Claim.** Under the stated first-visit hypotheses, the composed machine cannot have state $q_2$ in its right component at any time earlier than $T_1+1+T_2$.

**Proof.** First express the second machine's run from the configuration with state $exit$ as its run from the same tape contents and head positions with state replaced by $entry`. This is just the identification of a words configuration after changing its state (`seam_ofWords_mapState`), and transfers the hypothesis that $q_2$ is not reached before time $T_2$. Now apply the general first-return theorem for sequential composition (`seamComp_firstReturn_general`) to the first machine's run from its initial configuration to its exit configuration. The first machine avoids the exit state at every earlier time, so the composed machine remains in the left component during those times; it switches to the right component only after the exit configuration, in one transition. The transferred second-machine hypothesis rules out state $q_2$ throughout the following $T_2$ steps before its first return. Together these intervals exclude the right-component state $q_2$ at every time $t<T_1+1+T_2$.

**Key facts.** `Turing.seam_ofWords_mapState`, `Turing.seamComp_firstReturn_general`.
