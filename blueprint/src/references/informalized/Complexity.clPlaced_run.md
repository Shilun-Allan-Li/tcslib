<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlaced_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Placed Simulation

**Claim.** Under the stated transition-agreement and state guard hypotheses, the host machine run for $t$ steps from the placed configuration is exactly the placement of the source machine’s configuration after $t$ steps.

**Proof.** First view the source machine as a host-sized machine using the placement of its tapes: its transition reads the symbols in the occupied host slots and performs the source action there, leaving the other host tapes untouched. The theorem that runs commute with an injective state map when transitions agree on guarded states (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) then identifies the host run with this tape-expanded source run, with states mapped by the given injection. The guard hypothesis supplies the required transition agreement at every step before time $t$. Finally, the tape-expansion identity for runs (`Turing.embedEmitTM_runFrom`) says that this expanded run is precisely the placement of the source run, including the untouched host tapes and their head positions. Rewriting by that identity yields the desired equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.embedEmitTM_runFrom`.
