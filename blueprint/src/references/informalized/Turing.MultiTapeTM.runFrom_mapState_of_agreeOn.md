<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.MultiTapeTM.runFrom_mapState_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Under an Injective State Map

**Claim.** If the host machine’s transitions match the source machine’s mapped transitions on guarded source states, then, whenever the source run visits only guarded states before time $t$, the host run from the mapped configuration agrees with the mapped source run at time $t$.

**Proof.** First define a reference machine on the host state type: at a host state $q$, it applies the source transition at a chosen preimage of $q$, then maps the successor state through the embedding. On states of the form $e(p)$, injectivity ensures that the chosen preimage is $p$. Consequently, a step of this reference machine from a mapped source configuration is the mapped source step: the transition actions are those of the source, and applying a mapped action to a mapped configuration commutes with mapping the resulting configuration (`Cfg.mapState_apply`). Iterating this step identity shows that the reference run from the mapped starting configuration is the mapped source run at every time (`runFrom_comm_of_step`). Next, the reference machine and host machine have equal transitions on the set of host states that are images $e(p)$ of guarded source states; this follows from the assumed transition agreement and the same preimage property. At every time before $t$, the reference run’s state lies in this set: by the run identity it is the mapped source state, and the guard hypothesis applies. Thus the two runs agree through time $t$ by the theorem for machines whose transitions agree along the visited states (`runFrom_eq_of_agreeOn`). Combining that equality with the reference-run identity gives the claimed result.

**Key facts.** `Turing.Cfg.mapState_apply`, `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.MultiTapeTM.runFrom_eq_of_agreeOn`.
