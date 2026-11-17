<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.relabelState_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Relabelling Commutes with Runs

**Claim.** Relabelling the states of a machine by a bijection and relabelling the initial configuration in the same way commutes with running the machine under any finite choice word.

**Proof.** Use the bijection $e$ as an embedding of states. At a state $e(q)$, the relabelled machine applies the original transition at $e^{-1}(e(q))=q$ and relabels the successor state by $e$. Thus the relabelled and original transitions agree after embedding, at every state; the condition holds on every state encountered in any run. The run-comparison theorem for machines whose transitions agree on the embedded states (`Turing.NDTM.runWith_mapState_of_agreeOn`) therefore identifies the run of the relabelled machine from the relabelled configuration with the original run followed by state relabelling.

**Key facts.** `Turing.NDTM.runWith_mapState_of_agreeOn`.
