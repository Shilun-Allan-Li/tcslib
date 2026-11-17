<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_mapState_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Renaming Preserves Guarded Runs

**Claim.** When the host and source transitions agree on the guarded source states after renaming by the embedding, their runs under the same choice word agree, provided every source state reached before a step is guarded.

**Proof.** Proceed by induction on the choice word, allowing the starting configuration to vary. For the empty word, both runs return their starting configurations, so the equality is immediate. For a word beginning with a bit $b$, the guard hypothesis at prefix length zero says that the current source state, if present, is good. The one-step state-renaming theorem (`Turing.NDTM.stepWith_mapState_of_agreeOn`) then identifies the host configuration after choice $b$ with the state-renamed source configuration after that choice. Apply the induction hypothesis to the remaining word. Its guard condition follows from the original hypothesis: a prefix of length $u$ of the remaining word corresponds to a prefix of length $u+1$ of the original word, and the run configurations are the same by the one-step unfolding. Thus the complete runs agree.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.stepWith_mapState_of_agreeOn`.
