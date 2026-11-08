<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.readIn_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the input-reading routine

**Claim.** Under the stated transition and non-call hypotheses, starting in the initial reading phase with the specified tapes and head positions, the program reaches a state encoding the input symbol at index $i$, with every earlier configuration in the read frame of $c$.

**Proof.** First consider the auxiliary reading machine, whose states distinguish the reading phases from the possible Boolean outcomes. The reading-machine run theorem (`Complexity.LogProg.read_model_run`) supplies a time $T$ at which this machine reaches the outcome corresponding to the input symbol at index $i$; it also puts every earlier configuration in the read frame. The phase theorem (`Complexity.LogProg.read_model_phase`) says that before this endpoint the machine is in a reading phase, not an outcome state.

Now compare the actual program with the auxiliary machine after relabeling auxiliary reading phases by $st$ and outcomes by $ex$. At time zero the relabeled auxiliary configuration is the stated initial configuration: the initial tape contents and head positions agree by the assumptions. Inductively, as long as the time is at most $T$, the auxiliary machine is in a reading phase. The actual program has no call at that phase, so its next step is an ordinary machine step (`Complexity.LogProg.rstep_noncall`). The transition hypothesis identifies that step with the specified reading transition, and relabeling its target state agrees with the transition on the relabeled machine (`Complexity.LogProg.read_action_map`). Thus the two executions agree at every time through $T$.

At time $T$, the auxiliary outcome relabels to the state encoding the indexed input symbol, giving the desired endpoint. At any earlier time, the auxiliary run lies in the read frame; state relabeling does not change the configuration data defining that frame, so the actual run does too.

**Key facts.** `Complexity.LogProg.read_model_run`, `Complexity.LogProg.read_model_phase`, `Complexity.LogProg.rrun_succ`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.read_action_map`.
