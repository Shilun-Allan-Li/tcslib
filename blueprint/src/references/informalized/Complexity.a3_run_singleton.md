<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_run_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Wrapper computes a singleton output

**Claim.** Under the stated first-return and endpoint hypotheses, the wrapper computes the singleton word $[b]$ from $x$ within $2|x|+2+t+1$ steps.

**Proof.** Use the wrapper’s setup run: after $2|x|+2$ steps it is in phase $2$ with $x$ stored on work tape zero (Complexity.a3_run_start). From there, the first-return result (Complexity.a3_run_call) shows that after $t$ more steps it is in the renamed exit configuration whose work tape zero contains $[b]$. The wrapper’s exit transition copies the symbol found on work tape zero to the output and halts in one further step. Thus at the stated total time its state is halted and its output is $[b]$. The characterization of computation within a specified time by these two endpoint properties (Turing.FinTM.computesInTime_iff) supplies the desired computation claim. The run is split into setup and subsequent phases using the run-addition identity (Turing.MultiTapeTM.runFrom_add); the final transition is expressed by the run-successor identity (Turing.MultiTapeTM.runFrom_succ_eq_step').

**Key facts.** `Complexity.a3_run_start`, `Complexity.a3_run_call`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
