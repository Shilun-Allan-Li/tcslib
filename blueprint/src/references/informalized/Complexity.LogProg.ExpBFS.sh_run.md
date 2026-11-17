<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.sh_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Run

**Claim.** Under the register, scratch, head-position, and product bounds, the machine reaches the first copy phase for the same phase $q$, resets the shift counter to zero, and replaces $K$ by its initial value times $2$ raised to its initial shift counter. All other registers, the memory tape, and the head position are unchanged, with the guard holding throughout.

**Proof.** The shift loop is an instance of the generic doubling routine (`shl_run`). It repeatedly transfers one unit from the shift counter to a scratch process that doubles $K$, and terminates when the counter is exhausted. The routine establishes that the resulting counter is zero and the new value of $K$ is its old value multiplied by $2$ to the old counter; its hypotheses also ensure the register bound during the loop. The bound on every register needed by the routine follows from `St.Bd.toV`, and the assumed product bound supplies its key size condition. This yields a guarded register-only run ending at the first copy phase. `of_areach` lifts it to the memory machine using the head-position bounds; because this run uses only register instructions, the tape and head remain unchanged.

**Key facts.** `Complexity.LogProg.ExpBFS.St.Bd.toV`, `Complexity.LogProg.shl_run`, `Complexity.LogProg.ExpBFS.of_areach`.
