<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedFrame_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs of the Framed Machine

**Claim.** For every number of steps, running the capture machine from a framed configuration gives the frame of the timed-interpreter run from the original configuration for the same number of steps.

**Proof.** Proceed by induction on the number of steps. At zero steps, both sides are the same framed configuration. For the successor step, express each run of length one more as a single machine step after its run of the previous length (the run successor equation, `Turing.MultiTapeTM.runFrom_succ_eq_step'`). Apply the induction hypothesis to identify the configurations before that step. The one-step correspondence for framed configurations (`Turing.timedFrame_step`) then identifies their successors, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedFrame_step`.
