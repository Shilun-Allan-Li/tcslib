<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.mrun_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Configurations Remain Fixed

**Claim.** A configuration with halted control state, register assignment $v$, recorded answer $res$, and memory state $\mu$ is unchanged after any number of steps.

**Proof.** Induct on the number of steps. At zero steps the run is the initial configuration. For the successor case, the successor-time run identity (mrun_succ) expresses the run of length $n+1$ as a run of length $n$ starting after one transition. A halted configuration is fixed by one transition, directly from the definition of the step function; the induction hypothesis then says that the remaining $n$ steps leave it unchanged as well.

**Key facts.** `Complexity.LogProg.mrun_succ`.
