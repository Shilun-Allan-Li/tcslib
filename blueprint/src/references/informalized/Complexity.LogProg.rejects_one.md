<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.rejects_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Immediate Rejection at a Non-Call State

**Claim.** Under the stated transition hypothesis, the program rejects from the adjusted configuration in one step, appending false to the output and setting the register-head positions as specified; every pre-final configuration is an ordinary non-call state.

**Proof.** The one-step rejection lemma (`Complexity.LogProg.rrun_one_rej`) gives the halting state, the output with false appended, and the required adjusted register-head positions after one step. Choose the rejection time to be $1$. The only natural time strictly before $1$ is $0$, when the run is still at the starting configuration. That configuration has state $s$ and input-head position $ip$, and $P.call(s)=\mathrm{none}$ by hypothesis, so it supplies the required pre-final witness.

**Key facts.** `Complexity.LogProg.rrun_one_rej`.
