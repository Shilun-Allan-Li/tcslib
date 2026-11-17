<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.lockstep_admissible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Admissibility of a Lockstep Contract

**Claim.** Under the stated entry-state correspondence and head-position bounds, an entry configuration for $C$ satisfying its precondition maps to a configuration in state $e'$ that satisfies the precondition of the lockstep contract at parameter $(i,c)$.

**Proof.** The first conclusion is exactly the assumed entry-state correspondence: since $c$ is in state $e$, its encoded configuration is in state $e'$. For the second, the lockstep contract’s precondition requires three facts: the target configuration equals the encoding of the source configuration, the source is in entry state $e$, and the source satisfies $C$’s precondition. The first is true by taking the target to be $E(c)$; the other two are the hypotheses on $c$.
