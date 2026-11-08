<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.Traj.seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory property for sequential contracts

**Claim.** For the sequentially composed contract, every work-head position up to the total duration satisfies the first phase's trajectory property or the second phase's trajectory property, with the second evaluated at the linked datum and the first endpoint.

**Proof.** Fix an admissible starting configuration and a time $u$ up to the composed duration. The sequential-run lemma (`Turing.Contract.seq_traj`) identifies the composed run during the first phase with the embedded first-machine run, and after the intervening transition with the second-machine run begun at the renamed first endpoint; it also supplies the relevant live endpoint state and second-phase entry condition. If $u$ is no later than the first contract time, use the first trajectory hypothesis at $u$ and the first-phase run identification, yielding the first disjunct. Otherwise write $u=T_1+1+v$, where $T_1$ is the first contract time. The run identification now gives the second-machine run at time $v$. The bound on $u$ implies that $v$ is within the second contract duration, so the second trajectory hypothesis yields the second disjunct.

**Key facts.** `Turing.Contract.seq_traj`.
