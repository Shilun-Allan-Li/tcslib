<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.time_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Head Position Bound

**Claim.** At any time up to the contract's running time, each work-tape head lies within the interval centered at its initial position with radius that running time.

**Proof.** A head moves by at most one unit per step, so after $u$ steps its position lies between its initial position minus $u$ and its initial position plus $u$ (the general run bound `MultiTapeTM.workTapePos_runFrom_mem_Icc`). Since $u\le C.\mathrm{time}(i,d)$, the corresponding lower endpoint can only decrease and the upper endpoint can only increase when $u$ is replaced by the contract's running time. Thus the position belongs to the stated interval.

**Key facts.** `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`.
