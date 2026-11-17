<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_succ_of_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution after a halting step

**Claim.** If one step from $c$ halts with verdict $v$, then for every $t\ge0$, execution from $c$ for $t+1$ steps returns $v$ and leaves the memory unchanged.

**Proof.** The one-step execution equation reduces execution for $t+1$ to a case distinction on the first step (`WordRAM.exec_succ`). Since that step halts with verdict $v$, the halting branch applies and returns $(v,c.mem)$, independently of the remaining time bound.

**Key facts.** `WordRAM.exec_succ`.
