<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.append_mem_iff_outputWith_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership from the truncated run

**Claim.** Under the stated characterization of membership by a length-$Q$ choice string and the assumption that all length-$T$ runs halt, membership for a choice string $r$ of length $Q$ is equivalent to the truncated run on its first $T$ bits outputting true.

**Proof.** Since $|r|=Q$ and $T\le Q$, the run on $r$ agrees with the run on its first $T$ bits: after those $T$ choices the run has halted, so further choices do not change its configuration (`Turing.FinNDTM.runWith_eq_runWith_take`). Apply the assumed characterization of membership to $r$. Its halting condition follows from the same halting hypothesis, and its output equals the output of the truncated run. The characterization therefore reduces membership exactly to that output being the one-bit string true.

**Key facts.** `Turing.FinNDTM.runWith_eq_runWith_take`.
