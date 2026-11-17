<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.sourceAnswer_at_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Output at the Padded Time Bound

**Claim.** If $M$ decides $L$ within $aT(|x|)$ steps and outputs the membership bit, then after $(a+1)(T(|x|+1))$ steps its last output bit, interpreted as false for an empty output, is the membership indicator.

**Proof.** The padded time is at least $aT(|x|)$, since both factors in its product are at least the corresponding factors in $aT(|x|)$. Monotonicity of computation time therefore extends the assumed decision computation to the padded time. The characterization of computation in time says that at that time the output list is still the prescribed singleton list containing the membership indicator. Its last element, with false as the default for an empty list, is consequently the indicator itself.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`.
