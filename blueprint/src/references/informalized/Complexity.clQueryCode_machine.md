<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clQueryCode_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine for Querying Comparison Flags

**Claim.** There is a finite binary Turing machine that, on the packed query argument, outputs the optional-time code for the greatest time $s<N$ whose two indicated row values and target values satisfy the specified sum equality, or the absence code if no such time exists, within the stated time bound.

**Proof.** Use the query-flags machine to compute, in order, the $N$ Boolean flags for the comparison at each time. Its exact runtime and output are given by `Complexity.clQueryFlags_compute`. Next use a machine that computes the last-success code in polynomial time (`Complexity.clLastCode_native`). The buffered-composition theorem (`Turing.FinTM.bufferedCompTM_computesInTime`) combines these machines, with the intermediate flag word stored and supplied to the second machine. The output length of the first machine is at most its runtime (`Turing.MultiTapeTM.output_length_le`); hence the flag word has length at most the query-flags runtime. Substituting this bound into the composition runtime yields the displayed bound, up to the stated polynomial term. Finally, monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) raises the actual runtime to that bound, giving the required witness machine and constants.

**Key facts.** `Complexity.clQueryFlags_compute`, `Complexity.clLastCode_native`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
