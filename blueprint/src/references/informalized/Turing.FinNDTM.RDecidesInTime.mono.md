<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.RDecidesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the time bound

**Claim.** If $T_1(n)\le T_2(n)$ for every input length and the machine satisfies the one-sided-error condition within $T_1$, then it satisfies that condition within $T_2$.

**Proof.** Fix an input $x$. Every branch halts by time $T_2(|x|)$ because halting by $T_1(|x|)$ extends to any larger time (`Turing.NDTM.HaltsWithin.mono`). The output distribution at the larger time agrees with the one at the smaller time once all branches halt by the smaller bound (`Turing.FinNDTM.outputProb_eq_of_haltsWithin`), so the probability lower bound is preserved. For a length-$T_2(|x|)$ choice word, its run agrees with the run on the prefix of length $T_1(|x|)$ (`Turing.FinNDTM.runWith_eq_runWith_take`). That prefix has the required length, so on a nonmember input the shorter-time guarantee says its output is false; hence the longer word also outputs false. These are precisely the required guarantees at $T_2$.

**Key facts.** `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Turing.FinNDTM.runWith_eq_runWith_take`.
