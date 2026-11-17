<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.BPDecidesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Time Bound

**Claim.** If $N$ halts within $T_1(|x|)$ steps and outputs the membership indicator for $L$ with probability at least $2/3$, then any pointwise larger time bound $T_2$ has the same properties.

**Proof.** Fix an input $x$. The inequality $T_1(|x|)\le T_2(|x|)$ extends the halting guarantee to the larger time bound (`Turing.NDTM.HaltsWithin.mono`). Once all branches halt by the smaller bound, the output distribution at the larger bound equals the distribution at the smaller bound (`Turing.FinNDTM.outputProb_eq_of_haltsWithin`). Consequently the probability of outputting the membership indicator remains at least $2/3$.

**Key facts.** `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`.
