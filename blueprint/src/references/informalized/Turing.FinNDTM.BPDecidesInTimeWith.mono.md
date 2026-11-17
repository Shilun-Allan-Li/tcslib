<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Turing.FinNDTM.BPDecidesInTimeWith.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Time and Success

**Claim.** If the time bound is increased pointwise and the required success probability is decreased pointwise, the machine still satisfies the corresponding decision guarantee.

**Proof.** Fix an input $x$. The original guarantee supplies both halting within $T_1(|x|)$ and output probability at least $p(|x|)$. By monotonicity of bounded halting (\texttt{HaltsWithin.mono}) and the assumed inequality $T_1(|x|)\le T_2(|x|)$, the machine also halts within $T_2(|x|)$. Since it halts within the shorter bound, its output probability at the longer bound is unchanged (\texttt{outputProb_eq_of_haltsWithin}). Finally, $q(|x|)\le p(|x|)$ and the original probability lower bound imply the required lower bound $q(|x|)$ at time $T_2(|x|)$.

**Key facts.** `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`.
