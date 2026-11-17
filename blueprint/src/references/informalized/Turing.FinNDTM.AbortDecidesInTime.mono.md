<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Turing.FinNDTM.AbortDecidesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Aborting Decision Time

**Claim.** If the time bound for which $N$ satisfies the aborting decision conditions is increased pointwise, the same conditions continue to hold.

**Proof.** Fix an input $x$ and let $t=T_1(|x|)$ and $t'=T_2(|x|)$. Since $t\le t'$, every branch halts by time $t'$ (the halting guarantee is monotone). For a choice word $w$ of length $t'$, its first $t$ choices determine the same final configuration as running just that prefix: once the machine has halted by time $t$, extra choices do not change the configuration. The prefix has length $t$, so its output cannot be the incorrect one-bit membership value. Finally, the output distribution at time $t'$ equals the distribution at time $t$ when every branch has halted by time $t$; therefore the original probability lower bound is preserved.

**Key facts.** `Turing.NDTM.HaltsWithin.mono`, `Turing.FinNDTM.runWith_eq_runWith_take`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`.
