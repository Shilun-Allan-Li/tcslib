<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.two_point_rpow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-point power bound for large exponents

**Claim.** For $q\ge2$ and all real $a,t$, the average of $|a+t|^q$ and $|a-t|^q$ is at most $(a^2+(q-1)t^2)^{q/2}$.

**Proof.** Set $s=\sqrt{q-1}>0$ and consider the one-bit function whose two Fourier coefficients are $a$ at the empty set and $st$ at the singleton. The one-bit value formulas identify its values as $a+st$ and $a-st$. Its noise at parameter $1/s$ has Fourier coefficients $a$ and $t$, so its values are $a+t$ and $a-t$. Apply one-bit $(2,q)$ hypercontractivity and use the formula expressing the one-bit expectation of an absolute power as the average over these two values. This gives the desired comparison after raising both sides to the positive power $q$. The squared two-point average on the input side simplifies to $a^2+s^2t^2=a^2+(q-1)t^2$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.one_bit_val_false`, `BooleanAnalysis.Hypercontractivity.one_bit_val_true`, `BooleanAnalysis.noiseOp_fourier`, `BooleanAnalysis.Hypercontractivity.one_bit_2q_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit`.
