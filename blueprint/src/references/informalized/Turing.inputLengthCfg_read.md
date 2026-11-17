<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLengthCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Buffered Input

**Claim.** If the original tape is blank from one cell before the work-head position through $N$ cells after it, then overlaying $w$ across the interval of length $|w|$ makes every cell in that range read exactly the buffer value for its offset.

**Proof.** At offset $a$, the overlay construction tests whether the absolute cell lies in the interval beginning at the work-head position and extending for $|w|$ cells. When it lies there, the constructed tape returns the buffer value at offset $a$ by definition. Otherwise, the assumed blankness of the original tape supplies the value $\mathrm{none}$. In this outside case, either $a<0$, where the buffer is blank by definition, or $a\ge |w|$, where the list lookup is out of range and hence blank. Therefore the constructed tape and the buffer agree in both cases.
