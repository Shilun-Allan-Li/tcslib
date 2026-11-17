<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.toEnd_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run to the End of a Tape Word

**Claim.** Under the stated transition behavior, starting at state $c_R$ with register $r$ holding $w$ and its head at $p$, after $n+1$ steps the program is in state $n_x$ with the head at $|w|-1$. At every earlier time $t<n+1$, it remains in state $c_R$, still holds $w$ on register $r$, and its head is at some $q$ with $p\le q\le |w|$.

**Proof.** We induct on $n$, with the statement quantified over the starting head position $p$. If $n=0$, the equation $|w|-p=0$ gives $p=|w|$. At this position the buffer tape reads no symbol. The prescribed transition therefore moves left into state $n_x$ and places the head at $|w|-1$. The only earlier time is zero, when the starting configuration itself supplies the required position and bounds. Now suppose $n$ is positive. Since $p\ge0$, write $p=j$ for a natural number; the equation $|w|-p=n$ implies $j<|w|$. Thus the tape reads the symbol of $w$ at index $j$. The prescribed transition, together with the fact that $c_R$ is not a call state, performs one ordinary step: it keeps state $c_R$ and the tape word unchanged, and advances the head from $p$ to $p+1$. The register-read identity identifies the scanned symbol, and the register-action identity gives this updated configuration. Apply the induction hypothesis from position $p+1$, where the remaining distance is $n$. The run-addition law separates the first step from these remaining $n+1$ steps, yielding the claimed final configuration. For an earlier time $t$, either $t=0$, which is the original configuration, or $t=1+t'$ for an earlier time in the run starting at $p+1$. In the latter case induction supplies a position $q$ with $p+1\le q\le |w|$ and the required configuration; hence also $p\le q\le |w|$.

**Key facts.** `Complexity.LogProg.rrun_one_reg`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.rrun_add`.
