<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.dec_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Decrement Computation

**Claim.** The compiled decrement routine transforms the register from the binary expansion of $n$ to the binary expansion of $n-1$, with truncated subtraction, and its intermediate configurations satisfy the stated phase, call, and head-position bounds.

**Proof.** Apply the unary decrementing run invariant to the canonical word $\operatorname{bits}(n)$ with empty prefix. It yields a time $T_1$ and a head position $p$ where the register contains $\mathrm{decW}(\operatorname{bits}(n))$ and the run has entered the increment-back phase. The identity relating decremented binary expansions to predecessor expansions (`bits_pred`) identifies these contents with $\operatorname{bits}(n-1)$. The head bound from that invariant gives $p<|\operatorname{bits}(n-1)|$, which permits the increment-back run theorem to be applied starting at position $p$; that run returns the head to zero and reaches the required successor state. Concatenating the two runs using the run-addition law gives the claimed total time and final configuration. Before time $T_1$, the decrement invariant supplies the required intermediate configurations; from time $T_1$ onward, the increment-back invariant supplies them, and the call-free hypothesis at its phase ensures the required no-call condition. The binary-length monotonicity bound transfers its head upper bound from $|\operatorname{bits}(n-1)|$ to $|\operatorname{bits}(n)|$.

**Key facts.** `Complexity.LogProg.canon_bits`, `Complexity.LogProg.decD_run`, `Complexity.LogProg.bits_pred`, `Complexity.LogProg.incB_run`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.rrun_add`.
