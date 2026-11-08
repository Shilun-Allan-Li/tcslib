<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_carry_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Carry-Phase Step

**Claim.** From state $1$ with tape word $a$ followed by $b$, one step either propagates a carry through a leading $1$ or writes $1$ at the first non-$1$ position and enters state $2$, with the stated head movements and unchanged input and output.

**Proof.** The transition table in state $1$ applies the bump operation to the symbol under the work head. The tape-reading fact says that this symbol is the head of $b$ ($\texttt{counterTape_read}$). If that head is $1$, the transition stays in state $1$, writes $0$, and moves right; if it is not $1$ (including when the suffix is empty), it enters state $2$, writes $1$, and moves left. In either case, the write-at-prefix-boundary identity shows that the resulting tape is the prefix followed by the written bit and the tail of $b$ ($\texttt{counterTape_write}$). The input head stays fixed because its movement is zero ($\texttt{moveInputPos_zero}$); the work-head positions follow from adding the prescribed unit movement, while output remains empty.

**Key facts.** `Complexity.counterTape_read`, `Complexity.counterTape_write`, `Turing.moveInputPos_zero`.
