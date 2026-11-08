<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitEmit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete run of the split emitter

**Claim.** After exactly $|s|+|w|+3$ steps, the split emitter is halted, its input-head position is $|w|$, its counter-head position is $|s|$, and its output is the self-delimiting encoding of the prefix of $w$ of length $|s|$ and the remaining suffix.

**Proof.** Rewrite the total time as $2|s|+2+(|w\mathbin{\mathrm{drop}}|s||+1)$, using the length formula for a dropped list. The doubling-pass result shows that the first $2|s|$ steps emit two copies of each bit in the prefix of length $|s|$, leaving the emitter in state $0$ with both positions at $|s|$. The two-step separator result then appends $0,1$ and enters state $3$. Now write $w$ as its prefix of length $|s|$ followed by its dropped suffix. The suffix-copying result says that in state $3$ the machine copies that suffix to the output, advances the input head to the end of $w$, and halts after one step per suffix bit plus one final step. Combining these phases gives the stated time and configuration; the output is the doubled prefix, followed by the separator, followed by the suffix, which is precisely the pair encoding.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.splitEmit_double`, `Turing.FinTM.splitEmit_separator`, `Turing.FinTM.splitEmit_suffix`.
