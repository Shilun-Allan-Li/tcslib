<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitEmit_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator emission of the split emitter

**Claim.** Starting in state $0$ with both head positions equal to $|s|$ and output $out$, after two steps the emitter is in state $3$, the positions are unchanged, and the output is $out$ followed by $0,1$.

**Proof.** At counter position $|s|$, the first work tape reads no symbol, since its contents come from the finite word $s$. In state $0$ with this blank reading, the machine emits $0$ and enters state $2$ without moving either head. In state $2$, it emits $1$ and returns to state $3$, again leaving the positions unchanged. The output updates by appending each emitted bit, so after the two steps it is $out$ followed by $0,1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_zero`.
