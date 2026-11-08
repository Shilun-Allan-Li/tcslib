<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitEmit_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling pass of the split emitter

**Claim.** For every $j\le |s|$, after $2j$ steps the split emitter is in control state $0$, with input and counter positions both $j$, and output equal to the concatenation of two copies of each of the first $j$ bits of $w$.

**Proof.** Induct on $j$. At $j=0$ the initial configuration has the stated form. For the successor step, the hypotheses give $j<|s|\le |w|$, so both the counter tape and input head read the bit $w_j$. The transition from state $0$ emits this bit and enters state $1$, leaving both positions unchanged. The transition from state $1$ emits the same input bit again, advances the input head and counter head by one, and returns to state $0$. The new output is therefore the old output followed by two copies of $w_j$. Since the first $j+1$ bits of $w$ consist of its first $j$ bits followed by $w_j$, this is exactly the claimed output for $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.splitPos_read`, `Turing.moveInputPos_zero`, `Turing.FinTM.splitPos_succ`.
