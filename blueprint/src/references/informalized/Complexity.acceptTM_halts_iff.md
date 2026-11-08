<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.acceptTM_halts_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recognizer Halting and Acceptance

**Claim.** The halting recognizer of $M$ halts on $x$ within some finite time with some output if and only if $p(x)=\mathrm{true}$.

**Proof.** Suppose first that the recognizer halts at time $t$. By the characterization of computation at a fixed time (`Turing.FinTM.computesInTime_iff`), its state at time $t$ is halting. The run correspondence (`Complexity.acceptTM_run`) identifies that configuration with the recognizer configuration constructed from $M$'s configuration at time $t$. By the definition of the recognizer's state encoding, this can be halting only if $M$ itself is in its halting state; indeed, if $M$ still has a state, the encoded state remains nonhalting. Thus $M$ halts at time $t$. Its run at that time is a computation of its actual output, and the uniqueness of output across halting computations (`Turing.FinTM.ComputesInTime.output_unique`) identifies that output with $[p(x)]$, using the assumed computation of $p$. Since the recognizer's halting state in this case requires the recorded Boolean to be true, the last output bit of $M$ is true; the identified output $[p(x)]$ therefore gives $p(x)=\mathrm{true}$. Conversely, assume $p(x)=\mathrm{true}$. Choose a time at which $M$ computes $[p(x)]$. The fixed-time characterization gives both that $M$ has halted and that its output is $[p(x)]$. The run correspondence then shows that the recognizer's encoded state is halting: its recorded bit, obtained from the last output symbol (defaulting to false if there is none), is true. Its recognizer configuration has output the empty list, so it witnesses halting within that time with some output.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.acceptTM_run`, `Turing.FinTM.ComputesInTime.output_unique`.
