<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending One Computation Step

**Claim.** If one step takes $a$ to $a_1$, the state of $a$ avoids $F$, $P$ holds at $a$'s head positions, and there is a segment from $a_1$ to $b$ of length $t$, then there is a segment from $a$ to $b$ of length $1+t$.

**Proof.** First, the segment from $a_1$ to $b$ guarantees that $P$ holds at its time-zero configuration. Since a run of zero steps leaves $a_1$ unchanged (`Turing.MultiTapeTM.runFrom_zero`), this says that $P$ holds at $a_1$'s head positions. The one-step segment result now applies to the step from $a$ to $a_1$: the state of $a$ avoids $F$, and $P$ holds at both $a$ and $a_1$ (`Turing.Segment.one`). Concatenate this one-step segment with the given length-$t$ segment (`Turing.Segment.trans`). The resulting length is $1+t$, as claimed.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.Segment.one`, `Turing.Segment.trans`.
