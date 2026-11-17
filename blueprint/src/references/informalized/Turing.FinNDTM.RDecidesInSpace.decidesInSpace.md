<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.RDecidesInSpace.decidesInSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision from one-sided error

**Claim.** Under the stated space bound and one-sided error guarantees, every input has a time bound by which all branches halt and use the prescribed space, and membership in $L$ is equivalent to the existence of an accepting branch of that length.

**Proof.** Fix an input $x$ and take the time $T$ and guarantees supplied by the hypothesis. Every branch of length $T$ halts by the halting guarantee, and the space bound follows directly from the machine's assumed space usage. If $x\in L$, the probability of output $1$ is at least $2/3$, hence is positive. Positive output probability implies that some choice word of length $T$ produces output $[\mathrm{true}]$ (existence from positive output probability, `Turing.FinNDTM.exists_outputWith_of_outputProb_pos`). Its run halts by the chosen time's halting guarantee, so it witnesses acceptance. Conversely, if a length-$T$ branch halts with output $[\mathrm{true}]$ but $x\notin L$, the false-instance guarantee says that branch outputs $[\mathrm{false}]$. These two outputs differ, a contradiction. Thus an accepting branch exists exactly for inputs in $L$.

**Key facts.** `Turing.FinNDTM.exists_outputWith_of_outputProb_pos`.
