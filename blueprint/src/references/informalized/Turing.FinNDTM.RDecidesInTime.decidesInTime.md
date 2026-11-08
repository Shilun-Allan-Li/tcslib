<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Turing.FinNDTM.RDecidesInTime.decidesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision from one-sided error

**Claim.** Under the stated one-sided-error guarantees, every input's branches halt within the prescribed time, and $x\in L$ exactly when some branch of that length halts with output $[\mathrm{true}]$.

**Proof.** Fix $x$ and take its halting and error guarantees. If $x\in L$, the probability of output $[\mathrm{true}]$ is at least $2/3$, hence positive. Positive output probability supplies a choice word of the prescribed length producing that output (`Turing.FinNDTM.exists_outputWith_of_outputProb_pos`); its run halts by the halting guarantee, so it witnesses acceptance. Conversely, if $x\notin L$, every branch of that length outputs $[\mathrm{false}]$. No such branch can also output $[\mathrm{true}]$, so acceptance implies $x\in L$.

**Key facts.** `Turing.FinNDTM.exists_outputWith_of_outputProb_pos`.
