<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.RDecidesInTime.bpDecidesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded error from one-sided error

**Claim.** Under the stated one-sided-error guarantees, the machine halts within the given time on every input and outputs the correct membership indicator with probability at least $2/3$.

**Proof.** Fix an input $x$ and use its halting and one-sided-error guarantees. If $x\in L$, the membership indicator is true, so the required probability bound is exactly the assumed lower bound for output $[\mathrm{true}]$. If $x\notin L$, every branch of the specified length outputs $[\mathrm{false}]$. Therefore the probability of output $[\mathrm{false}]$ is $1$ (`Turing.FinNDTM.outputProb_eq_one`), which is at least $2/3$; this is the probability of the correct indicator in this case. The halting part is already among the hypotheses.

**Key facts.** `Turing.FinNDTM.outputProb_eq_one`.
