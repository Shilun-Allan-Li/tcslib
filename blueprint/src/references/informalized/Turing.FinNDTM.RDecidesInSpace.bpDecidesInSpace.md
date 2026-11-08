<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.RDecidesInSpace.bpDecidesInSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Error Gives Bounded Error

**Claim.** A machine with the stated one-sided error and space bound satisfies the corresponding bounded-error decision condition with the same space bound.

**Proof.** The one-sided decision hypothesis already supplies the required space bound, so retain it. Fix an input $x$ and take its time $T$, halting guarantee, and one-sided probability properties. If $x\in L$, the membership indicator is true, and the given lower bound on the probability of outputting $[\mathrm{true}]$ is exactly the required bound. If $x\notin L$, every branch of length $T$ outputs $[\mathrm{false}]$. Hence that output has probability $1$ (\texttt{outputProb_eq_one}); since the membership indicator is false, this is the probability required by the bounded-error condition, and in particular it is at least $2/3$.

**Key facts.** `Turing.FinNDTM.outputProb_eq_one`.
