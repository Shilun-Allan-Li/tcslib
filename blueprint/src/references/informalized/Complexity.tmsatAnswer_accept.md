<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsatAnswer_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from the bounded-run answer

**Claim.** The answer word formed from the decoded machine’s run after $t$ steps is $11$ exactly when that machine computes the one-bit output $1$ from $x$ within $t$ steps.

**Proof.** The characterization of timed computation (`Turing.FinTM.computesInTime_iff`) says that computing $[1]$ in time $t$ is equivalent to the configuration after $t$ steps being halted and having output $[1]$. If it is halted, the answer construction prefixes its output by $1$, so the answer is $11$ exactly when the output is $1$. If it is not halted, the answer is the one-bit word $0$, which is not $11$. These two cases establish both directions.

**Key facts.** `Turing.FinTM.computesInTime_iff`.
