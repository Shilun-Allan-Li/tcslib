<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryCells_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Summary Cell

**Claim.** Replacing the summary-cell function's value at position zero by $n$ gives the summary-cell function associated with $n$ and $w$.

**Proof.** Compare the functions at an arbitrary position $z$. At $z=0$, the update assigns $n$, and the summary-cell function associated with $n$ also returns $n$. At every $z\ne0$, the update leaves the value unchanged, and both summary-cell functions use the same buffer content for $w$. Hence they agree everywhere.
