<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryCells_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the Summary Word Region

**Claim.** Assigning the shifted buffer content on $2\le z<2+|w|$ and the empty-word summary-cell content elsewhere yields the summary-cell function for $s$ and $w$.

**Proof.** It suffices to compare the two functions at each integer $z$. First consider $z=0$: the interval condition fails, and both summary-cell functions return $s$. Now suppose $z\ne0$. If $z$ is in the stated interval, the summary-cell function for $w$ returns the buffer content at $z-2$, exactly as assigned. If $z$ is outside the interval, then $z-2$ is either negative or at least $|w|$. The buffer tape is blank outside the word's index range (`bufferTape_outside`), so the summary-cell content for $w$ agrees with that for the empty word at this cell. This proves equality in every case.

**Key facts.** `Turing.StepBlock.bufferTape_outside`.
