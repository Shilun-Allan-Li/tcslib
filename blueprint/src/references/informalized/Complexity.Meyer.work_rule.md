<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.work_rule -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Update Rule

**Claim.** Within the stated time and offset bounds, the encoded tape symbol at time $t+1$ equals the machine’s work-tape update rule applied to the configuration and reads at time $t$, with the time-$t$ encoding as the old tape contents.

**Proof.** Let $c$ be the configuration after $t$ steps. Apply the one-step edge statement twice: first at offset $d$, and then at offset $d-1$. The address bound for each application follows from the hypothesis on $|d|+t+1$, using `aE_add_one` to translate between the signed offset and its encoded address. The first application handles the unchanged and positive-movement cases directly. If the movement is negative, the second application gives the needed equation at $d-1$, which is the same as the value at $d$ after the head shifts left.

Now split on whether the configuration is halting. In that case the edge equation says the tape value is retained, exactly as the rule specifies. Otherwise split on the movement. With zero movement, the edge equation at $d$ is the rule’s choice between the prescribed write at the scanned cell and the old value at $d$. With positive movement, it gives that same choice at the cell whose offset from the new head is $d$. With negative movement, the equation from the second edge application gives the choice at that cell; the integer identity $(d-1)+1=d$ aligns it with the rule’s shifted offset. In every case the write-or-retain option is the transition’s prescribed one, so the resulting equation is the definition of the work-tape update rule.

**Key facts.** `Complexity.Meyer.aE_add_one`, `Complexity.Meyer.work_edge`.
