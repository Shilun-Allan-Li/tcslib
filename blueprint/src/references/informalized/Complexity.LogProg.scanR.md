<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.scanR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Rightward Scan

**Claim.** Under the stated transition and no-call hypotheses, after each of the first $k$ steps the machine is in state $\sigma_j$, its input head is at $q_0+j$, and register $r$'s head remains at $p$, with all other configuration data unchanged.

**Proof.** Induct on the number $j$ of steps. At $j=0$, the claim is exactly the definition of the starting configuration. For the induction step, use the induction hypothesis to identify the configuration after $j$ steps. Since $j<k$, the no-call assumption ensures this step uses the ordinary machine transition. The transition hypothesis says that, regardless of the scanned work-tape symbols, it is the action that enters $\sigma_{j+1}$, moves the input head right, and leaves every work-tape head and tape, as well as the output, unchanged. The head-position bound ensures the input head is not at the right boundary: if its position is $q_0+j$, then $q_0+j+1\le |x|+1$. Thus a right move sends it to $q_0+j+1$. These facts give the claimed configuration after $j+1$ steps.

**Key facts.** `Complexity.LogProg.rrun_succ`, `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`.
