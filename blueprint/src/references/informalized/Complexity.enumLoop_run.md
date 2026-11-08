<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumLoop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Candidate-Round Loop

**Claim.** Under the stated terminal and per-round hypotheses, the machine halts within $\mathrm{count}\,B$ steps from rank $i$, outputting true exactly when at least one of the first $\mathrm{count}$ ranks is accepted.

**Proof.** Induct on the number of rounds. With zero rounds, the starting rank is the terminal rank, so time zero already gives the required halted false output. For one or more rounds, the per-round hypothesis at rank $i$ gives a time $t\le B$. If rank $i$ is accepted, the machine halts with true at that time, which is the disjunction over all the rounds. If rank $i$ is not accepted, it reaches the next configuration, at rank $i+1$. Apply the induction hypothesis to the remaining rounds from that configuration, obtaining a further time $s\le\mathrm{count}\,B$. The run-from-addition law (`Turing.MultiTapeTM.runFrom_add`) combines these into a run of $t+s$ steps from rank $i$; it halts with the induction hypothesis's output. Since $t+s\le B+\mathrm{count}\,B=(\mathrm{count}+1)B$, and the disjunction over the current rejected rank and the remaining ranks is exactly the latter disjunction, the claim follows.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
