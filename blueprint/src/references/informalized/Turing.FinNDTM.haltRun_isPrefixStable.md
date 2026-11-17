<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltRun_isPrefixStable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting output is prefix stable

**Claim.** If choices $w$ make the machine halt with output $a$, then appending any choice word $v$ still makes it halt with output $a$.

**Proof.** Assume the halting-run result on $w$ is `some a`. By the characterization of a specified halting output (`Turing.FinNDTM.haltRun_eq_some_iff`), the run after $w$ is halted and has output $a$. The run on $w$ followed by $v$ equals the run on $w$ followed by running the remaining choices from that configuration (`Turing.NDTM.runWith_append`). Since a halted configuration is unchanged by any further choices (`Turing.NDTM.runWith_of_halt`), this extended run is exactly the run after $w$. Its state is therefore still halted and its output is still $a$, so the same characterization gives halting-run result `some a` for the extended word.

**Key facts.** `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
