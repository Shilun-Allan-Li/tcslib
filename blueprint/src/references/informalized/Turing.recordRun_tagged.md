<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordRun_tagged -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tagged Run Satisfies Recorded-Run Conditions

**Claim.** Under the stated run-agreement, endpoint, phase-index, and head-distance hypotheses, the tagged run from $a$ to $b$ satisfies the recorded-run conditions through time $t+1$.

**Proof.** The endpoint condition is exactly the assumed equality of the hosted run at time $t+1$ with $b$. For any earlier time $u<t+1$, we have $u\le t$, so the agreement hypothesis identifies the hosted configuration with the run of $M$ after tagging its state by $i$. The tagged-state separation fact (\(\texttt{Turing.record_tag_ne}\)) says that a configuration tagged by $i$ cannot have state equal to either distinguished state when $i$ differs from both of their phase indices. This proves the required avoidance. For the head-distance bound, take any $u\le t+1$. If $u\le t$, run agreement transfers the bound from the run of $M$ to the hosted run. Otherwise $u=t+1$, and the endpoint equality identifies the configuration with $b$, where the assumed endpoint bound applies.

**Key facts.** `Turing.record_tag_ne`.
