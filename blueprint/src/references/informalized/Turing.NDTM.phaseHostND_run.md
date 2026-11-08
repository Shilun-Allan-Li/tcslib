<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.NDTM.phaseHostND_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase Host Run Behavior

**Claim.** Under the stated condition that no redirection occurs at any proper-prefix state, the phase-host run agrees with the phase-$i$ run throughout every prefix of $w$. One further choice bit then takes the host run from the terminal state $s'$ to the prescribed redirected state $q'$, while leaving the other configuration data as in $c'$.

**Proof.** Embed each phase-$i$ state $s$ as the tagged state $(i,s)$. Whenever redirection at $(i,s)$ is absent, the host transition is precisely the phase-$i$ transition with its successor state tagged by $i$; this is the transition-agreement hypothesis needed for the run comparison. For any $u\le |w|$, every proper prefix of the first $u$ bits is also a proper prefix of $w$. The guard therefore ensures that each state encountered before those $u$ steps has no redirection. The run comparison theorem for machines whose transitions agree on all states encountered along the run (`Turing.NDTM.runWith_mapState_of_agreeOn`) now gives agreement for that prefix, with states tagged by $i$.

For the final assertion, split the choice word as $w$ followed by $b$. The run-concatenation law (`Turing.NDTM.runWith_append`) reduces this to the host run under $w$, followed by one step. The prefix result at $u=|w|$, together with the given equation that the phase-$i$ run under $w$ ends at $c'$, identifies the host configuration there as $c'$ with its state tagged $(i,s')$. Since redirection at $s'$ is $q'$, the next host transition uses the redirection action, which leaves the tape contents, head positions, input position, and output unchanged and replaces the state by $q'$. This is exactly $c'$ with its state replaced by $q'$.

**Key facts.** `Turing.NDTM.runWith_mapState_of_agreeOn`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`.
