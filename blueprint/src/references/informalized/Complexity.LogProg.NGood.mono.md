<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.NGood.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Good Runs

**Claim.** If the good-run conditions hold through time $T$ and $T\le T'$, then they hold through time $T'$.

**Proof.** First observe that any run of length at least $T$ agrees with its length-$T$ prefix: the prefix run is halted by the terminal condition at time $T$, and a halted run remains unchanged when further choices are appended. More precisely, decompose the choice word into its first $T$ choices and the remaining suffix; the run concatenation law and the fact that runs from a halted configuration stay fixed give this equality (`runWith_append_of_halt`). Now consider the two requirements at time $T'$. For the box condition on a word of length at most $T'$, if its length is below $T$, use the original box condition directly. Otherwise replace its run by that of its length-$T$ prefix and apply the original box condition to that prefix. For a word of length exactly $T'$, its length-$T$ prefix has a halted endpoint satisfying $Q$; the same run equality identifies this endpoint with the full run, so the terminal condition follows.

**Key facts.** `Complexity.LogProg.runWith_append_of_halt`.
