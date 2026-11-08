<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMax_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of maximum-pass machine

**Claim.** For every CNF formula $\varphi$, the intercepted maximum-pass machine reaches the specified streaming entry configuration on its serialization by time $3|\mathrm{enc}(\varphi)|+5$.

**Proof.** The startup lemma for the reduction machine supplies a time $t$ within the stated bound at which that machine reaches the entry configuration, with counter length $N(\varphi)$, its initialized buffer, both heads at zero, and empty output (Complexity.satRed_start). Since the output at this time is empty, the guard lemma ensures that the reduction machine did not enter state $9$ at any earlier step (Complexity.satRed_start_guard). Before that state is reached, the intercepted maximum-pass machine has the same transitions as the reduction machine. Hence the two runs agree through time $t$, by the run-agreement lemma (Complexity.sat_run_agree), and the maximum-pass machine reaches the same entry configuration at the same bounded time.

**Key facts.** `Complexity.satRed_start`, `Complexity.satRed_start_guard`, `Complexity.sat_run_agree`.
