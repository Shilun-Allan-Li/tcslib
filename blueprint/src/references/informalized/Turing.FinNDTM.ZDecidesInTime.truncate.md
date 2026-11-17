<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.ZDecidesInTime.truncate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-horizon success probability bound

**Claim.** For every input $x$ and positive horizon $t$, every halting choice word produces the correct output, and the probability of halting with that output at horizon $t$ is at least $1-T(|x|)/t$.

**Proof.** Fix $x$ and $t>0$. If a choice word halts with output $o$, the halting characterization `haltRun_eq_some_iff` identifies this with a halting run whose output is $o$. The correctness hypothesis therefore makes $o$ the required indicator. For the probability estimate, prefix stability of the halting event (`haltRun_isPrefixStable`) and the total nonhalting bound imply that the probability of still not having halted at horizon $t$ is at most $T(|x|)/t$ (`notHaltedProb_le_div`). The event of halting with the correct output is exactly the complement of the nonhalting event: a halting run has the correct output by the first part, and a nonhalting run yields no output. The complement rule for uniform probability (`randProb_not`), together with event equality (`randProb_congr`), thus gives success probability $1-\Pr[\text{not halted}]$. Substituting the upper bound on the latter proves the claimed lower bound.

**Key facts.** `Turing.FinNDTM.haltRun_eq_some_iff`, `Turing.FinNDTM.haltRun_isPrefixStable`, `Randomized.notHaltedProb_le_div`, `Turing.FinNDTM.haltRun_eq_none_iff`, `Randomized.randProb_not`, `Randomized.randProb_congr`.
