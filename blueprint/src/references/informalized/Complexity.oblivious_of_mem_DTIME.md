<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.oblivious_of_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oblivious simulation with quadratic overhead

**Claim.** If $T$ is time-constructible and $L$ belongs to $\mathrm{DTIME}(T)$, then an oblivious finite-state binary Turing machine decides $L$ within $c(T(n)+1)^2$ steps for some constant $c$.

**Proof.** Unpack time-constructibility to obtain a clock machine $W$, a constant $b$, and the lower bound $n\le T(n)$. Unpack $L\in\mathrm{DTIME}(T)$ to obtain a machine $M$ and constant $a$ such that $M$ decides $L$ within $aT(n)$ steps. The candidate-machine correctness result (`obliviousCandidate_decides`) shows that the schedule construction using $W$, $M$, and $a$ decides $L$ within $[18(a+1)^2+23(a+1)+3b+25](T(n)+1)^2$ steps. The candidate’s obliviousness is supplied by `obliviousCandidate_oblivious`. Choosing the displayed coefficient as $c$ gives the conclusion.

**Key facts.** `Complexity.obliviousCandidate_decides`, `Complexity.obliviousCandidate_oblivious`.
