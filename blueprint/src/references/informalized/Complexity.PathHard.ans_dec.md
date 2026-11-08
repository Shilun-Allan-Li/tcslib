<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.ans_dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting with a prescribed Boolean answer

**Claim.** If the initial registers are bounded by $B$ and the Boolean labels $q$ and $p$ agree, the machine started in the answer state for $q$ halts with result $p$, with the guard holding at every earlier time.

**Proof.** Since $q=p$, it suffices to consider the two possible Boolean values of $q$. If $q$ is false, the initial label is the false-answer state; if $q$ is true, it is the true-answer state. In either case, the answer-state halting result (`ans_halt`) applies: the register bound supplies the guard initially, the machine returns the state’s Boolean answer, and the guard holds at every earlier time. This answer is $q$, hence also $p$.

**Key facts.** `Complexity.PathHard.ans_halt`.
