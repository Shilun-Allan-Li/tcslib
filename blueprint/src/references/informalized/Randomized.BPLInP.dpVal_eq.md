<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.dpVal_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dynamic-programming values and acceptance probability

**Claim.** Under the space and code-range bounds, the depth-$t$ value at the code reached after choices $v$ equals $2^t$ times the probability that, after the additional uniform $t$ choices, the machine is halted with output exactly $[1]$.

**Proof.** We induct on $t$, allowing the already-fixed choice word $v$ to vary. At depth zero, the random experiment has just the empty continuation (`randProb_zero`), so its probability is $1$ exactly when the run after $v$ is halted with output $[1]$, and is otherwise zero. The acceptance-characterization lemma (`acceptLang_iff`) identifies this condition with membership of the code of that run in the acceptance language. Thus the base dynamic-programming value, which is the corresponding indicator, agrees with the claimed probability; the factor $2^0$ is one.

For the successor step, fix either next choice bit $b$. In the sum defining the next dynamic-programming value, only the successor code reached by appending $b$ can contribute: the transition characterization (`stepRel_iff`) says that the transition relation holds exactly at that code. This code lies in the summation range because every configuration code is strictly below the stated exponential bound (`cfgCode_lt`), which is at most $V$. Hence the sum for branch $b$ reduces to the depth-$t$ value at the run after $v$ followed by $b$. Apply the induction hypothesis to each of the two branches. The probability recurrence (`randProb_succ`) averages the probabilities for the two possible first continuation bits, while the two branch contributions add. Multiplying that average by $2^{t+1}$ gives exactly the sum of the two depth-$t$ scaled probabilities, proving the successor case.

**Key facts.** `Randomized.BPLInP.randProb_zero`, `Randomized.BPLInP.acceptLang_iff`, `Randomized.BPLInP.stepRel_iff`, `Complexity.Codec.cfgCode_lt`, `Randomized.randProb_succ`.
