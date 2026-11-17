<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.visited_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions Form an Interval

**Claim.** For each work tape, the positions visited from time $0$ through time $T$ form an integer interval with endpoints $a\le 0\le b$, and both endpoints are visited.

**Proof.** Let $U$ be the finite set of head positions visited through time $T$. It contains $0$, since the initial work-tape head position is $0$, so it is nonempty. Take $a$ and $b$ to be the minimum and maximum of $U$. They are visited, and the defining properties of minimum and maximum give $a\le 0\le b$ and show that every visited position lies between them.

It remains to show every integer between $a$ and $b$ is visited. Write $p(t)$ for the head position at time $t$. The initial position is $p(0)=0$. By the successor-time identity for a run, the next configuration is obtained by one machine step; the head-position step bound therefore gives $|p(t+1)-p(t)|\le 1$ at every time. Also, by the definition of $U$, every element of $U$ equals $p(t)$ for some $t\le T$.

If $0\le z\le b$, choose a time at which the maximum $b$ is attained. The discrete path result `exists_eq_of_between` says that a sequence starting at zero and changing by at most one at each step must attain every integer between zero and that endpoint. Thus $p$ attains $z$ no later than the time at which it attains $b$, hence by time $T$, so $z\in U$. If $a\le z\le 0$, apply the same result to a time at which the minimum $a$ is attained; it yields a time no later than that one at which $p$ equals $z$. Therefore every integer in $[a,b]$ belongs to $U$, proving the claimed interval description.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.MultiTapeTM.ConfigCount.exists_eq_of_between`.
