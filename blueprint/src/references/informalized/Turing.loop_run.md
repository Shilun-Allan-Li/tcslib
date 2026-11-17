<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.loop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded computation over successive rounds

**Claim.** Under the stated empty-output, terminal-round, and per-round hypotheses, the machine started at $c_0$ halts within $(N+1)B$ steps and outputs the bit indicating whether $a(j)$ is true for some $j<N$.

**Proof.** Proceed by induction on $N$, generalizing the configuration sequence and predicate so that the induction hypothesis can be applied to a shifted sequence. When $N=0$, the terminal-round hypothesis directly gives a halt within $B=(0+1)B$ steps with output false, matching the empty-range disjunction. Now let $N$ be positive and inspect the first round, obtaining a run of length $t\le B$ from $c_0$. If $a(0)$ is true, this run halts with output true. Its time is at most $(N+1)B$, and the disjunction over the first $N+1$ indices is true. If $a(0)$ is false, the run reaches $c_1$. Apply induction to the shifted configurations $c_{j+1}$ and shifted predicate $a(j+1)$, using the same terminal run and the remaining round hypotheses. It gives a run of length $s\le (N+1)B$ from $c_1$, halting with the disjunction over indices $1$ through $N$. Concatenate the first run and this run: the run-addition law identifies their combined run from $c_0$ with a run of length $t+s$ (`MultiTapeTM.runFrom_add`). The sum is at most $(N+2)B$, and the disjunction over indices $0$ through $N$ reduces to the tail disjunction because $a(0)$ is false. In each branch the output is the required single bit.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
