<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.timed_input_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Head Position Bound

**Claim.** After $t$ steps from a configuration with input-head position $p$, the input-head position is at most $p+t$.

**Proof.** First, one step can increase the input-head position by at most one. In a nonhalting state, the transition moves the head by one unit, leaves it in place, or moves it backward; the position update also clamps attempted moves at the ends of the input range. In each case the new position is at most the old position plus one. In the halting state the configuration stays fixed, so the same bound holds. Now induct on $t$. At $t=0$ the position is unchanged. For the successor case, the run-after-$t$ configuration takes one further step; applying the one-step bound and then the induction hypothesis gives a position at most $(p+t)+1=p+(t+1)$. The run decomposition used here is that a run of $t+1$ steps is one step followed by a run of $t$ steps ( `runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
