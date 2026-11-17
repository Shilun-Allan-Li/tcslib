<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_agree_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement before an anchor visit

**Claim.** If two deterministic machines have identical transitions outside the designated state, and the stopped machine's run avoids that state at every time before $t$, then their configurations after $t$ steps from the same configuration agree.

**Proof.** We argue by induction on $t$. At time zero both runs are at the initial configuration. For the successor step, apply the induction hypothesis to the first $t$ steps; its avoidance hypothesis follows by restricting the given condition to times $j<t$. Thus the two machines are in the same configuration at time $t$. If this configuration is halted, both steps leave it unchanged. Otherwise its state is some $q$. The avoidance assumption at time $t$ gives $q\ne q_a$, so the transition functions agree on this state and hence, because the configurations and their tape readings agree, the next configurations agree as well. The successor-step identity for runs, which identifies a run of length $t+1$ with one step after the run of length $t$, is the fact used here (\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
