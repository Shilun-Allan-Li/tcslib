<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.erase_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing a Tape Segment

**Claim.** Under the stated tape and head-position hypotheses, the erase phase finishes after $n+1$ steps in the back phase with the selected data and mark tapes adjusted to the endpoint, and throughout those steps all work-tape head positions stay within the bound $B$.

**Proof.** Proceed by induction on $n$. At each stage let $p$ be the selected data-tape head position. The assumptions give $p-(a-1)=n$ at the current stage and ensure that the selected data tape is $f$ up to $p$ and blank above, while the mark tape marks the origin and the interval from $a$ to $p$.

For $n=0$, the head is at $a-1$. The mark there is absent, so the erase transition switches directly to the back phase and places the data and mark heads at $a$. Since the data content already agrees with $f$ through $a-1$ and is blank above, it is the required erased content. The corresponding mark tape is the prescribed one through $a-1$. The head bound at this endpoint follows because $a$ is one step from the old position and the assumptions give $-B\le a-1$ and $a\le0$; all other heads are unchanged. The initial configuration satisfies the bound by the configuration bound for these tape positions, and the endpoint does too.

For the successor case, the head is at some $p\ge a$. One erase step moves the selected heads left to $p-1$, blanks the data cell at $p$, and removes the mark there. This leaves the same hypotheses with distance reduced by one: the data tape now agrees with $f$ through $p-1$ and is blank above, and the marks describe the interval from $a$ to $p-1$. If $p=0$, the mark at $p$ is the special origin mark; otherwise it is an interval mark. These two possibilities give exactly the stated update in either case. The new head position remains within $B$ because it is one step closer to the interval endpoint already bounded by the hypotheses; the other heads do not move. Apply the induction hypothesis to this updated configuration. Every positive-time configuration in the original run is a configuration in that shorter run, while time zero satisfies the bound directly. The induction endpoint, preceded by the first erase step, is the asserted back-phase configuration at time $n+1$.

**Key facts.** `Complexity.LogProg.PB_ccfg`, `Complexity.LogProg.abs_update_le`, `Complexity.LogProg.ccfg_state`, `Complexity.LogProg.ccfg_mark`, `Complexity.LogProg.apply_clAct`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
