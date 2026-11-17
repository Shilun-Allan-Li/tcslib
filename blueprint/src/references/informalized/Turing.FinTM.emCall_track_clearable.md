<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_clearable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Interval Cleaner's Time Bound

**Claim.** The three-tape cleaner can erase the data, marker, and origin tapes and return all heads to the origin in state $3$, in a positive number of steps at most $6T+7$, from the stated configuration.

**Proof.** Let $\ell$ and $h$ be the extreme head positions through time $T$, and let $a$ be the head position at time $T$. The tracking extent fact (Turing.FinTM.emCall_track_extent) gives $\ell\le0\le h$, places $a$ in $[\ell,h]$, and bounds both extremes in absolute value by $T$. Thus the interval width $w=(h-\ell+1)$ is positive and at most $2T+1$; the offset $j=a-\ell$ satisfies $j<w$. The tracking support fact (Turing.FinTM.emCall_track_support) says the data tape is blank outside this span. Apply the cleaner run result (Turing.FinTM.emCall_clear_run) to the interval starting at $\ell$, width $w$, and offset $j$. Its hypotheses hold by the extent and support facts, and it supplies a positive cleaning time at most $3w+4$, hence at most $6T+7$. Finally, the closed-span-to-half-open-interval identity (Turing.FinTM.emCall_span_interval) identifies the cleaner's marker tape with the stated closed-span marker, and $\ell+j=a$ identifies its starting head position with the given time-$T$ position. The cleaner's conclusion is therefore exactly the required cleared configuration.

**Key facts.** `Turing.FinTM.emCall_track_extent`, `Turing.FinTM.emCall_track_support`, `Turing.FinTM.emCall_clear_run`, `Turing.FinTM.emCall_span_interval`.
