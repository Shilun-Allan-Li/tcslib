<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.lane_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution across a finite transduction

**Claim.** Under the stated transition rule, running the machine for the length of $as$ processes those letters in order: it reaches the transducer's final state, advances the frontier by $|as|$, puts the encoded rewritten letters in reverse order on the left list before $l$, and leaves $r$ on the right.

**Proof.** Proceed by induction on the list $as$, generalizing the initial transducer state, frontier, and left list. For the empty list, zero steps leave the lane configuration unchanged, and folding the transition map over the empty list returns the initial state and an empty rewritten list (\(\texttt{Turing.MultiTapeTM.runFrom_zero}\)). For a nonempty list $a::as$, the lane-reading property shows that the designated head reads the encoding of $a$ at the right-list head (\(\texttt{Complexity.laneCfg_read}\)). The assumed transition rule therefore makes the first machine step exactly the action that writes the rewritten letter, moves right, and enters the next encoded state. The rightward lane-update identity gives the lane configuration with frontier advanced by one, that rewritten letter prepended to the left list, and the remaining letters followed by $r$ on the right (\(\texttt{Complexity.laneCfg_right}\)). The induction hypothesis processes the remaining list from this configuration. The recursive definition of the fold records the rewritten letters in processing order; reversing them and prepending to the left list yields the stated left list, while the frontier advances by the total list length. The successor-run identity identifies the original run with this first step followed by the remaining run (\(\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step}\)).

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.laneCfg_read`, `Complexity.laneCfg_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
