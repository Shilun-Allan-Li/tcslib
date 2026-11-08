<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NTIME.lean :: Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Simulation and Acceptance

**Claim.** If the deterministic machine computes the indicator of $L$ on $x$ within $t$ steps, then every length-$t$ choice sequence of its associated nondeterministic machine halts on $x$, and $x\in L$ exactly when some such sequence halts with output $[1]$.

**Proof.** The computation-time hypothesis says that the deterministic run is halted at time $t$ and has output equal to the indicator of membership (`computesInTime_iff`). For every choice list $w$, the nondeterministic run agrees with the deterministic run after $|w|$ steps (`toNDTM_runWith`). Thus every list of length $t$ yields a halted run. If $x\in L$, choose the length-$t$ list consisting entirely of false choices; its run halts and its output is the indicator value $[1]$. Conversely, suppose a length-$t$ choice list halts with output $[1]$. Its run agrees with the deterministic run at time $t$, so the deterministic output is $[1]$. Since that output is the indicator of membership, $x\notin L$ would instead give output $[0]$, a contradiction. Hence $x\in L$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.toNDTM_runWith`.
