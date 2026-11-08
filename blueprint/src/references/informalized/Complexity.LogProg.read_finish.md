<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the reading routine

**Claim.** Starting at input position $\min(i,|x|)+1$ with tape $s$ holding the binary representation of $\min(i,|x|)$, the read program reaches the exit state carrying $x[i]?$, with input position $1$ and the head of tape $s$ at $0$. Every earlier configuration lies in the read frame.

**Proof.** Set $k=\min(i,|x|)$ and start the comparison phase. By `read_eq`, after a finite run the program is in phase $yes$ if $k=i$ and phase $no$ otherwise, with all earlier configurations in the read frame. One more step advances to $rw_1(x[i]?)$: when $k=i$, the input position $k+1$ scans exactly the $i$th symbol, by the input-symbol successor identity (`inSym_succ`). When $k\ne i$, necessarily $k=|x|$ and $i\ge |x|$, so the scanned input is blank and the out-of-range list lookup is also blank. In either case the transition gives the stated phase and carried value (`read_one`). Apply the cleanup result (`read_cleanup`) from that phase to reach the exit state with head position $0$ on tape $s$. Concatenate the comparison, single-step, and cleanup runs using `rrun_add`. For times before the comparison ends, retain its frame bound; at the comparison endpoint use `readFrame_at`; for later times, shift the time past the one-step transition and apply the cleanup frame bound.

**Key facts.** `Complexity.LogProg.read_eq`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.read_one`, `Complexity.LogProg.read_cleanup`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.rrun_zero`, `Complexity.LogProg.readFrame_at`.
