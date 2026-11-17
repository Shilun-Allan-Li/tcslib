<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_writeReleased_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Released writing run

**Claim.** Starting in the release entry state, the released writing machine writes $w$ on tape $i$, advances that tape's head by $|w|$, and reaches state $0$ after exactly $|w|+1$ steps. It does not reach that exit state earlier, and all work-tape heads remain within distance $|w|$ of their initial positions throughout the run.

**Proof.** Change the state labels of the initial configuration so that its entry state becomes the initial state of the writing machine. The writing-run result (`Turing.writeAdvTM_run_ofCfg`) gives the configuration after $|w|+1$ steps: tape $i$ has $w$ on the interval beginning at its initial head position, its head has advanced by $|w|$, and the machine is back in state $0$. It also shows that state $0$ was not reached at any positive earlier time.

The released machine follows this writing computation until its first return to the anchor state, then marks that return by entering the released exit state. The first-return result for a released machine (`Turing.seamReleaseTM_firstReturn`) transfers the endpoint and the absence of any earlier visit to that exit state. To bound head positions, consider any head position visited through time $u\le |w|+1$. The visited-head identity for release (`Turing.seamReleaseTM_visitedByTapeHead`) identifies it with a position visited during the underlying writing run. The writing-run head bound puts it between the initial position and that position plus $|w|$ on tape $i$, and fixes every other tape's head at its initial position. Thus every head is within distance $|w|$ of its initial position.

**Key facts.** `Turing.writeAdvTM_run_ofCfg`, `Turing.seamReleaseTM_firstReturn`, `Turing.seamReleaseTM_visitedByTapeHead`.
