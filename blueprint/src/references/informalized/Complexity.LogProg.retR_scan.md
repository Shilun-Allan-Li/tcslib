<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.retR_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completing a Register Scan

**Claim.** If the selected register head begins at position $n-1$ and $n\le |w|$, then the scanning return phase finishes after $n+1$ steps: the selected head is at zero, the machine is at the successor for argument position $a+1$, and the other register and decider heads are unchanged. The stated bounds hold at every intermediate time.

**Proof.** Induct on $n$. If $n=0$, the selected head is at $-1$, so its buffer-tape read is blank. In the scanning phase, a blank read moves the head right and advances to the successor. Thus one step gives the claimed endpoint. At time zero the heads are at their initial positions; after the step the selected head is at zero, which satisfies the required lower and upper bounds, while all other heads and the decider heads are unchanged.

For the successor case, the selected head is at position $n$, and since $n<|w|$ its read is the symbol $w[n]$. The scanning transition moves it left by one and remains in the scanning phase. The resulting head position is $n-1$, so the induction hypothesis applies to the updated head-position map with parameter $n$. Decompose each positive-time run into this first step followed by the shorter run, using `Turing.MultiTapeTM.runFrom_succ_eq_step`. The induction bounds transfer to the remaining times: for the selected register the initial position has shifted left by one, and the one-step update restores the stated interval relative to the original position. Other register heads remain fixed. Composing the first transition with the induction endpoint gives the required successor state and selected head position zero.

**Key facts.** `Complexity.LogProg.apply_regMove`, `Complexity.LogProg.mkCfg_state`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
