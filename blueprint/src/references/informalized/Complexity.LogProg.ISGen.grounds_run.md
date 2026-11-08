<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.grounds_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round exponent accumulation

**Claim.** For either phase, after the generator's round state with index $j$ and register state $\sigma$, the asserted semantic property follows whenever the bound conditions hold and every possible value of the loop counter at the zero-index round state has that property with exponent increased by $2j$ times the phase's selected register.

**Proof.** Induct on $j$. At $j=0$, the round state is already the zero-index round state, and the premise supplies the required semantic property for the current counter value; equality of the register states transfers it to the goal (`IG.of_eq`). For the successor case, split according to the phase. The generator clears its loop counter, then runs an add-twice loop whose comparison register is respectively $lg$ or $s$. Each loop iteration increments the exponent register twice and the counter once. The add-twice loop principle therefore accounts for exactly $2(y-k)$ added to the exponent when the selected comparison register has value $y$ and the counter starts at $k$ (`Complexity.LogProg.nsem_addTwice`). With the counter cleared, this adds $2y$; the arithmetic identity $2(j+1)y=2y+2jy$ leaves the exponent in the form required by the induction hypothesis for index $j$. The hypothesis applies to every bounded counter value, and state equality identifies the resulting registers with its required input (`IG.of_eq`). The clear-step principle and the register-bound invariant justify the initial clearing and the intermediate loop configurations (`Complexity.LogProg.NSem.clr`, `Complexity.LogProg.ISGen.St.greg`).

**Key facts.** `Complexity.LogProg.ISGen.IG.of_eq`, `Complexity.LogProg.nsem_addTwice`, `Complexity.LogProg.NSem.clr`.
