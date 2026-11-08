<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPrepare_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the prepared configuration

**Claim.** From phase $1$ with work-head displacement $j-1$, after $j+1$ steps the preparation machine reaches phase $2$ with all work heads at zero and unchanged tapes and input-head position.

**Proof.** Induct on $j$, under the bound $j\le |s|$. For $j=0$, the initial displacement is $-1$, so the first work head scans the blank cell to the left of $s$. The phase-$1$ transition moves it right without changing any tape or the input head, enters phase $2$, and leaves all work heads at zero. For the successor case, the starting displacement $(j+1)-1$ equals $j$. Since $j<|s|$, the first work head scans a symbol of $s$; the phase-$1$ transition moves it left, preserving the configuration otherwise, and reaches the inductive starting configuration with displacement $j-1$. The run decomposition into one step followed by $j+1$ steps now applies the induction hypothesis. The identities for runs of zero and successor length (`runFrom_zero`, `runFrom_succ_eq_step`) express these decompositions; the tape reads are given by `bufferTape_nat`, while the base-case blank read is `bufferTape_left`. The stationary input head follows from `moveInputPos_zero`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
