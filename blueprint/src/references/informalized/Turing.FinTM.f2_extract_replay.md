<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay Phase Configuration

**Claim.** For each $j\le |a|$, after $j$ replay steps from the stated configuration, the extractor remains in the replay state at the same input position, its work head is at $j$, and its output is the first $j$ symbols of $a$ if $first$ is true and empty otherwise.

**Proof.** Induct on $j$. At $j=0$, no step has occurred, the head is at the origin, and the output is empty, which agrees with either value of the flag. For the successor step, the induction hypothesis places the work head at $j$. Since $j<|a|$, the tape symbol there is $a_j$ ($\texttt{Turing.FinTM.bufferTape_nat}$). In replay state $1$, the transition leaves the input head fixed, advances the work head by one, and emits that bit exactly when $first$ is true. The input position is unchanged by the zero-move formula ($\texttt{Turing.moveInputPos_zero}$). When the flag is true, appending $a_j$ to the first $j$ symbols gives the first $j+1$ symbols; when false, output remains empty. The one-step run equation ($\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}$) identifies this transition with the run of length $j+1$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
