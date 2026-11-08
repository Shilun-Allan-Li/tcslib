<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitRestore_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration Rewind

**Claim.** For every natural number $k$, Boolean words $w,s$, input-head position $p$, and natural number $j\le |s|$, running the split-restoration machine for $j+1$ steps from the clean configuration in state $(1,\mathrm{false})$ with first work-tape head at $j-1$ yields the clean configuration in state $(2,\mathrm{false})$, with input-head position $p$, unchanged tape contents, all other work tapes blank, all heads at zero, and empty output.

**Proof.** Induct on $j$. At $j=0$, the first work-tape head is at $-1$ and reads blank (`bufferTape_left`). The state-$1$ transition on a blank cell moves the heads right and enters state $2$, leaving the input head fixed; `moveInputPos_zero` verifies the latter. The run identities (`runFrom_zero`, `runFrom_succ_eq_step`) reduce the claim to this single step. For the successor case, the starting head position $(j+1)-1$ equals $j$. As $j<|s|$, the first work tape has a symbol at cell $j$ (`bufferTape_nat`), so the state-$1$ transition moves the heads one cell left and remains in state $1$. This produces the induction configuration with head position $j-1$, while preserving the input-head position and tape contents. The successor run identity reduces the run to that step followed by the induction hypothesis, proving the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
