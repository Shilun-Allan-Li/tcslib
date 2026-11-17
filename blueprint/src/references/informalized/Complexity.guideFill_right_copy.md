<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.guideFill_right_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward filling extends the copied guide

**Claim.** If $n+1\le R$, filling $R$ cells rightward from the copied guide with $n+1$ cells gives the copied guide with $R$ cells.

**Proof.** Compare the tapes at an arbitrary integer coordinate $z$. The rightward fill assigns a guide mark when $0\le z<R$; otherwise it retains the copied guide with $n+1$ cells. On the filled interval, the mark agrees with the copied guide with $R$ cells: both mark $0$ as the origin and the other coordinates as inside. Outside it, the retained copied guide also agrees with the larger copied guide: the exceptional coordinate $-1$ remains inside, and any nonnegative coordinate in the smaller copied interval is still in the larger one because $n+1\le R$. All other coordinates carry no mark in either definition. Hence the tapes agree pointwise.
