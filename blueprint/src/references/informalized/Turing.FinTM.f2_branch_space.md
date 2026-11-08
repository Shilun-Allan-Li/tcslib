<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_branch_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used by the Branch Machine

**Claim.** The branch machine's space through time $t$ equals the active machine's space through time $t$ plus the number of tapes belonging to the inactive machine: for true branch choice it is $M_1$'s space plus $M_2.k$, and for false choice it is $M_2$'s space plus $M_1.k$.

**Proof.** Split on the branch bit. If it is false, the branch machine starts in the right component, with $M_2$'s initial configuration on the right-hand tapes and the $M_1.k$ left-hand tapes blank at head position zero. The right-configuration run identity (`rightCfg_run`) shows that at every time the active right block follows exactly the run of $M_2$, while the left block's heads remain at zero. Each of those $M_1.k$ tapes therefore visits just the singleton position set, contributing one cell apiece. Split the sum over all tapes into its left and right blocks (`f2_sum_add`); the result is $M_2$'s space plus $M_1.k$. If the bit is true, the analogous initial-configuration equality places $M_1$ on the left and leaves the $M_2.k$ right-hand tapes at zero. The left-configuration run identity (`leftCfg_run`) preserves $M_1$'s run and keeps the added heads fixed. Splitting the tape sum again gives $M_1$'s space plus $M_2.k$. The singleton contribution follows because the visited set for a fixed head that remains at zero is the image of the nonempty time range under a constant map.

**Key facts.** `Turing.FinTM.f2_sum_add`, `Turing.FinTM.rightCfg_run`, `Turing.FinTM.leftCfg_run`.
