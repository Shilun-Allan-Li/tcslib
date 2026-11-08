<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairDup_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Duplication Computation

**Claim.** For every finite bit string $x$, the constructed machine computes the encoding of $(x,x)$ in exactly $4(|x|+1)$ steps.

**Proof.** Let $p$ be the list formed by doubling each bit of $x$. The pair-duplication invariant shows that after $2|x|$ steps the machine has emitted $p$ and reached the scanning configuration at the end of the input. One further step moves it into a configuration $c$ whose output is $p$ followed by the first separator bit. The scan configuration is read as the expected input symbol by `Turing.FinTM.f2_scanCfg_read`, and configurations with no work tapes are identified by comparing state, input position, and output (`Turing.Cfg.ext_zero_tapes`). From $c$, the rewind rule takes $|x|+1$ steps to return the head to position $1$, preserving the other components (`Turing.FinTM.rewind_scan`). One more step emits the second separator bit and enters the copy phase. Thus after $2|x|+1+(|x|+1)+1$ steps, the machine is poised to copy $x$, with output $p$ followed by $01$. The scan-copy finishing lemma says that the remaining $|x|+1$ steps append a copy of $x$ and halt (`Turing.FinTM.f2_scanCopy_finish`). The total is $4(|x|+1)$. The computation characterization then gives the required halting state and output (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Turing.FinTM.f2_pairDup_double`, `Turing.FinTM.f2_scanCfg_read`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.rewind_scan`, `Turing.FinTM.f2_scanCopy_finish`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_neg_of_ne_left`, `Turing.FinTM.computesInTime_iff`.
