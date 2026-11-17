<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.ac_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Access Simulation

**Claim.** Starting at a memory-access routine for a site, the machine reaches the site’s prescribed exit with the bit equal to the site’s marking flag or the memory bit at the addressed cell. The counters and head return to their initial values, and memory changes only by setting the addressed cell when the site is a marking site; all intermediate configurations satisfy the stated bounds and guards.

**Proof.** Let $u$ be the counter selected by the site. First copy the memory-region base into the outward-walk counter, then copy $u$ into that counter as well. The copy-loop result (\texttt{cp_run}) shows that these routines preserve the other registers, leave the scratch register cleared, and place the intended sum in the outward-walk counter. Since the site index is either the $U$ or $V$ register (\texttt{idx_cases}), this copied value is exactly $u$, while the initial zero value of the outward counter ensures the first copy starts correctly. The hypotheses give the register bounds needed for both copy routines and ensure their intermediate configurations remain guarded.

Next the outward walk moves the head right by the base-plus-index distance. Its result (\texttt{wo_run}) returns the outward counter to zero, records the distance in the return counter, and places the head at the addressed cell. The bounds on the initial registers and the assumptions that both walk counters and the scratch register start at zero verify the walk’s hypotheses; the address bounds ensure that the head remains between $0$ and $P$.

At the cell, split on whether the site marks memory. For a marking site, the machine sets the bit to true. For a reading site, it reads the existing bit and selects the corresponding return walk. In either case, the return-walk result (\texttt{wb_run}) moves left by the recorded distance, clears the return counter, and reaches the exit associated with the resulting bit. The head therefore returns to zero. In the marking case the memory is updated only at the addressed cell; in the reading case it is unchanged. Composing these reachability segments with \texttt{MReach.trans} gives the claimed run. The configuration-identification fact \texttt{toV_T} and the bookkeeping facts \texttt{reach_cf} and \texttt{idx_cases} ensure the intermediate register descriptions match the stated machine state.

**Key facts.** `Complexity.LogProg.ExpBFS.cp_run`, `Complexity.LogProg.ExpBFS.idx_cases`, `Complexity.LogProg.ExpBFS.wo_run`, `Complexity.LogProg.ExpBFS.mset_of`, `Complexity.LogProg.ExpBFS.wb_run`, `Complexity.LogProg.ExpBFS.mread_of`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.MReach.trans`.
