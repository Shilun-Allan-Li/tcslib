<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRestore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Restoration with a Side Condition

**Claim.** If $p$ lies on the side specified by $side$, then some side value $side'$ with the same property makes the dispatch machine reach the local answer configuration after $|p|+3$ steps from the ready configuration containing the verdict.

**Proof.** If $p=0$, take $side'=\mathrm{true}$; zero satisfies its side condition, and the zero-position restoration result gives the required run (`Turing.oracleRestore_zero`). Now suppose $p\ne0$. The side condition identifies the signed distance: $p$ equals the chosen direction, $1$ or $-1$, times $|p|$ (`Turing.oracleSide_distance`). Hence after $|p|-1$ backward moves from that direction, the head is at $p$; this is the endpoint calculation used to specialize the backward-run formula (`Turing.oracleBack_run`). The first three restoration steps establish the starting backward configuration (`Turing.oracleRestore_three`), and splitting the remaining run into those three steps, the backward segment, and one final transition is justified by the run concatenation and successor identities (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`). The last transition erases the temporary marker and enters the local answer state (`Turing.oracleErase_step`). Take $side'=side$, which retains the assumed side condition.

**Key facts.** `Turing.oracleRestore_zero`, `Turing.oracleSide_distance`, `Turing.oracleBack_run`, `Turing.oracleRestore_three`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.oracleErase_step`.
