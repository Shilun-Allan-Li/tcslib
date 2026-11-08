<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.fscan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Characterisation of the Final Scan

**Claim.** Under the stated register, memory-region, and counter hypotheses, the machine's final scan halts with the Boolean answer indicating whether some code $v$ in the range $U\le v<K$ is marked and is accepted by the oracle at index $3$ for the specified paired encoding.

**Proof.** Proceed by strong induction on $j=K-U$, proving the scan result for every machine state and memory marking satisfying the hypotheses. If $U=K$, the search range is empty, so the existential condition is false. The final-scan instruction therefore takes its rejecting branch and halts; the state bounds and head-position bounds give the guard at the starting and halting steps (`stepH_of`, `g_of`), and `MHalt.ret` records the rejection.

Now suppose $U<K$. Split the existential into the possibility that the current code $U$ is marked and accepted, or that a witness occurs at some $v\ge U+1$. For the latter range, apply the induction hypothesis to the state with $U$ increased by one. The new difference is $K-(U+1)<j$, and the updated state retains the register bounds, while the other hypotheses are unchanged. This gives a guarded halting run from the next scan state with answer exactly the existential over codes at least $U+1$.

The current scan step uses the memory-access routine at index $U$. Its safety bounds follow from the state and region assumptions. The routine reads the mark at $B_s+U$ and returns to the final-scan continuation, preserving the memory marking and restoring the head to zero (`ac_run`). If that mark is false, the current code cannot witness the existential, so the run continues with the next-code scan. If it is true, the machine queries oracle index $3$ on the paired encoding of $x$, the bits of $U$, and the bits of $s$. An affirmative answer makes $U$ a witness and the machine halts affirmatively; otherwise it continues with the induction-hypothesis run. The two cases establish the desired answer equivalence. The query's input has the stated paired form by the encoding identity `vword_whole₂`, and the configurations used in the run satisfy the guard by `g_of` and `stepH_of`.

**Key facts.** `Complexity.LogProg.ExpBFS.St.toV_U`, `Complexity.LogProg.ExpBFS.stepH_of`, `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MHalt.ret`, `Complexity.LogProg.MReach.halt`, `Complexity.LogProg.ExpBFS.ac_run`, `Complexity.LogProg.vword_whole₂`.
