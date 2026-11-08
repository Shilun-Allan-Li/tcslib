<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.cmp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Comparison-Stage Semantics

**Claim.** Under the stated register bounds and successor-run hypothesis, the comparison-stage computation terminates with all registers bounded by $B$ and accepts exactly when $cp=n$ or when $cp\ne n$ and $Q$ holds.

**Proof.** Split according to whether $cp=n$. If they are equal, the comparison instruction follows its equality branch directly to the accepting return. The register bound for encoded states (`St.greg`) supplies the required bound at the comparison label and at the return; the semantics of equality branching (`NSem.jeq_pos`) and of returning true (`NSem.ret`) establish termination and acceptance. In this case the desired condition is true because $cp=n$.

If $cp\ne n$, the comparison takes the unequal branch (`NSem.jeq_neg`). That branch clears the input-length register and copies $cp$ into it by the program's copy loop. The copy-loop correctness result (`nsem_copy`) shows that this reaches the next round with $n=cp$, while preserving termination, the register bound, and the acceptance condition. The loop's increment is covered by `NSem.inc`, and its clear step by `NSem.clr`; the bounds needed along these steps again come from `St.greg`. The resulting register state is the original state with $n$ replaced by $cp$ and $s$ unchanged. The theorem's hypothesis provides the round computation after additionally replacing $s$ by $s+1$; the comparison program's setup includes the increment of $s$, represented by the final `NSem.inc` step. After identifying the updated state with the hypothesized one (`IG.of_eq`), that run terminates within the bound and accepts exactly when $Q$ holds. Therefore in the unequal case acceptance is equivalent to $Q$, as required.

**Key facts.** `Complexity.LogProg.ISGen.St.greg`, `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.NSem.ret`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.nsem_copy`, `Complexity.LogProg.NSem.clr`, `Complexity.LogProg.NSem.inc`, `Complexity.LogProg.ISGen.IG.of_eq`.

**Caveat.** The supplied proof source applies a clear and then a copy loop from $n$ into $cp$-derived state, but the exact register updates and the transition from the copied state to the state with $s$ increased are obscured by omitted helper definitions and automation. The account follows the visible route, but that state bookkeeping cannot be fully checked from the supplied statements.
