<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_of_forall_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Count Below a Threshold

**Claim.** If $kf(i)<K$ for every $i<N$, then all $N$ indices below $N$ are counted, so the count is exactly $N$.

**Proof.** The hypothesis says that every index in the initial segment below $N$ satisfies the predicate $kf(i)<K$. The characterization of a count equal to the full segment length when the predicate holds everywhere (`Nat.count_iff_forall`) therefore gives $\operatorname{cntLt}(kf,K,N)=N$.
