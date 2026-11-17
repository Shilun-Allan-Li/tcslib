<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.snapSrcs_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Snapshot Sources

**Claim.** Every source in the snapshot-source list for $M$, $\ell$, and time $t$ is valid for input width $n$, configuration width $\mathrm{cfgWidth}(M)$, and block index $\mathrm{snapIdx}(M,|\ell|,T,t)$.

**Proof.** Split membership in the snapshot-source list into its constituent cases. The constant source is valid automatically. For the previous-snapshot block source, when $t=0$ the source is again constant. When $t\ne0$, its block index is below the current snapshot index: the previous snapshot lies before the next configuration stride, and the current snapshot index is at least the start of that stride. Its bit index is the snapshot width, which is below the configuration width, since that width is the snapshot width plus five. The input-symbol sources have block indices below the current snapshot index by the input-index bound; their bit indices $1$ and $2$ are below the configuration width. For each work tape, the two sources at the right edge of its cell window have indices below the corresponding input block, hence below the snapshot block; their bit indices $3$ and $4$ are again below the configuration width. Finally, the remaining previous-snapshot sources are valid at the current snapshot index by the validity theorem for that list, since the current snapshot index is at least the start of its time block.

**Key facts.** `Complexity.prevStep_lt`, `Complexity.snapIdx_lt_succ`, `Complexity.inpIdx_lt_snapIdx`, `Complexity.cellIdx_lt_inpIdx`, `Complexity.prevSnapSrcs_valid`.
