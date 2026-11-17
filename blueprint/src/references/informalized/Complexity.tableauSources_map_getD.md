<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.tableauSources_map_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of the Tableau Sources

**Claim.** Under the stated hypotheses on the input, constants, and earlier tableau blocks, reading the values at the source indices for time $t$ produces exactly the ideal source list for that time.

**Proof.** First use the hypotheses at indices $n$ and $n+1$ to see that every constant source reads its prescribed Boolean value. Set $p$ to be the input-head position at time $t$. If $p$ lies within the input, the source for position $p-1$ reads $x_{p-1}$ by the input-value hypothesis, while the corresponding input bit is present. If it does not, the input bit is absent and the source is the false-constant index. Thus both the presence flag and symbol source agree with the ideal input sources. For the preceding configuration, split on $t=0$: the replicated false constants give the zero-time source list; otherwise the block at time $t-1$ has the encoding specified by the block hypothesis. For each work tape, split on whether a previous visit exists. With no visit, the replicated false constants give the ideal blank information. With a previous visit at time $s$, the source list consists of a true flag followed by the block for $s$, whose values give the required encoding; the strict inequality $s<t$ needed to use the block hypothesis is supplied by `prevVisit_lt`. The final source is false at time zero and otherwise reads the preceding acceptance vertex, again by the block hypothesis. Combining these componentwise identifications in list order yields the ideal source list.

**Key facts.** `Complexity.prevVisit_lt`.
