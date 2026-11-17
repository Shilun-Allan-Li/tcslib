<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStepReadData_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Update of Read Data

**Claim.** The read-data record at threshold $i+1$ is obtained from the record at threshold $i$ by updating its symbol and edge entries at tape $i$ to the corresponding scanned symbol and edge tests.

**Proof.** Compare the fields of the two records. Their state, input-position flags, and all other unchanged data agree by definition. For each tape index $j$, if $j=i$, the update assigns the scanned symbol and the tests that the head is at $-s$ or $s$; these are exactly the entries selected by the threshold $i+1$. If $j\ne i$, then $j.val\ne i.val$, so $j.val<i.val+1$ is equivalent to $j.val<i.val$. Thus the old entries already have the values required at threshold $i+1$, and the update leaves them unchanged.
