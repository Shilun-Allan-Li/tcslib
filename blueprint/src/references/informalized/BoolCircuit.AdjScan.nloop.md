<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.nloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Initial scan-loop behavior

**Claim.** Under the stated hypotheses, for every $j\le n$ with $j\le tv$, the scan machine halts from label $nA$ with registers $(j,j,0)$, respecting the register bound, and returns the default answer when $tv<n$ and otherwise returns $ans$.

**Proof.** First, the initial encoding hypothesis says that the edge string begins with $n$ true bits followed by false. The bound on its length follows from the fact that a specified nonempty prefix of a list cannot be longer than the list itself (`le_of_drop`). The bit-reading consequence (`bit_rep`) says that, at position $j$ in this initial run, the oracle read is true exactly when $j<n$.

We prove a stronger assertion: whenever $j+d=n$ and $j\le tv$, the machine halts with the claimed answer from label $nA$ and registers $(j,j,0)$. Induct on $d$. If $d=0$, then $j=n$. The read at position $j$ is false, so the machine advances to the gate scan at register values $(n+1,n,0)$. The assumption $j\le tv$ gives $n\le tv$, allowing the hypothesized continuation from label $gA$ to supply the halt and answer. The two steps preserve the register bound.

For the successor case, $j<n$, so the read at position $j$ is true and the machine proceeds to compare the current vertex index $j$ with $tv$. If $j=tv$, it returns the task’s default answer, which is the required answer since $tv<n$. Otherwise, it increments the current index and the scan position, reaching label $nA$ with registers $(j+1,j+1,0)$. The induction hypothesis applies because $(j+1)+(d)=n$ and $j+1\le tv$. Each intermediate configuration respects the bound: the registers are at most $n+1$, and the initial string’s length bound together with the stated encoding bound supplies the needed register limits. Finally, for any $j\le n$, take $d=n-j$ to obtain the assertion.

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.bit_rep`, `BoolCircuit.AdjScan.gd_rg`, `BoolCircuit.AdjScan.AHalt.step`, `BoolCircuit.AdjScan.astep_rd`, `BoolCircuit.AdjScan.astep_hit`, `BoolCircuit.AdjScan.AHalt.ret`.

**Caveat.** The proof source uses register-bound facts at intermediate steps and the continuation hypothesis, but the supplied upstream list does not include the complete supporting details for how all stated register bounds follow.
