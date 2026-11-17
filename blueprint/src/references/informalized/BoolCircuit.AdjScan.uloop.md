<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.uloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Scan Loop

**Claim.** If the suffix of $E$ beginning at $p$ consists of exactly $k$ true bits followed by a false bit, then, for either flag $ex$, the scan machine moves from state $uA(ex)$ with registers $(p,c,0)$ to state $uE(ex)$ with registers $(p+k,c,k)$, keeping every register at most $B$.

**Proof.** First, the displayed suffix has length at least $k+1$, so $p+k+1\le |E|\le B$. We prove by induction on the number $d$ of true bits still to scan that, whenever $j+d=k$, the machine can go from $uA(ex)$ with registers $(p+j,c,j)$ to the stated endpoint. If $d=0$, then $j=k$: the read at position $p+k$ sees the false bit immediately after the run, so the machine moves directly to $uE(ex)$. The endpoint registers are already $(p+k,c,k)$. For the induction step, the read at position $p+j$ sees true because $j<k$. The machine therefore moves through $uB(ex)$, increments the third register, and then through $uC(ex)$, increments the first register. It is now at $uA(ex)$ with registers $(p+j+1,c,j+1)$, to which the induction hypothesis applies with one fewer bit remaining. The bit-read rule is justified by the suffix description (`bit_rep`), and each read transition uses the assumed oracle behavior (`astep_rd`). Throughout the run, the first register is at most $p+k\le B$, the third is at most $k\le B$, and the unchanged second register is at most $B$; these bounds supply the required intermediate register condition (`gd_rg`).

**Key facts.** `BoolCircuit.AdjScan.le_of_drop`, `BoolCircuit.AdjScan.bit_rep`, `BoolCircuit.AdjScan.astep_rd`, `BoolCircuit.AdjScan.gd_rg`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.step`.
