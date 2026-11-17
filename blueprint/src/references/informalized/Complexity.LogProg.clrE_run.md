<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.clrE_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Erasure Run

**Claim.** Starting with the first $k$ symbols of a word in a register whose head is at $k-1$, the erasing state clears the register and returns its head to zero in $k+1$ steps, then enters the next state; before that time it remains in the erasing state with head between $-1$ and $k-1$.

**Proof.** Proceed by induction on $k$, under the condition $k\le |w|$. For $k=0$, the register is blank at position $-1$. One prescribed erasing transition moves the head to zero, leaves the register blank, and enters the next state. The only earlier time is time zero, where the claimed head bound holds.

For the successor case, the prefix of length $k+1$ is the prefix of length $k$ followed by its last symbol. The head initially scans that last symbol. The prescribed erasing transition removes it and moves the head one place left, producing exactly the configuration with the length-$k$ prefix and head at $k-1$. The register-read fact identifies the scanned symbol (`regCfg_read`), and the register-action formula describes this transition (`apply_regAct`); deleting the last symbol from the buffered tape gives the shorter prefix (`bufferTape_erase_last`). By induction, another $k+1$ steps erase that prefix and enter the next state, so the total is $k+2$ steps. For any earlier time, either it is time zero, where the head starts at $k$, or it is one step followed by an earlier time in the inductive run. The latter run remains in the erasing state with head between $-1$ and $k-1$; after shifting the time by one, the same bounds give the required interval $[-1,k]$. Run concatenation identifies both the terminal configuration and these intermediate configurations (`rrun_add`).

**Key facts.** `Complexity.LogProg.rrun_one_reg`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.bufferTape_erase_last`, `Complexity.LogProg.rrun_add`.
