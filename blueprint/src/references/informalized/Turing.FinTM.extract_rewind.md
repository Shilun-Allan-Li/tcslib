<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extractor Buffer Rewind

**Claim.** Starting in rewind state with work-head displacement $j-1$, the extractor returns to replay state with work head at zero and empty output after exactly $j+1$ steps, for every $j\le |a|$.

**Proof.** Induct on $j$. When $j=0$, the head is at $-1$, where the buffer has no symbol (`bufferTape_left`). The rewind transition therefore moves right into replay state; it does not change the input head, buffer, or output. The run equations for zero and one step (`runFrom_zero` and `runFrom_succ_eq_step`) give the stated two-step run length. For the successor case, the head starts at displacement $(j+1)-1=j$. Because $j<|a|$, it reads the $j$th symbol of the buffer (`bufferTape_nat`). In rewind state, seeing a symbol moves the head one place left and keeps the machine in rewind state. Thus one step reaches exactly the configuration for the induction hypothesis, with head at $j-1$. Applying that hypothesis takes $j+1$ further steps and reaches replay state at zero. The one-step run equation (`runFrom_succ_eq_step`) combines these steps, and the bound $j+1\le |a|$ ensures the required symbol exists.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
