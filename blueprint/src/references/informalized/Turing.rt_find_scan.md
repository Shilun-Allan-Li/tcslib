<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Way Scan of a Word

**Claim.** The scanning machine processes a word $w$ from forward state $a$, completes after $2|w|+2$ steps with state given by folding the transition function over $w$, and leaves all other configuration data unchanged. It does not reach a completed state earlier, and its tape heads stay within the asserted bounds throughout.

**Proof.** The general configuration theorem for the two-way scanning machine (`scanTM_run_ofCfg`) gives the endpoint, the absence of a completed state at every earlier time, and the head-position bounds. Its endpoint accumulator is expressed using the scan result. The fold characterization of that result (`scanResult_fold`) identifies the accumulator as the left fold of the transition function over $w$ from $a$. Although the scan theorem also describes the tape contents after the return pass, the endpoint here agrees with the original tape: for any cell in the overwritten interval, the hypothesis says its original value is exactly the corresponding buffer symbol, and outside that interval the scan theorem leaves it unchanged. Thus the endpoint differs only in the control state, as claimed.

**Key facts.** `Turing.scanTM_run_ofCfg`, `Turing.scanResult_fold`.
