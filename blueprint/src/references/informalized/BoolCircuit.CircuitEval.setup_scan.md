<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.setup_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a Doubled Bit String

**Claim.** When the input segment is the doubled form of a word $w$, the machine's run of $2|w|$ steps implements the scan fold over $w$, with the prescribed resulting phase and mark count, input-head position advanced by $2|w|$, and the other configuration data unchanged.

**Proof.** Proceed by induction on $w$. For the empty word, the run has length zero, and the fold also leaves the phase and count unchanged. For a word beginning with a bit $b$, the input begins with the pair $b,b$, followed by the doubled remainder. The two-step scan fact (`BoolCircuit.CircuitEval.lstep`) shows that reading this pair produces exactly one scan update, from $(\phi,r)$ to $\operatorname{scanF}((\phi,r),b)$, and advances the input head by two. If the phase is $\mathrm{n0}$ and $b$ is true, the machine also adds a mark at the current mark-tape position; the tape-update fact for a replicated run of true bits (`BoolCircuit.CircuitEval.wr_replicate`) identifies the resulting tape with the buffer tape for one additional mark. In the other phase/bit cases, the scan update leaves the mark tape unchanged. The phase remains either $\mathrm{n0}$ or $\mathrm{sep}$, so the induction hypothesis applies to the doubled remainder. Split the total run into the first two steps and the remainder using the run-addition law (`Turing.MultiTapeTM.runFrom_add`), and identify configurations whose natural-number head positions agree using `cfS_congr`. The zero-run law (`Turing.MultiTapeTM.runFrom_zero`) supplies the empty-word case.

**Key facts.** `BoolCircuit.CircuitEval.lstep`, `BoolCircuit.CircuitEval.wr_replicate`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_zero`, `BoolCircuit.CircuitEval.cfS_congr`.
