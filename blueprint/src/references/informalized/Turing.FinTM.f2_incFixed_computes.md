<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_incFixed_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time of Fixed-Width Increment

**Claim.** The fixed-width increment machine computes the fixed-width increment of every Boolean word, using the empty word when increment is undefined, within $3(|x|+1)$ steps.

**Proof.** First use the case analysis for fixed-width increment (`Turing.FinTM.f2_incFixed_cases`). If every bit is true, the scan of the word reaches the end and halts with empty output in $|x|+1$ steps; the increment is undefined, so this is the required output. Otherwise write $x=1^j0\,rest$. The machine scans the initial $j$ true bits without output. On reading the first false bit, it moves into the rewind phase; rewinding takes $j+1$ steps and returns to the start of the input. It then scans the same $j$ true bits, outputting one false for each, and changes the first false to true. The suffix-copying phase appends $rest$. The scan and copy behaviors are supplied by `Turing.FinTM.f2_scanTrues_run` and `Turing.FinTM.f2_scanCopy_suffix`; `Turing.FinTM.rewind_scan` gives the return to the start. Combining these phases, the total number of steps is bounded by the displayed time allowance: using $|x|=j+1+|rest|$, the stated bound exceeds the phase total. This run halts with output $0^j1\,rest$, which is exactly the increment characterized by the case analysis.

**Key facts.** `Turing.FinTM.f2_incFixed_cases`, `Turing.FinTM.f2_scanTrues_run`, `Turing.FinTM.rewind_scan`, `Turing.FinTM.f2_scanCopy_suffix`, `Turing.FinTM.f2_scanCfg_read`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
