<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderBitsTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Canonical Header Test

**Claim.** For every machine format $F$, a finite Boolean-alphabet machine halts after exactly a constant multiple of $|\alpha|+1$ steps and outputs the one-bit canonical-header test.

**Proof.** Use the canonical-header seam machine to place the canonical header on tape zero, with all other tapes blank, in at most $a(|\alpha|+1)$ steps. Then run the verdict machine on that tape. Its run takes $2|w|+3$ steps and halts with output equal to the one-bit test of the last header bit, with the default value used when the header is empty. The header-seam result supplies the required first-exit condition, so the seam-composition theorem joins the two runs. Since the canonical header has length at most $|\alpha|$, the combined time is at most $a(|\alpha|+1)+2|\alpha|+4$, which is bounded by $(a+4)(|\alpha|+1)$. The computation-time monotonicity theorem raises the run to that uniform bound.

**Key facts.** `Turing.MachineFormat.exists_canonHeaderSeam`, `Turing.MachineFormat.canonVerdictTM_run`, `Turing.seamCompTM_run_ofCfg`, `Turing.MachineFormat.canonHeader_length`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.bufferTape_nil`.
