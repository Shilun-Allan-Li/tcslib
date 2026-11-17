<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderCountSeam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Header Count Seam

**Claim.** There is a finite Boolean-alphabet machine that reaches a designated exit with the canonical header on tape zero, its fixed-width increment on tape 1, and all other tapes empty, with a linear time bound and no earlier visit to the exit.

**Proof.** First load the canonical header onto tape zero using the header-seam machine. Embed that machine into a larger tape bank, so its run and the blank contents of unused tapes are preserved. Then use the preserving-install construction for the canonical count: it computes the count from the header while retaining the argument word and installs the result on a destination tape whose index is 1. The count specification says its word has length $|header|+1$, so the install-stage running-time bound simplifies to a constant times $|header|+1$, and hence to a constant times $|\alpha|+1$. Seam composition joins the stages. Its first-return theorem, using the first-exit conditions of both stages, proves that the combined machine does not reach its final exit earlier. The embedding identity identifies the final tape contents with the required header, count, and empty words elsewhere.

**Key facts.** `Turing.MachineFormat.exists_canonHeaderSeam`, `Turing.MachineFormat.exists_canonCountTM`, `Turing.MachineFormat.canonPreserveInstall`, `Turing.MachineFormat.canonCount_spec`, `Turing.MachineFormat.canonHeader_length`, `Turing.MachineFormat.canonEmbedWords`, `Turing.embedEmitTM_runFrom`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`.
